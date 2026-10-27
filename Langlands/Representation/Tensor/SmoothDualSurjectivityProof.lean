import Langlands.Representation.Tensor.SmoothDualSurjectivityStatement
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof

/-!
# Proof of surjectivity of the finite smooth-dual tensor map

A smooth functional on the finite external tensor product is fixed by a product
of compact open subgroups. Its restriction to the tensor product of the
finite-dimensional factor fixed spaces decomposes by finite-dimensional tensor
duality, the factor functionals lift to fixed smooth functionals, and injectivity
of compact-open fixed restriction for the external tensor identifies the image.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uI uG uV

section Surjectivity

variable {ι : Type uI} [Finite ι]
variable {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Factorwise compact-open cofinality places a product of compact open
subgroups inside any open subgroup of the finite product group. -/
theorem exists_isCompact_pi_le
    (hcof : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K)
    (U : OpenSubgroup (∀ i, G i)) :
    ∃ L : ∀ i, OpenSubgroup (G i), (∀ i, IsCompact (L i : Set (G i))) ∧
      Subgroup.pi Set.univ (fun i => (L i).toSubgroup) ≤ U.toSubgroup := by
  classical
  choose L hLc hLK using fun i =>
    hcof i (U.comap (MonoidHom.mulSingle G i) (continuous_mulSingle i))
  exact ⟨L, hLc, fun g hg =>
    Subgroup.pi_mem_of_mulSingle_mem g (fun i => hLK i (hg i (Set.mem_univ i)))⟩

variable [∀ i, IsTopologicalGroup (G i)]

/-- For admissible factors with compact-open cofinality, every smooth functional
on the finite external tensor product is the image of a tensor of smooth factor
functionals under the canonical map. -/
theorem smoothDualTensorMap_surjective (ρ : ∀ i, Representation ℂ (G i) (V i))
    (hρ : ∀ i, IsAdmissible (ρ i))
    (hcof : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K) :
    Function.Surjective (smoothDualTensorMap ρ) := by
  classical
  let := Fintype.ofFinite ι
  intro ℓ
  -- An open subgroup fixes `ℓ`; a compact open product subgroup lies inside it.
  obtain ⟨U, hU⟩ := ℓ.property
  obtain ⟨L, hLc, hLU⟩ := exists_isCompact_pi_le hcof U
  let P : OpenSubgroup (∀ i, G i) :=
    { toSubgroup := Subgroup.pi Set.univ (fun i => (L i).toSubgroup)
      isOpen' := by
        change IsOpen ((Subgroup.pi Set.univ (fun i => (L i).toSubgroup) :
          Subgroup (∀ i, G i)) : Set (∀ i, G i))
        rw [Subgroup.coe_pi]
        exact isOpen_set_pi Set.finite_univ (fun i _ => (L i).isOpen) }
  have hPc : IsCompact (P : Set (∀ i, G i)) := by
    change IsCompact ((Subgroup.pi Set.univ (fun i => (L i).toSubgroup) :
      Subgroup (∀ i, G i)) : Set (∀ i, G i))
    rw [Subgroup.coe_pi]
    exact isCompact_univ_pi hLc
  have hℓfix : ℓ ∈ fixedVectors (smoothContragredient (external ρ)) P.toSubgroup :=
    fun k => Subtype.ext (hU ⟨k, hLU k.property⟩)
  -- The factor fixed spaces are finite-dimensional.
  let F : ∀ i, Submodule ℂ (V i) := fun i => fixedVectors (ρ i) (L i).toSubgroup
  have : ∀ i, Module.Finite ℂ (F i) := fun i => (hρ i).2 (L i)
  -- Lifts of functionals on the factor fixed spaces to fixed smooth functionals.
  let e : ∀ i, fixedVectors (V := SmoothDual (ρ i)) (smoothContragredient (ρ i))
      (L i).toSubgroup ≃ₗ[ℂ] Module.Dual ℂ (F i) := fun i =>
    LinearEquiv.ofBijective (smoothDualFixedRestriction (ρ i) (L i).toSubgroup)
      (smoothDualFixedRestriction_bijective (ρ i) (hρ i).1 (L i) (hLc i))
  let lift : ∀ i, Module.Dual ℂ (F i) →ₗ[ℂ] SmoothDual (ρ i) := fun i =>
    (fixedVectors (V := SmoothDual (ρ i)) (smoothContragredient (ρ i))
      (L i).toSubgroup).subtype ∘ₗ (e i).symm.toLinearMap
  have hlift (i : ι) (f : Module.Dual ℂ (F i)) (u : F i) :
      smoothDualPairing (ρ i) (lift i f) u.val = f u := by
    change e i ((e i).symm f) u = f u
    rw [LinearEquiv.apply_symm_apply]
  have hlift_fixed (i : ι) (f : Module.Dual ℂ (F i)) (k : G i) (hk : k ∈ L i) :
      smoothContragredient (ρ i) k (lift i f) = lift i f :=
    ((e i).symm f).property ⟨k, hk⟩
  -- Decompose the restriction of `ℓ` by finite-dimensional tensor duality.
  let incl : (⨂[ℂ] i, F i) →ₗ[ℂ] ⨂[ℂ] i, V i :=
    PiTensorProduct.map (fun i => (F i).subtype)
  let y : ⨂[ℂ] i, Module.Dual ℂ (F i) :=
    (PiTensorProduct.dualDistribEquiv (R := ℂ) (M := fun i => F i)).symm
      (ℓ.val ∘ₗ incl)
  have hy : PiTensorProduct.dualDistrib y = ℓ.val ∘ₗ incl :=
    (PiTensorProduct.dualDistribEquiv (R := ℂ) (M := fun i => F i)).apply_symm_apply _
  have key : ∀ (z : ⨂[ℂ] i, Module.Dual ℂ (F i)) (w : ⨂[ℂ] i, F i),
      PiTensorProduct.dualDistrib
        (PiTensorProduct.map (fun i => smoothDualPairing (ρ i))
          (PiTensorProduct.map lift z)) (incl w) =
        PiTensorProduct.dualDistrib z w := by
    intro z w
    induction z using PiTensorProduct.induction_on with
    | smul_tprod a f =>
      induction w using PiTensorProduct.induction_on with
      | smul_tprod b u =>
        simp only [incl, map_smul, LinearMap.smul_apply, PiTensorProduct.map_tprod,
          PiTensorProduct.dualDistrib_apply, Submodule.subtype_apply, hlift]
      | add w w' hw hw' => simp only [map_add, hw, hw']
    | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
  refine ⟨PiTensorProduct.map lift y, ?_⟩
  -- The constructed functional is fixed by the compact open product subgroup.
  have hxfix : smoothDualTensorMap ρ (PiTensorProduct.map lift y) ∈
      fixedVectors (smoothContragredient (external ρ)) P.toSubgroup := by
    intro k
    change smoothContragredient (external ρ) (k : ∀ i, G i)
      (smoothDualTensorMap ρ (PiTensorProduct.map lift y)) =
        smoothDualTensorMap ρ (PiTensorProduct.map lift y)
    rw [← smoothDualTensorMap_action]
    congr 1
    change PiTensorProduct.map (fun i => smoothContragredient (ρ i) ((k : ∀ i, G i) i))
      (PiTensorProduct.map lift y) = PiTensorProduct.map lift y
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    congr 2
    funext i
    apply LinearMap.ext
    intro f
    exact hlift_fixed i f _ (k.property i (Set.mem_univ i))
  -- Both fixed functionals have the same restriction to the fixed vectors.
  have hinj := (smoothDualFixedRestriction_bijective (external ρ)
    (isSmooth_external ρ (fun i => (hρ i).1)) P hPc).1
  have hres : smoothDualFixedRestriction (external ρ) P.toSubgroup
        ⟨smoothDualTensorMap ρ (PiTensorProduct.map lift y), hxfix⟩ =
      smoothDualFixedRestriction (external ρ) P.toSubgroup ⟨ℓ, hℓfix⟩ := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := fixedVectors_external_le ρ (fun i => (L i).toSubgroup) v.property
    change (smoothDualTensorMap ρ (PiTensorProduct.map lift y)).val v.val = ℓ.val v.val
    rw [← hw]
    change (smoothDualTensorMap ρ (PiTensorProduct.map lift y)).val (incl w) =
      ℓ.val (incl w)
    rw [smoothDualTensorMap_val, key y w]
    exact LinearMap.congr_fun hy w
  exact congrArg Subtype.val (hinj hres)

end Surjectivity

/-- Proof of `SmoothDualTensorSurjectivityStatement`, with its three universe
levels. -/
theorem smoothDualTensorSurjectivity :
    SmoothDualTensorSurjectivityStatement.{uI, uG, uV} := by
  intro ι _ G _ _ _ V _ _ ρ hρ hcof
  exact smoothDualTensorMap_surjective ρ hρ hcof

end Langlands.FiniteTensor
