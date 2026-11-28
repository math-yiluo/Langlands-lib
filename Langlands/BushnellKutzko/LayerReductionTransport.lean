import Langlands.BushnellKutzko.SimpleTypes
import Langlands.BushnellKutzko.ConjugateRepresentationTransport

/-! # Transport of layer reductions and cuspidal data

Let `L₁` be a lattice chain over `O₁` and `L₂` a lattice chain over `O₂` in the same
additive group `V`, and let `f : V ≃+ V` carry `L₁` onto `L₂` semilinearly for a ring
isomorphism `σO : O₁ ≃+* O₂` (`LatticeChain.SemilinearImage`). Then:

* the chains have the same period (`LatticeChain.SemilinearImage.period_eq`);
* `f` induces additive isomorphisms of the layers `L₁ i / L₁ (i+1) ≃ L₂ i / L₂ (i+1)`
  (`LatticeChain.SemilinearImage.layerEquiv`), semilinear for the induced isomorphism of
  residue fields;
* if `f` is the action of `g ∈ Aut_F(V)`, layer reductions in the sense of
  `IsLayerReduction` (BK93 (5.5.10)) are carried to layer reductions of the conjugate
  group, for the transported bases (`basisTransport`).

A field isomorphism `σ : k ≃ k'` induces `GL_n(k) ≃ GL_n(k')`
(`generalLinearMapEquiv`), and pulling back along it preserves cuspidality
(`isCuspidal_comp_generalLinearMapEquiv`).
-/

noncomputable section

open IsLocalRing
open Langlands.Group.RelativeWeyl

namespace Langlands.BushnellKutzko

/-! ### Transport of bases -/

section Basis

variable {k₁ k₂ M₁ M₂ ι : Type*} [Field k₁] [Field k₂] [AddCommGroup M₁] [Module k₁ M₁]
  [AddCommGroup M₂] [Module k₂ M₂] [Fintype ι]

/-- A basis transported along an additive isomorphism that is semilinear for a field
isomorphism `σ`: the coordinates of `τ x` are the images under `σ` of those of `x`. -/
def basisTransport (σ : k₁ ≃+* k₂) (τ : M₁ ≃+ M₂)
    (hτ : ∀ (c : k₁) (x : M₁), τ (c • x) = σ c • τ x) (b : Module.Basis ι k₁ M₁) :
    Module.Basis ι k₂ M₂ :=
  Module.Basis.ofEquivFun
    { toFun := fun y i => σ (b.equivFun (τ.symm y) i)
      invFun := fun w => τ (b.equivFun.symm fun i => σ.symm (w i))
      map_add' := fun y z => by
        funext i
        simp
      map_smul' := fun c y => by
        have hs : τ.symm (c • y) = σ.symm c • τ.symm y := by
          apply τ.injective
          rw [hτ, τ.apply_symm_apply, τ.apply_symm_apply, σ.apply_symm_apply]
        funext i
        simp [hs]
      left_inv := fun y => by simp
      right_inv := fun w => by
        funext i
        change σ (b.equivFun (τ.symm (τ (b.equivFun.symm fun i => σ.symm (w i)))) i) = w i
        rw [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] }

theorem basisTransport_equivFun (σ : k₁ ≃+* k₂) (τ : M₁ ≃+ M₂)
    (hτ : ∀ (c : k₁) (x : M₁), τ (c • x) = σ c • τ x) (b : Module.Basis ι k₁ M₁) (x : M₁) :
    (basisTransport σ τ hτ b).equivFun (τ x) = fun i => σ (b.equivFun x i) := by
  rw [basisTransport, Module.Basis.equivFun_ofEquivFun]
  funext i
  simp

end Basis

/-! ### Semilinear images of lattice chains -/

section Layer

variable {O₁ K₁ O₂ K₂ V : Type*} [CommRing O₁] [Field K₁] [Algebra O₁ K₁] [CommRing O₂]
  [Field K₂] [Algebra O₂ K₂] [AddCommGroup V] [Module K₁ V] [Module O₁ V]
  [IsScalarTower O₁ K₁ V] [Module K₂ V] [Module O₂ V] [IsScalarTower O₂ K₂ V]

namespace LatticeChain

theorem intervalMk_congr {O K : Type*} [CommRing O] [Field K] [Algebra O K] [Module K V]
    [Module O V] [IsScalarTower O K V] (L : LatticeChain O K V) {i j : ℤ} {v w : V}
    (hvw : v = w) (hv : v ∈ L.lattice i) (hw : w ∈ L.lattice i) :
    L.intervalMk i j v hv = L.intervalMk i j w hw := by
  subst hvw
  rfl

/-- `L₂` is the image of `L₁` under the additive automorphism `f`, which is semilinear for
the ring isomorphism `σO`. -/
structure SemilinearImage (L₁ : LatticeChain O₁ K₁ V) (σO : O₁ ≃+* O₂) (f : V ≃+ V)
    (L₂ : LatticeChain O₂ K₂ V) : Prop where
  map_smul : ∀ (a : O₁) (v : V), f (a • v) = σO a • f v
  mem_iff : ∀ (i : ℤ) (v : V), v ∈ L₁.lattice i ↔ f v ∈ L₂.lattice i

variable {L₁ : LatticeChain O₁ K₁ V} {L₂ : LatticeChain O₂ K₂ V} {σO : O₁ ≃+* O₂} {f : V ≃+ V}

theorem SemilinearImage.symm (h : L₁.SemilinearImage σO f L₂) :
    L₂.SemilinearImage σO.symm f.symm L₁ where
  map_smul b w := by
    apply f.injective
    rw [f.apply_symm_apply, h.map_smul, RingEquiv.apply_symm_apply, f.apply_symm_apply]
  mem_iff i w := by
    rw [h.mem_iff i (f.symm w), f.apply_symm_apply]

/-- The restriction of `f` to `L₁ i → L₂ i`. -/
def SemilinearImage.latticeMap (h : L₁.SemilinearImage σO f L₂) (i : ℤ) :
    L₁.lattice i →ₛₗ[(σO : O₁ →+* O₂)] L₂.lattice i where
  toFun v := ⟨f (v : V), (h.mem_iff i v).1 v.2⟩
  map_add' v w := Subtype.ext (map_add f (v : V) w)
  map_smul' a v := Subtype.ext (h.map_smul a (v : V))

/-- The map of layers `L₁ i / L₁ (i+1) → L₂ i / L₂ (i+1)` induced by `f`. -/
def SemilinearImage.layerMap (h : L₁.SemilinearImage σO f L₂) (i : ℤ) :
    L₁.Layer i →ₛₗ[(σO : O₁ →+* O₂)] L₂.Layer i :=
  (L₁.intervalSubmodule i (i + 1)).mapQ (L₂.intervalSubmodule i (i + 1)) (h.latticeMap i)
    (fun v hv => (h.mem_iff (i + 1) v).1 hv)

/-- The additive isomorphism of layers induced by `f`. -/
def SemilinearImage.layerEquiv (h : L₁.SemilinearImage σO f L₂) (i : ℤ) :
    L₁.Layer i ≃+ L₂.Layer i where
  toFun := h.layerMap i
  invFun := h.symm.layerMap i
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H v => exact congrArg Submodule.Quotient.mk (Subtype.ext (f.symm_apply_apply v))
  right_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H v => exact congrArg Submodule.Quotient.mk (Subtype.ext (f.apply_symm_apply v))
  map_add' := map_add (h.layerMap i)

theorem SemilinearImage.layerEquiv_mk (h : L₁.SemilinearImage σO f L₂) (i : ℤ) (v : V)
    (hv : v ∈ L₁.lattice i) :
    h.layerEquiv i (L₁.intervalMk i (i + 1) v hv) =
      L₂.intervalMk i (i + 1) (f v) ((h.mem_iff i v).1 hv) :=
  rfl

theorem SemilinearImage.layerEquiv_smul (h : L₁.SemilinearImage σO f L₂) (i : ℤ) (a : O₁)
    (x : L₁.Layer i) : h.layerEquiv i (a • x) = σO a • h.layerEquiv i x :=
  (h.layerMap i).map_smulₛₗ a x

/-- Corresponding chains have the same period. -/
theorem SemilinearImage.period_eq (h : L₁.SemilinearImage σO f L₂) :
    L₂.period = L₁.period := by
  have := RingHomInvPair.of_ringEquiv σO
  have := RingHomInvPair.of_ringEquiv_symm σO
  let fₛ : V ≃ₛₗ[(σO : O₁ →+* O₂)] V :=
    { toFun := f
      invFun := f.symm
      map_add' := map_add f
      map_smul' := h.map_smul
      left_inv := f.left_inv
      right_inv := f.right_inv }
  have hmap : ∀ i, L₂.lattice i = (L₁.lattice i).map (fₛ : V →ₛₗ[(σO : O₁ →+* O₂)] V) := by
    intro i
    ext w
    rw [Submodule.mem_map_equiv]
    change w ∈ L₂.lattice i ↔ f.symm w ∈ L₁.lattice i
    rw [h.mem_iff i (f.symm w), f.apply_symm_apply]
  refine (L₂.period_unique fun i => ?_).symm
  rw [hmap, hmap, L₁.lattice_add_period, map_smul_semilinear,
    map_ideal_ringJacobson (σO : O₁ →+* O₂) σO.bijective]

variable [IsLocalRing O₁] [IsLocalRing O₂]

/-- The layer isomorphism is semilinear for the induced isomorphism of residue fields. -/
theorem SemilinearImage.layerEquiv_residue_smul (h : L₁.SemilinearImage σO f L₂) (i : ℤ)
    (c : ResidueField O₁) (x : L₁.Layer i) :
    h.layerEquiv i (c • x) = ResidueField.mapEquiv σO c • h.layerEquiv i x := by
  obtain ⟨a, rfl⟩ := residue_surjective c
  have h1 : residue O₁ a • x = a • x := by
    rw [← ResidueField.algebraMap_eq, algebraMap_smul]
  have h2 : residue O₂ (σO a) • h.layerEquiv i x = σO a • h.layerEquiv i x := by
    rw [← ResidueField.algebraMap_eq, algebraMap_smul]
  rw [h1, h.layerEquiv_smul, ResidueField.mapEquiv_apply, ResidueField.map_residue]
  exact h2.symm

/-- The basis of a layer of `L₂` transported from a basis of the layer of `L₁`. -/
def SemilinearImage.layerBasis (h : L₁.SemilinearImage σO f L₂) {ι : Type*} [Fintype ι]
    (i : ℤ) (b : Module.Basis ι (ResidueField O₁) (L₁.Layer i)) :
    Module.Basis ι (ResidueField O₂) (L₂.Layer i) :=
  basisTransport (ResidueField.mapEquiv σO) (h.layerEquiv i) (h.layerEquiv_residue_smul i) b

theorem SemilinearImage.layerBasis_equivFun (h : L₁.SemilinearImage σO f L₂) {ι : Type*}
    [Fintype ι] (i : ℤ) (b : Module.Basis ι (ResidueField O₁) (L₁.Layer i)) (x : L₁.Layer i) :
    (h.layerBasis i b).equivFun (h.layerEquiv i x) =
      fun j => ResidueField.mapEquiv σO (b.equivFun x j) :=
  basisTransport_equivFun _ _ _ b x

/-- Layer reductions are carried by conjugation (BK93 (5.5.10)): if `f` is the action of
`g` and `U₂ = gU₁g⁻¹`, then the transported bases and the transported reduction map form a
layer reduction of `U₂` for `L₂`. -/
theorem SemilinearImage.isLayerReduction {F : Type*} [Field F] [Module F V]
    (h : L₁.SemilinearImage σO f L₂) (g : (Module.End F V)ˣ)
    (hfg : ∀ v, f v = (g : Module.End F V) v)
    {U₁ U₂ : Subgroup (Module.End F V)ˣ} (hU : U₂ = conjugateSubgroup g U₁)
    (hU₁ : ∀ u ∈ U₁, ∀ (i : ℤ) (v : V), v ∈ L₁.lattice i →
      (u : Module.End F V) v ∈ L₁.lattice i)
    (hU₂ : ∀ u ∈ U₂, ∀ (i : ℤ) (v : V), v ∈ L₂.lattice i →
      (u : Module.End F V) v ∈ L₂.lattice i)
    {e d : ℕ} {b₁ : ∀ i : Fin e, Module.Basis (Fin d) (ResidueField O₁) (L₁.Layer ((i : ℕ) : ℤ))}
    {φ₁ : U₁ →* (Fin e → GeneralLinear d (ResidueField O₁))}
    (b₂ : ∀ i : Fin e, Module.Basis (Fin d) (ResidueField O₂) (L₂.Layer ((i : ℕ) : ℤ)))
    (φ₂ : U₂ →* (Fin e → GeneralLinear d (ResidueField O₂)))
    (hb : ∀ (i : Fin e) (x : L₁.Layer ((i : ℕ) : ℤ)),
      (b₂ i).equivFun (h.layerEquiv _ x) =
        fun j => ResidueField.mapEquiv σO ((b₁ i).equivFun x j))
    (hφ : ∀ (u : U₂) (i : Fin e),
      ((φ₂ u i : GeneralLinear d (ResidueField O₂)) :
          Matrix (Fin d) (Fin d) (ResidueField O₂)) =
        ((φ₁ ((conjEquivOfEq g hU).symm u) i : GeneralLinear d (ResidueField O₁)) :
          Matrix (Fin d) (Fin d) (ResidueField O₁)).map (ResidueField.mapEquiv σO))
    (hred : IsLayerReduction L₁ U₁ hU₁ b₁ φ₁) : IsLayerReduction L₂ U₂ hU₂ b₂ φ₂ := by
  intro u i v hv
  set u₁ := (conjEquivOfEq g hU).symm u with hu₁
  have hv₁ : f.symm v ∈ L₁.lattice ((i : ℕ) : ℤ) := by
    rw [h.mem_iff, f.apply_symm_apply]
    exact hv
  have hgv : (g : Module.End F V) (f.symm v) = v := by
    rw [← hfg, f.apply_symm_apply]
  have huv : ((u : (Module.End F V)ˣ) : Module.End F V) v =
      f (((u₁ : (Module.End F V)ˣ) : Module.End F V) (f.symm v)) := by
    rw [hfg, hu₁, coe_conjEquivOfEq_symm]
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [hgv, ← Module.End.mul_apply (g : Module.End F V), ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply]
  have hmk : L₂.intervalMk _ _ (((u : (Module.End F V)ˣ) : Module.End F V) v)
      (hU₂ u u.2 _ v hv) =
      h.layerEquiv _ (L₁.intervalMk _ _ (((u₁ : (Module.End F V)ˣ) : Module.End F V)
        (f.symm v)) (hU₁ u₁ u₁.2 _ _ hv₁)) := by
    rw [h.layerEquiv_mk]
    exact L₂.intervalMk_congr huv _ _
  have hmk' : L₂.intervalMk _ _ v hv = h.layerEquiv _ (L₁.intervalMk _ _ (f.symm v) hv₁) := by
    rw [h.layerEquiv_mk]
    exact L₂.intervalMk_congr (f.apply_symm_apply v).symm _ _
  rw [hmk, hmk', hb, hb, hred u₁ i (f.symm v) hv₁, hφ]
  funext j
  exact RingHom.map_mulVec (ResidueField.mapEquiv σO).toRingHom _ _ j

end LatticeChain

end Layer

/-! ### General linear groups over isomorphic fields -/

section GeneralLinear

variable {k k' : Type*} [Field k] [Field k']

/-- The isomorphism `GL_n(k) ≃ GL_n(k')` induced by a field isomorphism `σ`, applying `σ`
to the matrix entries. -/
def generalLinearMapEquiv (σ : k ≃+* k') (n : ℕ) : GeneralLinear n k ≃* GeneralLinear n k' :=
  Units.mapEquiv σ.mapMatrix.toMulEquiv

theorem coe_generalLinearMapEquiv (σ : k ≃+* k') (n : ℕ) (g : GeneralLinear n k) :
    ((generalLinearMapEquiv σ n g : GeneralLinear n k') : Matrix (Fin n) (Fin n) k') =
      (g : Matrix (Fin n) (Fin n) k).map σ :=
  rfl

theorem generalLinearMapEquiv_apply_apply (σ : k ≃+* k') (n : ℕ) (g : GeneralLinear n k)
    (a b : Fin n) : (generalLinearMapEquiv σ n g) a b = σ (g a b) :=
  rfl

theorem generalLinearMapEquiv_symm_apply_apply (σ : k ≃+* k') (n : ℕ) (g : GeneralLinear n k')
    (a b : Fin n) : ((generalLinearMapEquiv σ n).symm g) a b = σ.symm (g a b) :=
  rfl

/-- Cuspidality is preserved by pulling back along `GL_n(k') ≃ GL_n(k)` for a field
isomorphism. -/
theorem isCuspidal_comp_generalLinearMapEquiv (σ : k ≃+* k') {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GeneralLinear n k) W}
    (hρ : FiniteGeneralLinear.IsCuspidal ρ) :
    FiniteGeneralLinear.IsCuspidal (ρ.comp (generalLinearMapEquiv σ n).symm.toMonoidHom) := by
  set μ := generalLinearMapEquiv σ n
  intro B hB w hw
  have hB' : B.parabolic k ≠ ⊤ := by
    intro htop
    apply hB
    rw [eq_top_iff]
    intro g _
    have hg : μ.symm g ∈ B.parabolic k := htop ▸ Subgroup.mem_top _
    rw [B.mem_parabolic_iff] at hg ⊢
    intro i j a b hij
    have h0 := hg i j a b hij
    rw [generalLinearMapEquiv_symm_apply_apply] at h0
    simpa using h0
  refine hρ B hB' w fun u hu => ?_
  have hu' : μ u ∈ B.unipotentSubgroup k' := by
    rw [B.mem_unipotentSubgroup_iff] at hu ⊢
    obtain ⟨hp, hd⟩ := hu
    refine ⟨?_, fun i a b => ?_⟩
    · rw [B.mem_parabolic_iff] at hp ⊢
      intro i j a b hij
      rw [generalLinearMapEquiv_apply_apply, hp i j a b hij, map_zero]
    · rw [generalLinearMapEquiv_apply_apply, hd i a b]
      split_ifs <;> simp
  have := hw (μ u) hu'
  simpa [μ] using this

/-- The tensor power of a pulled back representation, pulled back along the product
isomorphism, is the original tensor power. -/
theorem tensorPowerRepresentation_comp_piMap {H H' W : Type*} [Group H] [Group H']
    [AddCommGroup W] [Module ℂ W] (σ₀ : Representation ℂ H W) (μ : H ≃* H') (e : ℕ) :
    (tensorPowerRepresentation (σ₀.comp μ.symm.toMonoidHom) e).comp
        (MonoidHom.piMap fun _ : Fin e => μ.toMonoidHom) =
      tensorPowerRepresentation σ₀ e := by
  refine MonoidHom.ext fun x => ?_
  simp only [tensorPowerRepresentation, MonoidHom.coe_comp, Function.comp_apply]
  congr 1
  funext i
  change σ₀ (μ.symm (μ (x i))) = σ₀ (x i)
  rw [MulEquiv.symm_apply_apply]

end GeneralLinear

end Langlands.BushnellKutzko
