import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityStatement
import Langlands.GroupTheory.TransferDoubleCoset

/-!
# The local Weil transfer square in a tower of embeddings

Let `fK : F → K`, `fE : F → E` and `g : K → E` be embeddings of p-adic fields whose
images in the algebraic closure of `F` are compatible, `ε_E ∘ g = ε_K` for the
embeddings `ε` given by `extensionFieldEmbedding`. Assuming the published square
`ExtensionWeilTransferReciprocityStatement`, the transfer from `W_K` to the subgroup
`N` of elements whose image in `W_F` lies in the image of `W_E` corresponds under
geometric Weil reciprocity to the inclusion `Kˣ → Eˣ`.

The chosen closure embeddings of the three Galois maps differ by an element `γ` of
`G_K`; conjugation by `γ` carries the image of `W_E` in `W_K` onto `N`, and it does
not change classes in the closed-commutator quotient of `W_K`.
-/

noncomputable section

namespace Langlands.LocalClassField

open Weil Weil.Local

universe u v w

/-- The profinite completion of the integers is commutative: the integers are dense
in it and it is Hausdorff. -/
theorem profiniteIntegers_mul_comm (a b : ProfiniteIntegers) : a * b = b * a := by
  have hd := ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree)
  have h₁ : ∀ (n : Degree) (b : ProfiniteIntegers), frobenius n * b = b * frobenius n := by
    intro n b
    refine hd.induction_on (p := fun b : ProfiniteIntegers => frobenius n * b = b * frobenius n)
      b (isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const))
      ?_
    intro m
    change frobenius n * frobenius m = frobenius m * frobenius n
    rw [← map_mul, ← map_mul, mul_comm]
  refine hd.induction_on (p := fun a : ProfiniteIntegers => a * b = b * a) a
    (isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)) ?_
  intro m
  exact h₁ m b

section Conjugation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{v} p)

/-- The residue degree is invariant under conjugation. -/
theorem localResidueDegree_conj (γ σ : Field.absoluteGaloisGroup K.Carrier) :
    localResidueDegree K (γ * σ * γ⁻¹) = localResidueDegree K σ := by
  rw [map_mul, map_mul, map_inv, profiniteIntegers_mul_comm (localResidueDegree K γ),
    mul_inv_cancel_right]

/-- Conjugation of the Galois component of `W_K` by `γ ∈ G_K`, keeping the degree:
`(σ, m) ↦ (γ σ γ⁻¹, m)`. -/
def weilConj (γ : Field.absoluteGaloisGroup K.Carrier) : localWeilGroup K →* localWeilGroup K :=
  (((MulAut.conj γ).toMonoidHom.prodMap (MonoidHom.id Degree)).comp
      (pullbackSubgroup (localResidueDegree K)).subtype).codRestrict
    (pullbackSubgroup (localResidueDegree K)) fun w => by
      have hw : localResidueDegree K w.val.1 = frobenius w.val.2 := w.property
      change localResidueDegree K (γ * w.val.1 * γ⁻¹) = frobenius w.val.2
      rw [localResidueDegree_conj, hw]

@[simp] theorem localProjection_weilConj (γ : Field.absoluteGaloisGroup K.Carrier)
    (w : localWeilGroup K) :
    localProjection K (weilConj K γ w) = γ * localProjection K w * γ⁻¹ := rfl

@[simp] theorem localDegree_weilConj (γ : Field.absoluteGaloisGroup K.Carrier)
    (w : localWeilGroup K) :
    localDegree K (weilConj K γ w) = localDegree K w := rfl

theorem weilConj_weilConj (γ δ : Field.absoluteGaloisGroup K.Carrier) (w : localWeilGroup K) :
    weilConj K γ (weilConj K δ w) = weilConj K (γ * δ) w := by
  apply projection_injective (localResidueDegree K)
  change γ * (δ * localProjection K w * δ⁻¹) * γ⁻¹ = γ * δ * localProjection K w * (γ * δ)⁻¹
  group

theorem weilConj_one (w : localWeilGroup K) : weilConj K 1 w = w := by
  apply projection_injective (localResidueDegree K)
  change 1 * localProjection K w * 1⁻¹ = localProjection K w
  group

theorem weilConj_inv_weilConj (γ : Field.absoluteGaloisGroup K.Carrier) (w : localWeilGroup K) :
    weilConj K γ⁻¹ (weilConj K γ w) = w := by
  rw [weilConj_weilConj, inv_mul_cancel, weilConj_one]

theorem weilConj_weilConj_inv (γ : Field.absoluteGaloisGroup K.Carrier) (w : localWeilGroup K) :
    weilConj K γ (weilConj K γ⁻¹ w) = w := by
  rw [weilConj_weilConj, mul_inv_cancel, weilConj_one]

/-- On the image of `W_K` in `G_K`, `weilConj` is inner conjugation. -/
theorem weilConj_localProjection (v w : localWeilGroup K) :
    weilConj K (localProjection K v) w = v * w * v⁻¹ := by
  apply projection_injective (localResidueDegree K)
  change localProjection K v * localProjection K w * (localProjection K v)⁻¹ =
    localProjection K (v * w * v⁻¹)
  rw [map_mul, map_mul, map_inv]

theorem continuous_weilConj_apply (w : localWeilGroup K) :
    Continuous fun γ : Field.absoluteGaloisGroup K.Carrier => weilConj K γ w := by
  refine continuous_induced_rng.2 ?_
  exact ((continuous_id.mul continuous_const).mul continuous_inv).prodMk continuous_const

/-- Conjugation by `γ ∈ G_K` does not change classes in the closed-commutator
quotient: `γ ↦ (weilConj γ y)⁻¹ y` is continuous, takes commutator values on the
dense image of `W_K`, and the closed commutator subgroup is closed. -/
theorem projection_weilConj (γ : Field.absoluteGaloisGroup K.Carrier) (y : localWeilGroup K) :
    WeilQuotients.projection (localResidueDegree K) (weilConj K γ y) =
      WeilQuotients.projection (localResidueDegree K) y := by
  let C := (commutator (localWeilGroup K)).topologicalClosure
  have key : ∀ δ : Field.absoluteGaloisGroup K.Carrier, (weilConj K δ y)⁻¹ * y ∈ C := by
    intro δ
    refine (localProjection_denseRange K).induction_on
      (p := fun δ => (weilConj K δ y)⁻¹ * y ∈ C) δ ?_ ?_
    · exact (Subgroup.isClosed_topologicalClosure _).preimage
        ((continuous_weilConj_apply K y).inv.mul continuous_const)
    · intro v
      apply Subgroup.le_topologicalClosure
      rw [weilConj_localProjection]
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top v) (Subgroup.mem_top y⁻¹)
      rw [commutatorElement_def, inv_inv] at hc
      have h : (v * y * v⁻¹)⁻¹ * y = v * y⁻¹ * v⁻¹ * y := by group
      rw [h]
      exact hc
  exact QuotientGroup.eq.mpr (key γ)

/-- Reciprocity is invariant under `weilConj`. No property of the candidate is used. -/
theorem reciprocityUnits_weilConj (e : LocalFactor.RankOne.ReciprocityCandidate K)
    (γ : Field.absoluteGaloisGroup K.Carrier) (y : localWeilGroup K) :
    letI := K.canonicalTopologicalData.topology
    LocalFactor.RankOne.reciprocityUnits K e (weilConj K γ y) =
      LocalFactor.RankOne.reciprocityUnits K e y := by
  let := K.canonicalTopologicalData.topology
  change e (WeilQuotients.projection (localResidueDegree K) (weilConj K γ y)) =
    e (WeilQuotients.projection (localResidueDegree K) y)
  rw [projection_weilConj]

end Conjugation

section Tower

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (K : PadicField.{v} p)
  (E : PadicField.{w} p) (fK : F.Carrier →ₐ[Padic p] K.Carrier)
  (fE : F.Carrier →ₐ[Padic p] E.Carrier) (g : K.Carrier →ₐ[Padic p] E.Carrier)

private theorem lift_galoisMap_apply {F : PadicField.{u} p} {E : PadicField.{w} p}
    (f : F.Carrier →ₐ[Padic p] E.Carrier) (σ : Field.absoluteGaloisGroup E.Carrier)
    (x : AlgebraicClosure F.Carrier) :
    extensionClosureLift F E f (AlgEquiv.toAlgHom (extensionGaloisMap F E f σ) x) =
      AlgEquiv.toAlgHom σ (extensionClosureLift F E f x) :=
  extensionClosureLift_galoisMap F E f σ x

/-- Compatible closure embeddings force `g ∘ fK = fE`. -/
theorem comp_apply_eq_of_fieldEmbedding
    (hg : ∀ x, extensionFieldEmbedding F E fE (g x) = extensionFieldEmbedding F K fK x)
    (x : F.Carrier) : g (fK x) = fE x := by
  apply (extensionFieldEmbedding F E fE).injective
  rw [hg, extensionFieldEmbedding_comp, extensionFieldEmbedding_comp]

/-- The automorphism `λ_{fE}⁻¹ ∘ λ_g ∘ λ_{fK}` of the algebraic closure of `F`, where
`λ` denotes the chosen closure embeddings `extensionClosureLift`. -/
def towerClosureAut (hgf : ∀ x, g (fK x) = fE x) : Field.absoluteGaloisGroup F.Carrier :=
  AlgEquiv.ofRingEquiv
    (f := ((extensionClosureEquiv F K fK).trans (extensionClosureEquiv K E g)).trans
      (extensionClosureEquiv F E fE).symm) fun x => by
    apply (extensionClosureEquiv F E fE).injective
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, extensionClosureEquiv_apply]
    simp only [extensionClosureLift_algebraMap, hgf]

theorem extensionClosureLift_towerClosureAut (hgf : ∀ x, g (fK x) = fE x)
    (x : AlgebraicClosure F.Carrier) :
    extensionClosureLift F E fE (AlgEquiv.toAlgHom (towerClosureAut F K E fK fE g hgf) x) =
      extensionClosureLift K E g (extensionClosureLift F K fK x) := by
  change extensionClosureEquiv F E fE ((extensionClosureEquiv F E fE).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The Galois maps of a compatible tower agree up to conjugation by some `γ ∈ G_K`:
`ι_{fE}(σ) = ι_{fK}(γ ι_g(σ) γ⁻¹)`. -/
theorem exists_extensionGaloisMap_tower
    (hg : ∀ x, extensionFieldEmbedding F E fE (g x) = extensionFieldEmbedding F K fK x) :
    ∃ γ : Field.absoluteGaloisGroup K.Carrier, ∀ σ : Field.absoluteGaloisGroup E.Carrier,
      extensionGaloisMap F E fE σ =
        extensionGaloisMap F K fK (γ * extensionGaloisMap K E g σ * γ⁻¹) := by
  have hgf := comp_apply_eq_of_fieldEmbedding F K E fK fE g hg
  have hfix : towerClosureAut F K E fK fE g hgf ∈
      (extensionIntermediateField F K fK).fixingSubgroup := by
    refine (IntermediateField.mem_fixingSubgroup_iff (extensionIntermediateField F K fK)
      (towerClosureAut F K E fK fE g hgf)).mpr ?_
    intro y hy
    obtain ⟨x, rfl⟩ := (mem_extensionIntermediateField F K fK y).mp hy
    apply (extensionClosureEquiv F E fE).injective
    rw [extensionClosureEquiv_apply, extensionClosureEquiv_apply]
    refine (extensionClosureLift_towerClosureAut F K E fK fE g hgf _).trans ?_
    rw [extensionClosureLift_fieldEmbedding, extensionClosureLift_algebraMap, ← hg,
      extensionClosureLift_fieldEmbedding]
  rw [← extensionGaloisMap_range] at hfix
  obtain ⟨γ, hγ⟩ := hfix
  change extensionGaloisMap F K fK γ = towerClosureAut F K E fK fE g hgf at hγ
  refine ⟨γ, fun σ => ?_⟩
  rw [map_mul, map_mul, map_inv, hγ, eq_mul_inv_iff_mul_eq]
  apply AlgEquiv.ext
  intro x
  apply (extensionClosureLift_bijective F E fE).1
  change extensionClosureLift F E fE (AlgEquiv.toAlgHom (extensionGaloisMap F E fE σ)
      (AlgEquiv.toAlgHom (towerClosureAut F K E fK fE g hgf) x)) =
    extensionClosureLift F E fE (AlgEquiv.toAlgHom (towerClosureAut F K E fK fE g hgf)
      (AlgEquiv.toAlgHom (extensionGaloisMap F K fK (extensionGaloisMap K E g σ)) x))
  rw [lift_galoisMap_apply,
    extensionClosureLift_towerClosureAut, extensionClosureLift_towerClosureAut,
    lift_galoisMap_apply, lift_galoisMap_apply]

/-- The Weil maps of the tower agree up to `weilConj γ`. -/
theorem extensionWeilMap_weilConj_tower (γ : Field.absoluteGaloisGroup K.Carrier)
    (hγ : ∀ σ, extensionGaloisMap F E fE σ =
      extensionGaloisMap F K fK (γ * extensionGaloisMap K E g σ * γ⁻¹))
    (x : localWeilGroup E) :
    extensionWeilMap F K fK (weilConj K γ (extensionWeilMap K E g x)) =
      extensionWeilMap F E fE x := by
  apply projection_injective (localResidueDegree F)
  change extensionGaloisMap F K fK (γ * extensionGaloisMap K E g (localProjection E x) * γ⁻¹) =
    extensionGaloisMap F E fE (localProjection E x)
  rw [hγ]

/-- `weilConj γ` carries the image of `W_E` in `W_K` onto the preimage in `W_K` of the
image of `W_E` in `W_F`. -/
theorem mem_range_iff_weilConj_mem (γ : Field.absoluteGaloisGroup K.Carrier)
    (hγ : ∀ σ, extensionGaloisMap F E fE σ =
      extensionGaloisMap F K fK (γ * extensionGaloisMap K E g σ * γ⁻¹))
    (l : localWeilGroup K) :
    l ∈ (extensionWeilMap K E g).toMonoidHom.range ↔
      weilConj K γ l ∈ (extensionWeilMap F E fE).toMonoidHom.range.comap
        (extensionWeilMap F K fK).toMonoidHom := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (extensionWeilMap_weilConj_tower F K E fK fE g γ hγ x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have h : weilConj K γ (extensionWeilMap K E g x) = weilConj K γ l := by
      apply extensionWeilMap_injective F K fK
      rw [extensionWeilMap_weilConj_tower F K E fK fE g γ hγ x]
      exact hx
    have h' := congrArg (weilConj K γ⁻¹) h
    rwa [weilConj_inv_weilConj, weilConj_inv_weilConj] at h'

/-- The transfer to the preimage subgroup at `weilConj γ y` is the transfer to the image
of `W_E` along `g` at `y`. -/
theorem transfer_weilConj_tower (eE : LocalFactor.RankOne.ReciprocityCandidate E)
    (γ : Field.absoluteGaloisGroup K.Carrier)
    (hγ : ∀ σ, extensionGaloisMap F E fE σ =
      extensionGaloisMap F K fK (γ * extensionGaloisMap K E g σ * γ⁻¹))
    (y : localWeilGroup K) :
    letI := E.canonicalTopologicalData.topology
    haveI := extensionWeilMap_range_finiteIndex F E fE
    haveI := extensionWeilMap_range_finiteIndex K E g
    MonoidHom.transfer ((LocalFactor.RankOne.reciprocityUnits E eE).toMonoidHom.comp
        ((InductionAlong.rangeInverse (extensionWeilMap F E fE).toMonoidHom
            (extensionWeilMap_injective F E fE)).comp
          ((extensionWeilMap F K fK).toMonoidHom.subgroupComap
            (extensionWeilMap F E fE).toMonoidHom.range))) (weilConj K γ y) =
      MonoidHom.transfer ((LocalFactor.RankOne.reciprocityUnits E eE).toMonoidHom.comp
        (InductionAlong.rangeInverse (extensionWeilMap K E g).toMonoidHom
          (extensionWeilMap_injective K E g))) y := by
  let := E.canonicalTopologicalData.topology
  have := extensionWeilMap_range_finiteIndex F E fE
  have := extensionWeilMap_range_finiteIndex K E g
  have hK : ∀ (_ : Unit) (l : localWeilGroup K),
      l ∈ (extensionWeilMap K E g).toMonoidHom.range ↔
        (1 : localWeilGroup K)⁻¹ * weilConj K γ l * 1 ∈
          (extensionWeilMap F E fE).toMonoidHom.range.comap
            (extensionWeilMap F K fK).toMonoidHom := by
    intro _ l
    rw [inv_one, one_mul, mul_one]
    exact mem_range_iff_weilConj_mem F K E fK fE g γ hγ l
  rw [GroupTheory.Transfer.transfer_comp_eq_prod_of_conj (ψ := weilConj K γ)
    (t := fun _ : Unit => (1 : localWeilGroup K))
    (K := fun _ : Unit => (extensionWeilMap K E g).toMonoidHom.range) (hK := hK) _
    (fun _ => (LocalFactor.RankOne.reciprocityUnits E eE).toMonoidHom.comp
      (InductionAlong.rangeInverse (extensionWeilMap K E g).toMonoidHom
        (extensionWeilMap_injective K E g))) ?_ ?_ ?_ y, Fintype.prod_unique]
  · rintro _ ⟨_, x, rfl⟩
    simp only [MonoidHom.comp_apply, InductionAlong.rangeInverse_apply]
    congr 1
    apply extensionWeilMap_injective F E fE
    refine Eq.trans ?_ (InductionAlong.apply_rangeInverse _ _ _).symm
    change extensionWeilMap F E fE x =
      extensionWeilMap F K fK (1⁻¹ * weilConj K γ (extensionWeilMap K E g x) * 1)
    rw [inv_one, one_mul, mul_one, extensionWeilMap_weilConj_tower F K E fK fE g γ hγ x]
  · intro w
    refine ⟨(), weilConj K γ⁻¹ w, 1, Subgroup.one_mem _, ?_⟩
    change w = weilConj K γ (weilConj K γ⁻¹ w) * 1 * 1
    rw [mul_one, mul_one, weilConj_weilConj_inv]
  · intro _ _ _ _ _ _
    rfl

/-- **Tower transfer square.** For compatible embeddings `fK : F → K`, `fE : F → E`,
`g : K → E`, the transfer from `W_K` to `N = ι_{fK}⁻¹(ι_{fE}(W_E))` of geometric
reciprocity of `E` (through the identification `N ≅ W_E` given by `ι_{fE}`) is
geometric reciprocity of `K` followed by `g : Kˣ → Eˣ`, assuming the published
transfer square for embeddings. -/
theorem extensionWeilTransferReciprocity_tower
    (hsq : ExtensionWeilTransferReciprocityStatement.{v, w})
    (hg : ∀ x, extensionFieldEmbedding F E fE (g x) = extensionFieldEmbedding F K fK x)
    (eK : LocalFactor.RankOne.ReciprocityCandidate K)
    (eE : LocalFactor.RankOne.ReciprocityCandidate E)
    (hK : GeometricWeilReciprocityRelation K K.canonicalTopologicalData eK)
    (hE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE) :
    letI := K.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    haveI := extensionWeilMap_range_finiteIndex F E fE
    ∀ y : localWeilGroup K,
      MonoidHom.transfer ((LocalFactor.RankOne.reciprocityUnits E eE).toMonoidHom.comp
          ((InductionAlong.rangeInverse (extensionWeilMap F E fE).toMonoidHom
              (extensionWeilMap_injective F E fE)).comp
            ((extensionWeilMap F K fK).toMonoidHom.subgroupComap
              (extensionWeilMap F E fE).toMonoidHom.range))) y =
        Units.map g.toRingHom.toMonoidHom (LocalFactor.RankOne.reciprocityUnits K eK y) := by
  let := K.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  have := extensionWeilMap_range_finiteIndex F E fE
  intro y
  obtain ⟨γ, hγ⟩ := exists_extensionGaloisMap_tower F K E fK fE g hg
  have h₁ := transfer_weilConj_tower F K E fK fE g eE γ hγ (weilConj K γ⁻¹ y)
  rw [weilConj_weilConj_inv] at h₁
  rw [h₁, hsq p K E g eK eE hK hE (weilConj K γ⁻¹ y), reciprocityUnits_weilConj]

/-- A compatible `g` exists as soon as the image of `K` in the closure of `F` is
contained in that of `E`. -/
theorem exists_fieldEmbedding_tower
    (h : extensionIntermediateField F K fK ≤ extensionIntermediateField F E fE) :
    ∃ g : K.Carrier →ₐ[Padic p] E.Carrier,
      ∀ x, extensionFieldEmbedding F E fE (g x) = extensionFieldEmbedding F K fK x := by
  let := extensionAlgebra F K fK
  let := extensionAlgebra F E fE
  let g₀ : K.Carrier →+* E.Carrier :=
    (extensionIntermediateFieldEquiv F E fE).symm.toRingEquiv.toRingHom.comp
      ((IntermediateField.inclusion h).toRingHom.comp
        (extensionIntermediateFieldEquiv F K fK).toRingEquiv.toRingHom)
  have hg₀ : ∀ x, extensionFieldEmbedding F E fE (g₀ x) = extensionFieldEmbedding F K fK x := by
    intro x
    change ((extensionIntermediateFieldEquiv F E fE
      ((extensionIntermediateFieldEquiv F E fE).symm
        (IntermediateField.inclusion h (extensionIntermediateFieldEquiv F K fK x))) :
          AlgebraicClosure F.Carrier)) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl
  refine ⟨{ g₀ with commutes' := fun a => ?_ }, hg₀⟩
  apply (extensionFieldEmbedding F E fE).injective
  change extensionFieldEmbedding F E fE (g₀ (algebraMap (Padic p) K.Carrier a)) = _
  rw [hg₀, ← fK.commutes, ← fE.commutes, extensionFieldEmbedding_comp,
    extensionFieldEmbedding_comp]

end Tower

end Langlands.LocalClassField
