import Langlands.GroupScheme.Rational.GeneralLinearStatement
import Langlands.GroupScheme.Rational.GeneralLinearGenericCentralizer
import Langlands.GroupScheme.Reductive.GeneralLinearMaximal
import Langlands.LinearAlgebra.RootSystemTypeA

/-! # Proof: the rational structure of `GL_n` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan Langlands.LinearAlgebra.RootSystemTypeA

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift n)

/-! ### Maximality and relative roots -/

/-- The diagonal torus of `GL_n` is a maximal split torus. -/
theorem isMaximalSplitTorus_diagonalTorus :
    IsMaximalSplitTorus (diagonalTorus n (CommRingCat.of k)) := by
  obtain ⟨-, hcl, hmax⟩ := isMaximalTorus_diagonalTorus (n := n) k
  exact ⟨⟨isSplitTorus_splitTorus _, hcl⟩,
    fun T' i' hi' f hf => hmax T' i' f hi'.1.isTorus hi'.2 hf⟩

/-- The relative roots of the diagonal torus of `GL_n` are the characters `eᵢ - eⱼ`, `i ≠ j`. -/
theorem relativeRoots_diagonalTorus :
    relativeRoots (diagonalTorus n (CommRingCat.of k)) =
      {χ | ∃ i j : n, i ≠ j ∧ splitTorus.characterLatticeEquiv k (ULift.{u} n) χ =
        Pi.single (ULift.up i) 1 - Pi.single (ULift.up j) 1} :=
  roots_diagonalTorus

/-! ### Rational coordinates -/

/-- The coordinates `ℚ ⊗ X^*(D_n) ≃ ℚ^n`. -/
abbrev ratCoord : ℚ ⊗[ℤ] characterLattice 𝔻 ≃ₗ[ℚ] (ULift.{u} n → ℚ) :=
  tensorEquivPi (splitTorus.characterLatticeEquiv k (ULift.{u} n))

instance : FiniteDimensional ℚ (ℚ ⊗[ℤ] characterLattice 𝔻) :=
  LinearEquiv.finiteDimensional (ratCoord (n := n) k).symm

omit [DecidableEq n] in
/-- An automorphism of `X^*(D_n)` permuting the integer coordinates permutes the rational
coordinates in the same way. -/
theorem ratCoord_ratAut (e : characterLattice 𝔻 ≃ₗ[ℤ] characterLattice 𝔻)
    (τ : ULift.{u} n → ULift.{u} n)
    (he : ∀ χ, splitTorus.characterLatticeEquiv k (ULift.{u} n) (e χ) =
      splitTorus.characterLatticeEquiv k (ULift.{u} n) χ ∘ τ)
    (x : ℚ ⊗[ℤ] characterLattice 𝔻) :
    ratCoord k (ratAut e x) = ratCoord k x ∘ τ := by
  induction x using TensorProduct.inductionOn with
  | tmul q χ =>
    rw [ratAut_tmul, tensorEquivPi_tmul, tensorEquivPi_tmul, he]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    rfl

/-- The permutation `c ↦ w⁻¹ c` of `ULift n`. -/
def ulPerm (w : Equiv.Perm n) : Equiv.Perm (ULift.{u} n) :=
  Equiv.permCongr Equiv.ulift.symm w⁻¹

omit [Fintype n] [DecidableEq n] in
theorem ulPerm_apply (w : Equiv.Perm n) (c : ULift.{u} n) : ulPerm w c = ⟨w⁻¹ c.down⟩ :=
  rfl

omit [DecidableEq n] in
theorem characterLatticeEquiv_permutationAction_comp (w : Equiv.Perm n)
    (χ : characterLattice 𝔻) :
    splitTorus.characterLatticeEquiv k (ULift.{u} n) (permutationAction n k w χ) =
      splitTorus.characterLatticeEquiv k (ULift.{u} n) χ ∘ ulPerm w :=
  characterLatticeEquiv_permutationAction (k := k) w χ

/-- The Weyl action of a normalizing point is a permutation action. -/
theorem exists_permutationAction_eq_weylAction
    (m : normalizerPoints (diagonalTorus n (CommRingCat.of k))) :
    ∃ w : Equiv.Perm n, permutationAction n k w = weylAction _ m := by
  have hm : weylAction _ m ∈ weylImage (diagonalTorus n (CommRingCat.of k)) := ⟨m, rfl⟩
  exact weylImage_le_range_permutationAction n k hm

/-! ### The span of the relative roots -/

section RootSystem

/-- The rational coordinates restricted to the span of the relative roots. -/
def spanCoord :
    relativeRootSpan (diagonalTorus n (CommRingCat.of k)) →ₗ[ℚ] (ULift.{u} n → ℚ) :=
  (ratCoord k).toLinearMap ∘ₗ (relativeRootSpan _).subtype

theorem spanCoord_apply (x : relativeRootSpan (diagonalTorus n (CommRingCat.of k))) :
    spanCoord k x = ratCoord k x :=
  rfl

theorem spanCoord_injective : Function.Injective (spanCoord (n := n) k) :=
  (ratCoord k).injective.comp Subtype.val_injective

/-- The character `e_{p.1} - e_{p.2}` of the diagonal torus. -/
def rootChar (p : Index (ULift.{u} n)) : characterLattice 𝔻 :=
  (splitTorus.characterLatticeEquiv k (ULift.{u} n)).symm (rootVecInt p.1.1 p.1.2)

theorem characterLatticeEquiv_rootChar (p : Index (ULift.{u} n)) :
    splitTorus.characterLatticeEquiv k (ULift.{u} n) (rootChar k p) = rootVecInt p.1.1 p.1.2 :=
  AddEquiv.apply_symm_apply _ _

theorem relativeRoots_diagonalTorus_eq_range :
    relativeRoots (diagonalTorus n (CommRingCat.of k)) = Set.range (rootChar (n := n) k) := by
  rw [relativeRoots_diagonalTorus]
  ext χ
  constructor
  · rintro ⟨i, j, hij, hχ⟩
    refine ⟨⟨(⟨i⟩, ⟨j⟩), fun h => hij (congrArg ULift.down h)⟩, ?_⟩
    apply (splitTorus.characterLatticeEquiv k (ULift.{u} n)).injective
    rw [characterLatticeEquiv_rootChar, hχ]
    rfl
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.1.down, p.1.2.down, fun h => p.2 (ULift.ext _ _ h),
      characterLatticeEquiv_rootChar k p⟩

theorem rootChar_mem (p : Index (ULift.{u} n)) :
    rootChar k p ∈ relativeRoots (diagonalTorus n (CommRingCat.of k)) := by
  rw [relativeRoots_diagonalTorus_eq_range]
  exact ⟨p, rfl⟩

/-- The root `e_{p.1} - e_{p.2}` as an element of the span of the relative roots. -/
def rootElt (p : Index (ULift.{u} n)) : relativeRootSpan (diagonalTorus n (CommRingCat.of k)) :=
  ⟨toRat (rootChar k p), toRat_mem_ratSpan (rootChar_mem k p)⟩

theorem spanCoord_rootElt (p : Index (ULift.{u} n)) :
    spanCoord k (rootElt k p) = rootVec p.1.1 p.1.2 := by
  funext c
  rw [rootVec_eq_cast, spanCoord_apply]
  change ratCoord k (toRat (rootChar k p)) c = _
  rw [tensorEquivPi_toRat, characterLatticeEquiv_rootChar]

theorem range_rootElt :
    Set.range (rootElt (n := n) k) =
      ((↑) : relativeRootSpan (diagonalTorus n (CommRingCat.of k)) → _) ⁻¹'
        (toRat '' relativeRoots (diagonalTorus n (CommRingCat.of k))) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨rootChar k p, rootChar_mem k p, rfl⟩
  · rintro ⟨χ, hχ, hx⟩
    rw [relativeRoots_diagonalTorus_eq_range] at hχ
    obtain ⟨p, rfl⟩ := hχ
    exact ⟨p, Subtype.ext hx⟩

theorem span_range_rootElt : Submodule.span ℚ (Set.range (rootElt (n := n) k)) = ⊤ := by
  rw [range_rootElt]
  exact Submodule.span_span_coe_preimage

/-- The root system of type `A` on the span of the relative roots of the diagonal torus. -/
def rootSystem :
    RootPairing (Index (ULift.{u} n)) ℚ (relativeRootSpan (diagonalTorus n (CommRingCat.of k)))
      (Module.Dual ℚ (relativeRootSpan (diagonalTorus n (CommRingCat.of k)))) :=
  rootPairing (spanCoord_injective k) (spanCoord_rootElt k) (span_range_rootElt k)

theorem isCrystallographic_rootSystem : (rootSystem (n := n) k).IsCrystallographic := by
  refine ⟨fun p q => ⟨rootVecInt p.1.1 p.1.2 q.1.1 - rootVecInt p.1.1 p.1.2 q.1.2, ?_⟩⟩
  change _ = corootFun (spanCoord k) q (rootElt k p)
  rw [corootFun_r (spanCoord_rootElt k), rootVec_eq_cast, rootVec_eq_cast]
  push_cast
  rfl

theorem image_range_root_rootSystem :
    Subtype.val '' Set.range (rootSystem (n := n) k).root =
      toRat '' relativeRoots (diagonalTorus n (CommRingCat.of k)) := by
  rw [rootSystem, range_rootPairing_root, range_rootElt]
  refine Set.image_preimage_eq_of_subset ?_
  rintro _ ⟨χ, hχ, rfl⟩
  exact ⟨⟨toRat χ, toRat_mem_ratSpan hχ⟩, rfl⟩

/-! ### The relative Weyl group -/

theorem spanCoord_relativeWeylAction_mk {m : normalizerPoints (diagonalTorus n (CommRingCat.of k))}
    {w : Equiv.Perm n} (hw : permutationAction n k w = weylAction _ m)
    (x : relativeRootSpan (diagonalTorus n (CommRingCat.of k))) :
    spanCoord k (relativeWeylAction _ (QuotientGroup.mk m) x) = spanCoord k x ∘ ulPerm w := by
  rw [spanCoord_apply, coe_relativeWeylAction_mk_apply, ← hw,
    ratCoord_ratAut k _ _ (characterLatticeEquiv_permutationAction_comp k w)]
  rfl

theorem permSubgroup_eq_range_relativeWeylAction :
    permSubgroup (spanCoord (n := n) k) =
      (relativeWeylAction (diagonalTorus n (CommRingCat.of k))).range := by
  apply le_antisymm
  · rintro g ⟨σ, hσ⟩
    let w : Equiv.Perm n := (Equiv.permCongr Equiv.ulift σ)⁻¹
    have hw : ulPerm w = σ := by
      ext c
      simp [ulPerm_apply, w, Equiv.permCongr_apply]
    refine ⟨QuotientGroup.mk (permNormalizer k w), ?_⟩
    apply LinearEquiv.ext
    intro x
    apply spanCoord_injective k
    rw [spanCoord_relativeWeylAction_mk k (weylAction_permNormalizer k w).symm, hσ, hw]
  · rintro _ ⟨q, rfl⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨w, hw⟩ := exists_permutationAction_eq_weylAction k m
    exact ⟨ulPerm w, spanCoord_relativeWeylAction_mk k hw⟩

/-- A point whose Weyl action is trivial centralizes the diagonal torus. -/
theorem mem_centralizerPoints_of_weylAction_eq_one
    {m : normalizerPoints (diagonalTorus n (CommRingCat.of k))} (h : weylAction _ m = 1) :
    (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (groupScheme n (CommRingCat.of k)).X) ∈
      centralizerPoints (diagonalTorus n (CommRingCat.of k)) := by
  have hχ : ∀ χ : characterLattice 𝔻, (normalizingAut _ m).inv ≫ χ = χ := fun χ => by
    have h' : weylAction _ m χ = χ := by rw [h]; rfl
    rwa [weylAction_apply] at h'
  have hinv : (normalizingAut _ m).inv = 𝟙 𝔻 := by
    calc (normalizingAut _ m).inv
        = (normalizingAut _ m).inv ≫ ∑ c, splitTorus.proj _ (ULift.{u} n) c ≫
            splitTorus.single _ (ULift.{u} n) c := by
          rw [splitTorus.sum_proj_comp_single, Category.comp_id]
      _ = ∑ c, splitTorus.proj _ (ULift.{u} n) c ≫ splitTorus.single _ (ULift.{u} n) c := by
          rw [Preadditive.comp_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← Category.assoc, hχ]
      _ = 𝟙 𝔻 := splitTorus.sum_proj_comp_single _ _
  have hrefl : normalizingAut _ m = Iso.refl 𝔻 := by
    apply Iso.ext
    rw [← Category.comp_id (normalizingAut _ m).hom, ← hinv, Iso.hom_inv_id]
    rfl
  have hm := isNormalizingPoint_normalizingAut (diagonalTorus n (CommRingCat.of k)) m
  rw [hrefl] at hm
  exact hm

theorem relativeWeylAction_diagonalTorus_injective :
    Function.Injective (relativeWeylAction (diagonalTorus n (CommRingCat.of k))) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨w, hw⟩ := exists_permutationAction_eq_weylAction k m
  have hperm : ulPerm w = 1 := by
    apply perm_eq_one_of_rootVec_comp
    intro a b hab
    have h1 := spanCoord_relativeWeylAction_mk k hw (rootElt k ⟨(a, b), hab⟩)
    rw [hq] at h1
    change spanCoord k (rootElt k ⟨(a, b), hab⟩) = _ at h1
    rw [spanCoord_rootElt] at h1
    exact h1.symm
  have hw1 : w = 1 := by
    rw [← inv_eq_one]
    exact Equiv.ext fun c => congrArg ULift.down (Equiv.congr_fun hperm ⟨c⟩)
  have h1 : weylAction _ m = 1 := by rw [← hw, hw1, map_one]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact mem_centralizerPoints_of_weylAction_eq_one k h1

/-- The diagonal torus of `GL_n` has a relative root system: the root system of type `A`. -/
theorem hasRelativeRootSystem_diagonalTorus :
    HasRelativeRootSystem (diagonalTorus n (CommRingCat.of k)) := by
  refine ⟨Index (ULift.{u} n), inferInstance, rootSystem k, isRootSystem_rootPairing _ _ _,
    isCrystallographic_rootSystem k, rootPairing_toLinearMap _ _ _,
    image_range_root_rootSystem k, ?_, relativeWeylAction_diagonalTorus_injective k⟩
  rw [rootSystem, weylGroup_map_weightHom, permSubgroup_eq_range_relativeWeylAction]

end RootSystem

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme

open _root_.Langlands.GroupScheme.GeneralLinear in
/-- **The rational structure of `GL_n`.** -/
theorem generalLinearRationalStatement : GeneralLinearRationalStatement.{u} := by
  intro k _ n _ _
  exact ⟨isMaximalSplitTorus_diagonalTorus k, relativeRoots_diagonalTorus k,
    hasRelativeRootSystem_diagonalTorus k,
    fun ν hν => dynamicCentralizer_diagonalTorus_of_isGeneric k ν hν⟩

end Langlands.GroupScheme
