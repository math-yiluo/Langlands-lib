import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters
import Mathlib.LinearAlgebra.StdBasis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

open Langlands.GeneralLinear (BlockShape)

variable {N : ℕ} (B : BlockShape N) (R : CommRingCat.{u})

/-- Block-matrix coordinates on every test scheme of the actual block Levi. -/
def blockLeviPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) ≃*
      B.Levi Γ(T.left, ⊤) :=
  (Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_blockLevi (n := Fin N) (R := R) (blockShapeWeight B))) T).trans
    ((MulEquiv.subgroupCongr (blockLeviSubgroup_blockShapeWeight B Γ(T.left, ⊤))).trans
      (B.leviEquiv Γ(T.left, ⊤)).symm)

theorem blockLeviPointsEquiv_entry (T : Over (Spec R))
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X)
    (i : Fin B.length) (a b : Fin (B.size i)) :
    blockLeviPointsEquiv B R T x i a b =
      pointsEquiv (Fin N) R T
        (x ≫ (blockLeviHom (Fin N) R (blockShapeWeight B)).hom.hom)
        (B.index i a) (B.index i b) := by
  exact congrArg (fun g : GL (Fin N) Γ(T.left, ⊤) => g (B.index i a) (B.index i b))
    (pointsEquiv_cutHom _ x).symm

theorem blockLeviPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    blockLeviPointsEquiv B R T' (a ≫ x) =
      fun i => Matrix.GeneralLinearGroup.map a.left.appTop.hom (blockLeviPointsEquiv B R T x i) := by
  funext i
  apply Units.ext
  ext b c
  rw [blockLeviPointsEquiv_entry, Category.assoc, pointsEquiv_naturality]
  change a.left.appTop (pointsEquiv (Fin N) R T
      (x ≫ (blockLeviHom (Fin N) R (blockShapeWeight B)).hom.hom) (B.index i b) (B.index i c)) =
    a.left.appTop (blockLeviPointsEquiv B R T x i b c)
  rw [blockLeviPointsEquiv_entry]

def blockProjectionPoints (i : Fin B.length) (T : Over (Spec R)) :
    (T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) →*
      (T ⟶ (groupScheme (Fin (B.size i)) R).X) :=
  (pointsEquiv (Fin (B.size i)) R T).symm.toMonoidHom.comp
    ((Pi.evalMonoidHom (fun j => Langlands.GeneralLinear (B.size j) Γ(T.left, ⊤)) i).comp
      (blockLeviPointsEquiv B R T).toMonoidHom)

theorem blockProjectionPoints_naturality (i : Fin B.length)
    {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    blockProjectionPoints B R i T' (a ≫ x) = a ≫ blockProjectionPoints B R i T x := by
  apply (pointsEquiv (Fin (B.size i)) R T').injective
  simp only [blockProjectionPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Pi.evalMonoidHom_apply, pointsEquiv_naturality,
    blockLeviPointsEquiv_naturality]

/-- The actual scheme projection to one invertible diagonal block. -/
def blockProjectionHom (i : Fin B.length) :
    blockLeviScheme (Fin N) R (blockShapeWeight B) ⟶ groupScheme (Fin (B.size i)) R :=
  homOfPoints (blockProjectionPoints B R i) (blockProjectionPoints_naturality B R i)

theorem pointsEquiv_blockProjectionHom (i : Fin B.length) (T : Over (Spec R))
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    pointsEquiv (Fin (B.size i)) R T (x ≫ (blockProjectionHom B R i).hom.hom) =
      blockLeviPointsEquiv B R T x i := by
  rw [blockProjectionHom, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

def blockInclusionPoints (i : Fin B.length) (T : Over (Spec R)) :
    (T ⟶ (groupScheme (Fin (B.size i)) R).X) →*
      (T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :=
  (blockLeviPointsEquiv B R T).symm.toMonoidHom.comp
    ((MonoidHom.mulSingle
      (fun j => Langlands.GeneralLinear (B.size j) Γ(T.left, ⊤)) i).comp
        (pointsEquiv (Fin (B.size i)) R T).toMonoidHom)

theorem blockInclusionPoints_naturality (i : Fin B.length)
    {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme (Fin (B.size i)) R).X) :
    blockInclusionPoints B R i T' (a ≫ x) = a ≫ blockInclusionPoints B R i T x := by
  apply (blockLeviPointsEquiv B R T').injective
  simp only [blockInclusionPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.mulSingle_apply, pointsEquiv_naturality,
    blockLeviPointsEquiv_naturality]
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.mulSingle_eq_of_ne hji]

/-- Insert one invertible block, with identity matrices on the other blocks. -/
def blockInclusionHom (i : Fin B.length) :
    groupScheme (Fin (B.size i)) R ⟶ blockLeviScheme (Fin N) R (blockShapeWeight B) :=
  homOfPoints (blockInclusionPoints B R i) (blockInclusionPoints_naturality B R i)

theorem blockLeviPointsEquiv_blockInclusionHom (i : Fin B.length) (T : Over (Spec R))
    (x : T ⟶ (groupScheme (Fin (B.size i)) R).X) :
    blockLeviPointsEquiv B R T (x ≫ (blockInclusionHom B R i).hom.hom) =
      Pi.mulSingle i (pointsEquiv (Fin (B.size i)) R T x) := by
  rw [blockInclusionHom, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

/-- The scheme projection pulls the determinant character back to the block determinant. -/
theorem blockDeterminantCharacter_eq_restrict (i : Fin B.length) :
    blockDeterminantCharacter R B i =
      characterRestrict (blockProjectionHom B R i) (determinantCharacter (Fin (B.size i)) R) := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [characterEval_characterRestrict, characterEval_determinantCharacter,
    pointsEquiv_blockProjectionHom, characterEval_apply, comp_blockDeterminantCharacter,
    pointsEquiv_blockDetPoints]
  rfl

private theorem ordered_prod_mulSingle {I : Type*} [Fintype I] [DecidableEq I]
    {M : I → Type*} [∀ i, Monoid (M i)] (d : ∀ i, M i) :
    ((Finset.univ.toList.map (fun i => Pi.mulSingle i (d i))).prod) = d := by
  funext j
  change Pi.evalMonoidHom M j ((Finset.univ.toList.map (fun i => Pi.mulSingle i (d i))).prod) = _
  rw [map_list_prod, List.map_map, List.prod_map_eq_pow_single j]
  · have hj : Finset.univ.toList.count j = 1 :=
      List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)
    rw [hj, pow_one]
    exact Pi.mulSingle_eq_same j (d j)
  · intro i hij _
    exact Pi.mulSingle_eq_of_ne hij.symm _

/-- The point is the ordered product of its individual diagonal-block points. -/
theorem blockLevi_point_decomposition (T : Over (Spec R))
    (x : T ⟶ (blockLeviScheme (Fin N) R (blockShapeWeight B)).X) :
    x = (Finset.univ.toList.map (fun i =>
      (pointsEquiv (Fin (B.size i)) R T).symm (blockLeviPointsEquiv B R T x i) ≫
        (blockInclusionHom B R i).hom.hom)).prod := by
  apply (blockLeviPointsEquiv B R T).injective
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, blockLeviPointsEquiv_blockInclusionHom,
    MulEquiv.apply_symm_apply, ordered_prod_mulSingle]

private theorem eval_finset_sum {S : Scheme.{u}} {G : GroupScheme S}
    {I : Type*} (s : Finset I) (f : I → rationalCharacters G) (T : Over S) (x : T ⟶ G.X) :
    characterEval (∑ i ∈ s, f i) T x = ∏ i ∈ s, characterEval (f i) T x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [characterEval_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, characterEval_add, ih]

theorem character_block_decomposition
    (χ : rationalCharacters (blockLeviScheme (Fin N) R (blockShapeWeight B))) :
    χ = ∑ i, characterRestrict (blockProjectionHom B R i)
      (characterRestrict (blockInclusionHom B R i) χ) := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [eval_finset_sum]
  simp only [characterEval_characterRestrict]
  have he := congrArg (characterEval χ T) (blockLevi_point_decomposition B R T x)
  rw [map_list_prod, List.map_map] at he
  rw [he, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro i _
  have hp : (pointsEquiv (Fin (B.size i)) R T).symm (blockLeviPointsEquiv B R T x i) =
      x ≫ (blockProjectionHom B R i).hom.hom := by
    apply (pointsEquiv (Fin (B.size i)) R T).injective
    rw [MulEquiv.apply_symm_apply, pointsEquiv_blockProjectionHom]
  exact congrArg (fun y => characterEval χ T (y ≫ (blockInclusionHom B R i).hom.hom)) hp

theorem characterRestrict_blockInclusion_blockDet_same (i : Fin B.length) :
    characterRestrict (blockInclusionHom B R i) (blockDeterminantCharacter R B i) =
      determinantCharacter (Fin (B.size i)) R := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [blockDeterminantCharacter_eq_restrict]
  simp only [characterEval_characterRestrict, characterEval_determinantCharacter,
    pointsEquiv_blockProjectionHom, blockLeviPointsEquiv_blockInclusionHom,
    Pi.mulSingle_eq_same]

theorem characterRestrict_blockInclusion_blockDet_ne (i j : Fin B.length) (hij : i ≠ j) :
    characterRestrict (blockInclusionHom B R i) (blockDeterminantCharacter R B j) = 0 := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [blockDeterminantCharacter_eq_restrict]
  simp only [characterEval_characterRestrict, characterEval_determinantCharacter,
    pointsEquiv_blockProjectionHom, blockLeviPointsEquiv_blockInclusionHom,
    Pi.mulSingle_eq_of_ne hij.symm, map_one, characterEval_zero]

/-- The combination of the block determinants with prescribed integer exponents. -/
def blockDetCombination :
    (Fin B.length → ℤ) →ₗ[ℤ]
      rationalCharacters (blockLeviScheme (Fin N) R (blockShapeWeight B)) where
  toFun m := ∑ i, m i • blockDeterminantCharacter R B i
  map_add' m m' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c m := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply, smul_eq_mul]

theorem blockDetCombination_apply (m : Fin B.length → ℤ) :
    blockDetCombination B R m = ∑ i, m i • blockDeterminantCharacter R B i := rfl

theorem blockDetCombination_surjective [IsDomain R] :
    Function.Surjective (blockDetCombination B R) := by
  intro χ
  choose m hm using fun i =>
    rationalCharacter_eq_zsmul_determinant (characterRestrict (blockInclusionHom B R i) χ)
  refine ⟨m, ?_⟩
  rw [blockDetCombination_apply, character_block_decomposition B R χ]
  apply Finset.sum_congr rfl
  intro i _
  rw [hm, map_zsmul, ← blockDeterminantCharacter_eq_restrict]

/-- Extract an integer coefficient by restricting to one block and then to its
first coordinate cocharacter. -/
def blockCharacterCoefficient [IsDomain R] (i : Fin B.length) :
    rationalCharacters (blockLeviScheme (Fin N) R (blockShapeWeight B)) →+ ℤ :=
  (gmEndEquiv R).toAddMonoidHom.comp
    ((characterRestrict (coordinateDiagonalHom (Fin (B.size i)) R ⟨0, B.positive i⟩)).comp
      (characterRestrict (blockInclusionHom B R i)))

theorem blockCharacterCoefficient_blockDet [IsDomain R] (i j : Fin B.length) :
    blockCharacterCoefficient B R i (blockDeterminantCharacter R B j) =
      if i = j then 1 else 0 := by
  change gmEndEquiv R (characterRestrict
    (coordinateDiagonalHom (Fin (B.size i)) R ⟨0, B.positive i⟩)
    (characterRestrict (blockInclusionHom B R i) (blockDeterminantCharacter R B j))) = _
  by_cases hij : i = j
  · subst j
    rw [characterRestrict_blockInclusion_blockDet_same, characterRestrict_coordinate_determinant,
      ite_eq_left rfl]
    exact gmEndEquiv_id R
  · rw [characterRestrict_blockInclusion_blockDet_ne B R i j hij, map_zero, map_zero, ite_eq_right hij]

theorem blockCharacterCoefficient_combination [IsDomain R]
    (i : Fin B.length) (m : Fin B.length → ℤ) :
    blockCharacterCoefficient B R i (blockDetCombination B R m) = m i := by
  rw [blockDetCombination_apply, map_sum]
  simp only [map_zsmul, blockCharacterCoefficient_blockDet, smul_eq_mul]
  simp

theorem blockDetCombination_injective [IsDomain R] :
    Function.Injective (blockDetCombination B R) := by
  intro m m' h
  funext i
  have he := congrArg (blockCharacterCoefficient B R i) h
  simpa only [blockCharacterCoefficient_combination] using he

/-- The basis of actual rational characters of the block Levi given by its block determinants. -/
def blockDeterminantBasis [IsDomain R] :
    Module.Basis (Fin B.length) ℤ
      (rationalCharacters (blockLeviScheme (Fin N) R (blockShapeWeight B))) :=
  (Pi.basisFun ℤ (Fin B.length)).map
    (LinearEquiv.ofBijective (blockDetCombination B R)
      ⟨blockDetCombination_injective B R, blockDetCombination_surjective B R⟩)

theorem blockDeterminantBasis_apply [IsDomain R] (i : Fin B.length) :
    blockDeterminantBasis B R i = blockDeterminantCharacter R B i := by
  change blockDetCombination B R ((Pi.basisFun ℤ (Fin B.length)) i) = _
  simp [blockDetCombination_apply, Pi.basisFun_apply, Pi.single_apply]

end Langlands.GroupScheme.GeneralLinear
