import Langlands.Global.AdelicCentralPositiveHeightStatement
import Langlands.Global.AdelicPositiveDecompositionProof
import Langlands.Global.AdelicRepresentationHeightDominationProof
import Langlands.Global.AdelicRationalHeightReduction
import Langlands.Global.PositiveRealTorusLog
import Langlands.GroupScheme.Rational.CharacterLine
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndexProof
import Langlands.Global.AdelicCharacterLog
import Langlands.Global.AdelicPositiveRootCharacterRelation

/-! # Central archimedean factors of adelic points with polynomially bounded height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Opposite
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-! ### Character lines -/

/-- The adelic matrix of the line representation of a character is the `1 × 1` matrix of its
idele value. -/
theorem adelicMatrix_lineRepresentation (χ : rationalCharacters G) (g : AdelicGroupPoints F G) :
    adelicMatrix F G χ.lineRepresentation g =
      GeneralLinear.diagonalUnits (AdeleRing (𝓞 F) F) (fun _ : Fin 1 => (1 : ℤ))
        (character F G χ.toMul g) := by
  change GeneralLinear.affinePointsEquiv (Fin 1) (CommRingCat.of F)
      (CommAlgCat.of F (AdeleRing (𝓞 F) F))
      (g ≫ (χ.toMul ≫ GeneralLinear.scalarTorus (Fin 1) (CommRingCat.of F)).hom.hom) = _
  rw [GeneralLinear.scalarTorus_eq_diagonalCocharacter, Grp.comp_hom_hom, ← Category.assoc,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]
  rfl

/-- The normalized idele norm of a character value is at most the full adelic height of its
line representation. -/
theorem characterNorm_le_adelicHeight_lineRepresentation (χ : rationalCharacters G)
    (g : AdelicGroupPoints F G) :
    ((characterNorm F G χ.toMul g : ℝ≥0) : ℝ) ≤
      adelicHeight F G χ.lineRepresentation g := by
  set x : Ideles F := character F G χ.toMul g with hx
  set D := adelicMatrix F G χ.lineRepresentation g with hD
  have hD0 : D 0 0 = x.val := by
    rw [hD, adelicMatrix_lineRepresentation]
    simp [GeneralLinear.coe_diagonalUnits, x]
  have hinf (v : InfinitePlace F) :
      ‖x.val.1 v‖ ≤ (1 : ℝ) * AdelicMatrixHeight.infiniteLocal F 1 D v := by
    rw [one_mul]
    have h := MatrixInverseHeight.entry_le_localMaximum (infiniteProjection F v) D 0 0
    rw [hD0] at h
    exact h
  have hfin (v : FinitePlace F) :
      ‖x.val.2 v‖ ≤ AdelicMatrixHeight.finiteLocal F 1 D v := by
    have h := MatrixInverseHeight.entry_le_localMaximum (finiteProjection F v) D 0 0
    rw [hD0] at h
    exact h
  have hsupp : (fun v : FinitePlace F => ‖x.val.2 v‖).HasFiniteMulSupport :=
    NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (ideleProductEquiv F x).2
  change ((IdeleAbsoluteValue.full F x : ℝ≥0) : ℝ) ≤ AdelicMatrixHeight.height F 1 D
  rw [IdeleAbsoluteValue.coe_full]
  unfold AdelicMatrixHeight.height
  push_cast
  apply mul_le_mul
  · apply Finset.prod_le_prod₀
    · intro v _
      exact pow_nonneg (norm_nonneg _) _
    · intro v _
      exact pow_le_pow_left₀ (norm_nonneg _) (hinf v) _
  · exact finprod_le_finprod₀ hsupp (fun v => norm_nonneg _)
      (AdelicMatrixHeight.hasFiniteMulSupport_finiteLocal F 1 one_pos D) hfin
  · exact finprod_nonneg fun v => norm_nonneg _
  · exact Finset.prod_nonneg fun v _ =>
      pow_nonneg (mul_nonneg zero_le_one (MatrixInverseHeight.localMaximum_nonneg _ _)) _

variable {G} in
/-- A closed matrix embedding bounds every character norm and its inverse polynomially. -/
theorem exists_characterNorm_le {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hrho : IsClosedSubgroup rho) (χ : rationalCharacters G) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ, ∀ g : AdelicGroupPoints F G,
      ((characterNorm F G χ.toMul g : ℝ≥0) : ℝ) ≤ C * adelicHeight F G rho g ^ e ∧
        (((characterNorm F G χ.toMul g)⁻¹ : ℝ≥0ˣ) : ℝ≥0) ≤ C * adelicHeight F G rho g ^ e := by
  obtain ⟨C, hC, e, he⟩ := closedImmersionAdelicHeightDomination F G N 1 rho
    χ.lineRepresentation hN one_pos hrho
  refine ⟨C, hC, e, fun g => ⟨?_, ?_⟩⟩
  · exact (characterNorm_le_adelicHeight_lineRepresentation F G χ g).trans (he g)
  · rw [← map_inv]
    calc
      _ ≤ adelicHeight F G χ.lineRepresentation g⁻¹ :=
        characterNorm_le_adelicHeight_lineRepresentation F G χ g⁻¹
      _ ≤ C * adelicHeight F G rho g⁻¹ ^ e := he g⁻¹
      _ = C * adelicHeight F G rho g ^ e := by rw [adelicHeight_inv]

/-! ### Positive points of a coordinate split torus -/

/-- The product over the coordinates of the larger of a positive real and its inverse. -/
def positiveSize {I : Type*} [Fintype I] (x : I → ℝ≥0ˣ) : ℝ≥0 :=
  ∏ j, max ((x j : ℝ≥0ˣ) : ℝ≥0) (((x j)⁻¹ : ℝ≥0ˣ) : ℝ≥0)

theorem one_le_max_inv (y : ℝ≥0ˣ) : 1 ≤ max (y : ℝ≥0) ((y⁻¹ : ℝ≥0ˣ) : ℝ≥0) := by
  rcases le_total 1 (y : ℝ≥0) with h | h
  · exact le_max_of_le_left h
  · apply le_max_of_le_right
    rw [Units.val_inv_eq_inv_val]
    exact (one_le_inv₀ (pos_iff_ne_zero.mpr y.ne_zero)).mpr h

theorem one_le_positiveSize {I : Type*} [Fintype I] (x : I → ℝ≥0ˣ) : 1 ≤ positiveSize x :=
  Finset.one_le_prod fun j _ => one_le_max_inv (x j)

theorem le_positiveSize {I : Type*} [Fintype I] (x : I → ℝ≥0ˣ) (j : I) :
    max ((x j : ℝ≥0ˣ) : ℝ≥0) (((x j)⁻¹ : ℝ≥0ˣ) : ℝ≥0) ≤ positiveSize x :=
  Finset.single_le_prod (fun k _ => one_le_max_inv (x k)) (Finset.mem_univ j)

theorem positiveSize_inv {I : Type*} [Fintype I] (x : I → ℝ≥0ˣ) :
    positiveSize x⁻¹ = positiveSize x := by
  unfold positiveSize
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Pi.inv_apply, inv_inv, max_comm]

/-- If a power of a positive real and of its inverse are bounded, so is the power of the larger
of the two. -/
theorem max_inv_pow_le (y : ℝ≥0ˣ) (n : ℕ) (B : ℝ) (h1 : (((y ^ n : ℝ≥0ˣ) : ℝ≥0) : ℝ) ≤ B)
    (h2 : ((((y ^ n)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) ≤ B) :
    ((max (y : ℝ≥0) ((y⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ≥0) : ℝ) ^ n ≤ B := by
  rcases max_choice (y : ℝ≥0) ((y⁻¹ : ℝ≥0ˣ) : ℝ≥0) with h | h <;> rw [h]
  · simpa only [Units.val_pow_eq_pow_val, NNReal.coe_pow] using h1
  · simpa only [← inv_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow] using h2

theorem norm_diagonal_infinite_le {r : ℕ} (y : ULift.{u} (Fin r) → ℝ≥0ˣ) (v : InfinitePlace F) :
    ‖fun a b : Fin r => infiniteProjection F v
      ((Matrix.diagonal fun k : Fin r =>
        ((PositiveRealIdeles.full F (y ⟨k⟩) : Ideles F) : Adeles F)) a b)‖ ≤
      ((positiveSize y : ℝ≥0) : ℝ) := by
  have hP : (0 : ℝ) ≤ ((positiveSize y : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  refine (pi_norm_le_iff_of_nonneg hP).mpr fun a => (pi_norm_le_iff_of_nonneg hP).mpr fun b => ?_
  rw [Matrix.diagonal_apply]
  split_ifs with hab
  · subst hab
    change ‖(PositiveRealIdeles.full F (y ⟨a⟩)).val.1 v‖ ≤ _
    rw [PositiveRealIdeles.norm_full_infinite_value]
    exact_mod_cast (le_max_left _ _).trans (le_positiveSize y ⟨a⟩)
  · rw [map_zero, norm_zero]
    exact hP

theorem norm_diagonal_finite_le {r : ℕ} (y : ULift.{u} (Fin r) → ℝ≥0ˣ) (v : FinitePlace F) :
    ‖fun a b : Fin r => finiteProjection F v
      ((Matrix.diagonal fun k : Fin r =>
        ((PositiveRealIdeles.full F (y ⟨k⟩) : Ideles F) : Adeles F)) a b)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun a =>
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun b => ?_
  rw [Matrix.diagonal_apply]
  split_ifs with hab
  · change ‖(PositiveRealIdeles.full F (y ⟨a⟩)).val.2 v‖ ≤ 1
    rw [PositiveRealIdeles.full_finite_value, norm_one]
  · rw [map_zero, norm_zero]
    exact zero_le_one

/-- The adelic matrix of a representation pulled back along a homomorphism. -/
theorem adelicMatrix_map {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (x : AdelicGroupPoints F H) :
    adelicMatrix F G rho (AdelicGroupPoints.map F H G f x) = adelicMatrix F H (f ≫ rho) x := by
  change GeneralLinearGroupPoints.adelicHomeomorph F N ((x ≫ f.hom.hom) ≫ rho.hom.hom) =
    GeneralLinearGroupPoints.adelicHomeomorph F N (x ≫ (f ≫ rho).hom.hom)
  rw [Grp.comp_hom_hom, Category.assoc]

variable {F} in
/-- In the diagonal representation of a coordinate splitting, a positive point is the diagonal
matrix of its positive scalar ideles. -/
theorem adelicMatrix_diagonalTorus_full {r : ℕ} (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin r)))
    (x : ULift.{u} (Fin r) → ℝ≥0ˣ) :
    ((adelicMatrix F T.toGrp (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F))
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x) :
          Matrix (Fin r) (Fin r) (Adeles F))) =
      Matrix.diagonal fun k => ((PositiveRealIdeles.full F (x ⟨k⟩) : Ideles F) : Adeles F) := by
  change ((GeneralLinear.affinePointsEquiv (Fin r) (CommRingCat.of F)
      (CommAlgCat.of F (AdeleRing (𝓞 F) F))
      (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x ≫
        (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F)).hom.hom) :
        Matrix (Fin r) (Fin r) (Adeles F))) = _
  rw [Grp.comp_hom_hom, ← Category.assoc, GeneralLinear.affinePointsEquiv_comp_diagonalTorus,
    GeneralLinear.coe_diagonalTorusUnits]
  have h : GeneralLinear.torusCoords (R := CommRingCat.of F) (A := Adeles F)
      (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x ≫ e.hom.hom.hom) =
      PositiveRealTorus.coordinates F (ULift.{u} (Fin r)) T e (Adeles F)
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x) := rfl
  rw [h, PositiveRealTorus.coordinates_full]

/-- The diagonal height of a positive point is bounded by a power of its coordinate size. -/
theorem adelicHeight_diagonalTorus_full_le {r : ℕ} (hr : 0 < r)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin r)))
    (x : ULift.{u} (Fin r) → ℝ≥0ˣ) :
    adelicHeight F T.toGrp (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F))
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x) ≤
      ((r : ℝ) * ((positiveSize x : ℝ≥0) : ℝ)) ^ Module.finrank ℚ F := by
  have hDm := adelicMatrix_diagonalTorus_full T e x
  have hDinv : (((adelicMatrix F T.toGrp
      (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F))
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x))⁻¹ : AdelicGL F r) :
          Matrix (Fin r) (Fin r) (Adeles F)) =
      Matrix.diagonal fun k => ((PositiveRealIdeles.full F (x⁻¹ ⟨k⟩) : Ideles F) : Adeles F) := by
    rw [← map_inv, ← map_inv]
    exact adelicMatrix_diagonalTorus_full T e x⁻¹
  change AdelicMatrixHeight.height F r (adelicMatrix F T.toGrp
      (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F))
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x)) ≤ _
  set D := adelicMatrix F T.toGrp
      (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F))
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x) with hD
  have hinf (v : InfinitePlace F) :
      AdelicMatrixHeight.infiniteLocal F r D v ≤ ((positiveSize x : ℝ≥0) : ℝ) := by
    unfold AdelicMatrixHeight.infiniteLocal MatrixInverseHeight.localMaximum
    apply max_le
    · rw [hDm]
      exact norm_diagonal_infinite_le F x v
    · rw [hDinv, ← positiveSize_inv x]
      exact norm_diagonal_infinite_le F x⁻¹ v
  have hfin (v : FinitePlace F) : AdelicMatrixHeight.finiteLocal F r D v = 1 := by
    apply le_antisymm _ (AdelicMatrixHeight.one_le_finiteLocal F r hr D v)
    unfold AdelicMatrixHeight.finiteLocal MatrixInverseHeight.localMaximum
    apply max_le
    · rw [hDm]
      exact norm_diagonal_finite_le F x v
    · rw [hDinv]
      exact norm_diagonal_finite_le F x⁻¹ v
  unfold AdelicMatrixHeight.height
  rw [finprod_congr hfin, finprod_one, mul_one]
  calc
    _ ≤ ∏ v : InfinitePlace F, ((r : ℝ) * ((positiveSize x : ℝ≥0) : ℝ)) ^ v.mult := by
      apply Finset.prod_le_prod₀
      · intro v _
        exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (MatrixInverseHeight.localMaximum_nonneg _ _)) _
      · intro v _
        exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _)
          (MatrixInverseHeight.localMaximum_nonneg _ _))
          (mul_le_mul_of_nonneg_left (hinf v) (Nat.cast_nonneg _)) _
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, NumberField.InfinitePlace.sum_mult_eq]

variable {G} in
/-- The height of the image of a positive torus point is polynomial in its coordinate size. -/
theorem exists_adelicHeight_map_full_le {N r : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin r))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x : ULift.{u} (Fin r) → ℝ≥0ˣ,
      adelicHeight F G rho (AdelicGroupPoints.map F T.toGrp G i
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x)) ≤
          C * ((positiveSize x : ℝ≥0) : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨adelicHeight F G rho 1, zero_le_one.trans (one_le_adelicHeight F G rho hN 1), 0,
      fun x => ?_⟩
    have hx : x = 1 := funext fun j => j.down.elim0
    rw [hx, map_one, map_one, pow_zero, mul_one]
  · obtain ⟨C, hC, k, hk⟩ := closedImmersionAdelicHeightDomination F T.toGrp r N
      (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F)) (i ≫ rho) hr hN
      ((IsClosedSubgroup.of_iso e).comp (GeneralLinear.isClosedSubgroup_diagonalTorus _ _))
    refine ⟨C * (r : ℝ) ^ (Module.finrank ℚ F * k),
      mul_nonneg (zero_le_one.trans hC) (pow_nonneg (Nat.cast_nonneg _) _),
      Module.finrank ℚ F * k, fun x => ?_⟩
    have hmap : adelicHeight F G rho (AdelicGroupPoints.map F T.toGrp G i
        (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x)) =
        adelicHeight F T.toGrp (i ≫ rho) (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x) := by
      unfold adelicHeight
      rw [adelicMatrix_map]
    rw [hmap]
    calc
      _ ≤ C * adelicHeight F T.toGrp
            (e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F))
            (PositiveRealTorus.full F (ULift.{u} (Fin r)) T e x) ^ k := hk _
      _ ≤ C * (((r : ℝ) * ((positiveSize x : ℝ≥0) : ℝ)) ^ Module.finrank ℚ F) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀
            (zero_le_one.trans (one_le_adelicHeight F _ _ hr _))
            (adelicHeight_diagonalTorus_full_le F hr T e x) k) (zero_le_one.trans hC)
      _ = _ := by ring

/-! ### Characters restricting to multiples of the coordinates -/

variable {G} in
/-- Finite index of the character restriction gives, for every coordinate, an ambient character
whose norm on positive points is a fixed power of that coordinate. -/
theorem exists_characterNorm_full (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) {I : Type u} [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    [(characterRestrict i).range.FiniteIndex] :
    ∃ m : ℕ, 0 < m ∧ ∀ j : I, ∃ χ : rationalCharacters G, ∀ x : I → ℝ≥0ˣ,
      characterNorm F G χ.toMul
          (AdelicGroupPoints.map F T.toGrp G i (PositiveRealTorus.full F I T e x)) =
        x j ^ (m * Module.finrank ℚ F) := by
  refine ⟨(characterRestrict i).range.index,
    Nat.pos_of_ne_zero AddSubgroup.FiniteIndex.index_ne_zero, fun j => ?_⟩
  obtain ⟨χ, hχ⟩ := (characterRestrict i).range.nsmul_index_mem
    (PositiveRealTorus.coordinateCharacter F I T e j)
  refine ⟨χ, fun x => ?_⟩
  rw [← characterNorm_comp]
  change characterNorm F T.toGrp (characterRestrict i χ).toMul _ = _
  rw [hχ, characterNorm_nsmul,
    PositiveRealTorus.characterNorm_eq_absoluteValue_characterValue,
    PositiveRealTorus.characterValue_coordinateCharacter, PositiveRealTorus.coordinates_full,
    PositiveRealIdeles.absoluteValue_full, ← pow_mul, mul_comm]

/-! ### The central factor -/

variable {G} in
/-- The actual positive image of a split torus has trivial finite component. -/
theorem finite_positivePointMap [IsAffine G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (a : PositiveRealTorus.intrinsicSubgroup F T) :
    AdelicGroupPoints.finite F G (PositiveRealTorus.positivePointMap F G T i a) = 1 := by
  rw [← map_one (AdelicGroupPoints.finite F G)]
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  funext b
  dsimp only
  rw [AdelicSiegelFactors.evaluation_finite, AdelicSiegelFactors.evaluation_finite]
  refine IsDedekindDomain.FiniteAdeleRing.ext _ fun v => ?_
  have h1 := atFinitePlace_evaluation F G v (PositiveRealTorus.positivePointMap F G T i a) b
  have h2 := atFinitePlace_evaluation F G v 1 b
  have h3 : atFinitePlace F G v (PositiveRealTorus.positivePointMap F G T i a) = 1 := by
    change atPlace F G (.inr v) (AdelicGroupPoints.map F T.toGrp G i a.val) = 1
    rw [atPlace_map]
    change GroupScheme.affinePointsTarget T.toGrp i (placeCompletion F (.inr v))
      (atFinitePlace F T.toGrp v a.val) = 1
    rw [PositiveRealTorus.atFinitePlace_intrinsic F T hT, map_one]
  rw [h3] at h1
  rw [map_one] at h2
  exact h1.symm.trans h2

end Langlands.Global.RepresentationGrowth

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

/-- Every adelic point of a connected reductive group is a central positive point with trivial
finite component times a norm-one point, and the height of the central factor is polynomially
bounded by the height of the point. -/
theorem centralNormOneHeightFactorStatement : CentralNormOneHeightFactorStatement.{u} := by
  intro F _ _ G _ N rho hG hrho hN
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨T, i, hi, E, hE⟩ := PositiveRealTorus.adelicPositiveDecompositionStatement F G hG
  have hT : IsSplitTorus T.toGrp := hi.1.1.1
  have : (characterRestrict i).range.FiniteIndex :=
    characterRestrictionFiniteIndexStatement F G hG T i hi
  obtain ⟨I, _, ⟨e₀⟩⟩ := hT
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨r, ⟨σ⟩⟩ : ∃ r : ℕ, Nonempty (ULift.{u} (Fin r) ≃ I) :=
    ⟨Fintype.card I, ⟨Equiv.ulift.trans (Fintype.equivFin I).symm⟩⟩
  let e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin r)) :=
    e₀ ≪≫ LocalSplitCell.exponentEquivGroupIso _ (LinearEquiv.funCongrLeft ℤ ℤ σ)
  obtain ⟨Cb, hCb, kb, hb⟩ := exists_adelicHeight_map_full_le F rho hN T i e
  obtain ⟨m, hm, hχ⟩ := exists_characterNorm_full F T i e
  choose χ hχ using hχ
  choose C hC ea hea using fun j => exists_characterNorm_le F rho hN hrho (χ j)
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  let Cmax : ℝ := ∑ j, C j
  let emax : ℕ := ∑ j, ea j
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun j _ => zero_le_one.trans (hC j)
  refine ⟨Cb * Cmax ^ (r * kb), emax * r * kb, fun g => ?_⟩
  set p := E.symm g with hp
  have hg : g = PositiveRealTorus.positivePointMap F G T i p.1 * p.2 := by
    rw [← hE, hp, ContinuousMulEquiv.apply_symm_apply]
  have ha : p.1.val ∈ PositiveRealTorus.subgroup F _ T e := by
    rw [PositiveRealTorus.subgroup_eq_intrinsicSubgroup]
    exact p.1.property
  obtain ⟨x, hx⟩ := ha
  refine ⟨PositiveRealTorus.positivePointMap F G T i p.1,
    PositiveRealTorus.positivePointMap_commute F G T i hi.1.2 p.1,
    finite_positivePointMap F T i hi.1.1.1 p.1, ?_, ?_⟩
  · rw [hg, inv_mul_cancel_left]
    exact p.2.property
  set H := adelicHeight F G rho g with hH
  have hH1 : 1 ≤ H := one_le_adelicHeight F G rho hN g
  have hnorm (j : ULift.{u} (Fin r)) :
      characterNorm F G (χ j).toMul g = x j ^ (m * Module.finrank ℚ F) := by
    rw [hg, map_mul, (mem_normOneSubgroup F G _).mp p.2.property, mul_one,
      PositiveRealTorus.positivePointMap_apply, ← hx, hχ]
  have hj (j : ULift.{u} (Fin r)) :
      ((max ((x j : ℝ≥0ˣ) : ℝ≥0) (((x j)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ≥0) : ℝ) ^ (m * Module.finrank ℚ F) ≤
        Cmax * H ^ emax := by
    have hb1 := (hea j g).1
    have hb2 := (hea j g).2
    rw [hnorm j] at hb1 hb2
    have hCj : C j ≤ Cmax :=
      Finset.single_le_sum (fun k _ => zero_le_one.trans (hC k)) (Finset.mem_univ j)
    have hej : H ^ ea j ≤ H ^ emax :=
      pow_le_pow_right₀ hH1 (Finset.single_le_sum (fun k _ => Nat.zero_le (ea k))
        (Finset.mem_univ j))
    have hbound : C j * H ^ ea j ≤ Cmax * H ^ emax :=
      mul_le_mul hCj hej (pow_nonneg (zero_le_one.trans hH1) _) hCmax0
    exact max_inv_pow_le (x j) (m * Module.finrank ℚ F) _ (hb1.trans hbound) (hb2.trans hbound)
  have hP1 : (1 : ℝ) ≤ ((positiveSize x : ℝ≥0) : ℝ) := by
    exact_mod_cast one_le_positiveSize x
  have hP0 : (0 : ℝ) ≤ ((positiveSize x : ℝ≥0) : ℝ) := zero_le_one.trans hP1
  have hP : ((positiveSize x : ℝ≥0) : ℝ) ^ (m * Module.finrank ℚ F) ≤ (Cmax * H ^ emax) ^ r := by
    rw [positiveSize, NNReal.coe_prod, ← Finset.prod_pow]
    calc
      _ ≤ ∏ _j : ULift.{u} (Fin r), Cmax * H ^ emax :=
        Finset.prod_le_prod₀ (fun j _ => pow_nonneg (NNReal.coe_nonneg _) _) fun j _ => hj j
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_ulift, Fintype.card_fin]
  have hkb : kb ≤ m * Module.finrank ℚ F * kb := Nat.le_mul_of_pos_left kb (Nat.mul_pos hm hd)
  calc
    adelicHeight F G rho (PositiveRealTorus.positivePointMap F G T i p.1)
        ≤ Cb * ((positiveSize x : ℝ≥0) : ℝ) ^ kb := by
      rw [PositiveRealTorus.positivePointMap_apply, ← hx]
      exact hb x
    _ ≤ Cb * (((positiveSize x : ℝ≥0) : ℝ) ^ (m * Module.finrank ℚ F)) ^ kb := by
      rw [← pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP1 hkb) hCb
    _ ≤ Cb * ((Cmax * H ^ emax) ^ r) ^ kb :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hP0 _) hP kb) hCb
    _ = Cb * Cmax ^ (r * kb) * H ^ (emax * r * kb) := by ring

end Langlands.Global.RepresentationGrowth
