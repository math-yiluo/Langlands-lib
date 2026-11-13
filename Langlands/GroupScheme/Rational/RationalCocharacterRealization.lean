import Langlands.GroupScheme.Rational.RelativeReflectionPairing
import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.LinearAlgebra.FiniteHyperplaneChamberGallery

/-! # Integral realizations of rational cocharacter directions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalCocharacter

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Rational directions are linear functionals on rationalized actual characters. -/
abbrev Space (A : CommGroupScheme (Spec (CommRingCat.of k))) :=
  (ℚ ⊗[ℤ] characterLattice A) →ₗ[ℚ] ℚ

/-- Evaluation at an actual character, as a rational linear form on directions. -/
def rootForm (α : characterLattice A) : Module.Dual ℚ (Space A) where
  toFun v := v (toRat α)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem rootForm_apply (α : characterLattice A) (v : Space A) :
    rootForm α v = v (toRat α) :=
  rfl

/-- An integral cocharacter realizing a positive multiple of a rational direction. -/
structure IntegralRealization (v : Space A) where
  multiplier : ℤ
  positive : 0 < multiplier
  cocharacter : cocharacterLattice A
  pairing : ∀ α : characterLattice A,
    (latticePairing A α cocharacter : ℚ) = (multiplier : ℚ) * v (toRat α)

/-- Positive denominator clearing for a split torus, on its actual lattices. -/
def integralRealization (hA : IsSplitTorus A.toGrp) (v : Space A) :
    IntegralRealization v := by
  let h := hA.exists_positive_multiple_pairing v
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.choose, h.choose_spec.2.choose_spec⟩

namespace IntegralRealization

variable {v : Space A} (r : IntegralRealization v) (α : characterLattice A)

theorem pairing_eq_zero_iff :
    latticePairing A α r.cocharacter = 0 ↔ v (toRat α) = 0 := by
  have hd : (r.multiplier : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt r.positive
  have h : (latticePairing A α r.cocharacter : ℚ) = 0 ↔ v (toRat α) = 0 := by
    rw [r.pairing, mul_eq_zero]
    simp only [hd, false_or]
  exact_mod_cast h

theorem pairing_nonneg_iff :
    0 ≤ latticePairing A α r.cocharacter ↔ 0 ≤ v (toRat α) := by
  have hd : (0 : ℚ) < r.multiplier := by exact_mod_cast r.positive
  have h : 0 ≤ (latticePairing A α r.cocharacter : ℚ) ↔ 0 ≤ v (toRat α) := by
    rw [r.pairing]
    exact mul_nonneg_iff_of_pos_left hd
  exact_mod_cast h

theorem pairing_pos_iff :
    0 < latticePairing A α r.cocharacter ↔ 0 < v (toRat α) := by
  have hd : (0 : ℚ) < r.multiplier := by exact_mod_cast r.positive
  have h : 0 < (latticePairing A α r.cocharacter : ℚ) ↔ 0 < v (toRat α) := by
    rw [r.pairing]
    exact mul_pos_iff_of_pos_left hd
  exact_mod_cast h

end IntegralRealization

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual dynamic parabolic associated with a rational direction. -/
def parabolic (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G) (v : Space A) :
    SubgroupFunctor G :=
  Dynamic.parabolic (CommGroupScheme.groupHom (integralRealization hA v).cocharacter ≫ i)

/-- The actual dynamic centralizer associated with a rational direction. -/
def centralizer (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G) (v : Space A) :
    SubgroupFunctor G :=
  Dynamic.centralizer (CommGroupScheme.groupHom (integralRealization hA v).cocharacter ≫ i)

section Comparison

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
  (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G)

include hA in
/-- Parabolic containment is exactly the nonnegative-root implication, for
arbitrary positive integral realizations of both rational directions. -/
theorem IntegralRealization.parabolic_le_iff {v w : Space A}
    (r : IntegralRealization v) (s : IntegralRealization w) :
    Dynamic.parabolic (CommGroupScheme.groupHom r.cocharacter ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom s.cocharacter ≫ i) ↔
      ∀ α ∈ relativeRoots i, 0 ≤ v (toRat α) → 0 ≤ w (toRat α) := by
  rw [RelativeRoot.parabolic_le_iff_nonnegative_rootSupport dynamicConnected hA]
  simp only [r.pairing_nonneg_iff, s.pairing_nonneg_iff]

/-- Parabolic containment for the chosen realizations. -/
theorem parabolic_le_iff {v w : Space A} :
    parabolic hA i v ≤ parabolic hA i w ↔
      ∀ α ∈ relativeRoots i, 0 ≤ v (toRat α) → 0 ≤ w (toRat α) :=
  IntegralRealization.parabolic_le_iff hA i _ _

/-- Equality of nonnegative actual-root supports identifies the actual parabolics. -/
theorem parabolic_eq_of_nonnegative_iff {v w : Space A}
    (h : ∀ α ∈ relativeRoots i, 0 ≤ v (toRat α) ↔ 0 ≤ w (toRat α)) :
    parabolic hA i v = parabolic hA i w :=
  le_antisymm ((parabolic_le_iff hA i).2 fun α hα => (h α hα).1)
    ((parabolic_le_iff hA i).2 fun α hα => (h α hα).2)

/-- Positive integral realization does not change the associated parabolic. -/
theorem parabolic_eq_of_realization {v : Space A} (r : IntegralRealization v) :
    parabolic hA i v =
      Dynamic.parabolic (CommGroupScheme.groupHom r.cocharacter ≫ i) := by
  apply le_antisymm
  · exact (IntegralRealization.parabolic_le_iff hA i _ r).2 fun _ _ => id
  · exact (IntegralRealization.parabolic_le_iff hA i r _).2 fun _ _ => id

include hA in
/-- Zero-root support controls centralizer containment for any realizations. -/
theorem IntegralRealization.centralizer_le {v w : Space A}
    (r : IntegralRealization v) (s : IntegralRealization w)
    (h : ∀ α ∈ relativeRoots i, v (toRat α) = 0 → w (toRat α) = 0) :
    Dynamic.centralizer (CommGroupScheme.groupHom r.cocharacter ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom s.cocharacter ≫ i) :=
  dynamicCentralizer_le_of_root_zero_imp dynamicConnected hA i _ _
    fun α hα hzero =>
      (s.pairing_eq_zero_iff α).2 (h α hα ((r.pairing_eq_zero_iff α).1 hzero))

/-- Equality of zero actual-root supports identifies the actual centralizers. -/
theorem centralizer_eq_of_zero_iff {v w : Space A}
    (h : ∀ α ∈ relativeRoots i, v (toRat α) = 0 ↔ w (toRat α) = 0) :
    centralizer hA i v = centralizer hA i w :=
  le_antisymm
    (IntegralRealization.centralizer_le hA i _ _ fun α hα => (h α hα).1)
    (IntegralRealization.centralizer_le hA i _ _ fun α hα => (h α hα).2)

/-- Positive integral realization does not change the associated centralizer. -/
theorem centralizer_eq_of_realization {v : Space A} (r : IntegralRealization v) :
    centralizer hA i v =
      Dynamic.centralizer (CommGroupScheme.groupHom r.cocharacter ≫ i) := by
  apply le_antisymm
  · exact IntegralRealization.centralizer_le hA i _ r fun _ _ => id
  · exact IntegralRealization.centralizer_le hA i r _ fun _ _ => id

/-- The rational construction agrees with every original integral parabolic. -/
theorem parabolic_ofIntegral (ν : cocharacterLattice A) :
    parabolic hA i (rationalCocharacterEvaluation ν) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
  parabolic_eq_of_realization hA i
    ⟨1, by norm_num, ν, by intro α; simp only [rationalCocharacterEvaluation_toRat, Int.cast_one, one_mul]⟩

/-- The rational construction agrees with every original integral centralizer. -/
theorem centralizer_ofIntegral (ν : cocharacterLattice A) :
    centralizer hA i (rationalCocharacterEvaluation ν) =
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) :=
  centralizer_eq_of_realization hA i
    ⟨1, by norm_num, ν, by intro α; simp only [rationalCocharacterEvaluation_toRat, Int.cast_one, one_mul]⟩

/-- Strict sign chambers have exactly one actual dynamic parabolic. -/
theorem parabolic_eq_of_sameChamber {v w : Space A}
    (h : LinearAlgebra.FiniteHyperplaneSegment.SameChamber
      (fun α : relativeRoots i => rootForm (α : characterLattice A)) v w) :
    parabolic hA i v = parabolic hA i w := by
  apply parabolic_eq_of_nonnegative_iff hA i
  intro α hα
  rcases mul_pos_iff.mp (h ⟨α, hα⟩) with h' | h'
  · exact iff_of_true h'.1.le h'.2.le
  · exact iff_of_false (not_le_of_gt h'.1) (not_le_of_gt h'.2)

/-- Every regular rational direction centralizes exactly the original split torus. -/
theorem centralizer_eq_torusCentralizer_of_regular {v : Space A}
    (h : LinearAlgebra.FiniteHyperplaneSegment.Regular
      (fun α : relativeRoots i => rootForm (α : characterLattice A)) v) :
    centralizer hA i v = torusCentralizer i := by
  apply hA.dynamicCentralizer_eq_torusCentralizer i
  intro α hα hzero
  exact h ⟨α, hα⟩ (((integralRealization hA v).pairing_eq_zero_iff α).1 hzero)

end Comparison

section Regularity

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Equality with the full torus centralizer forces nonzero pairing with every
actual root, even when the torus itself is not maximal in that centralizer. -/
theorem isGenericCocharacter_of_centralizer_eq_torusCentralizer
    (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G) (ν : cocharacterLattice A)
    (h : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i) :
    IsGenericCocharacter i ν := by
  intro α hα hzero
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hfixed : X.toMul.val ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier _ := by
    apply (dynamicLie k G _ X.toMul).1.mpr
    have hcomp := weightSpace_le_weightSpace_cocharacter ν i α hX
    rwa [hzero] at hcomp
  rw [h] at hfixed
  have hXzero : X ∈ weightSpace i 0 :=
    Lie.mem_weightSpace_zero_of_mem_torusCentralizer i X.toMul hfixed
  exact hX0 ((Submodule.disjoint_def.mp (weightSpace_disjoint hA i hα.1)) X hX hXzero)

/-- Integral endpoints with the prescribed full torus centralizer give regular
rational directions for the finite arrangement. -/
theorem regular_ofIntegral_of_centralizer_eq
    (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G) (ν : cocharacterLattice A)
    (h : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i) :
    LinearAlgebra.FiniteHyperplaneSegment.Regular
      (fun α : relativeRoots i => rootForm (α : characterLattice A)) (rationalCocharacterEvaluation ν) := by
  intro α hzero
  apply isGenericCocharacter_of_centralizer_eq_torusCentralizer hA i ν h α α.property
  change rationalCocharacterEvaluation ν (toRat (α : characterLattice A)) = 0 at hzero
  rw [rationalCocharacterEvaluation_toRat] at hzero
  exact_mod_cast hzero

end Regularity

end Langlands.GroupScheme.RationalCocharacter
