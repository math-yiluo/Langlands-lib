import Langlands.Automorphic.CuspidalUnitaryCompactForm
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientStatement
import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanSeparateJointFiniteProof

/-! # Joint finiteness of actual determinant-band Hilbert orbit coefficients -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F]

local instance jointFiniteRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance jointFiniteContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance jointFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance jointFiniteFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance jointFiniteStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace CuspidalHilbertOrbitCoefficient

section Realization

variable {n : ℕ} (S : OperatorRealization F n)

local instance jointFiniteRealizationGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Composition of two positive right translations of the quotient. -/
theorem translate_translate (a b : AdelicGL F n) (q : OperatorDeterminantSlice.Quotient F n) :
    OperatorDeterminantSlice.translate F n a (OperatorDeterminantSlice.translate F n b q) =
      OperatorDeterminantSlice.translate F n (b * a) q := by
  obtain ⟨x, rfl⟩ := OperatorDeterminantSlice.point_surjective F n q
  simp only [OperatorDeterminantSlice.translate_point, mul_assoc]

set_option maxHeartbeats 500000 in
/-- The standard compact action is the same positive right translation on the quotient. -/
theorem toQuotient_compactRepresentation (k : standardInfiniteCompact F n) (f : S.Space)
    (q : OperatorDeterminantSlice.Quotient F n) :
    OperatorDeterminantSlice.toQuotient F n S (S.compactRepresentation k f) q =
      OperatorDeterminantSlice.toQuotient F n S f
        (OperatorDeterminantSlice.translate F n (AdelicGL.ofInfinite F n k.val) q) :=
  OperatorDeterminantSlice.toQuotient_compact F n S k f q

set_option maxHeartbeats 400000 in
/-- The common ideal of the ambient center-finiteness condition annihilates the realized
vector itself under the restricted enveloping action. -/
theorem exists_center_ideal (f : S.Space) :
    ∃ I : Ideal (ArchimedeanGL.EnvelopingCenter F n),
      Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter F n ⧸ I.restrictScalars ℂ) ∧
      ∀ z ∈ I, S.envelopingAction (ArchimedeanGL.centerInclusion F n z) f = 0 := by
  obtain ⟨I, hI, hz⟩ := (isCenterFinite_iff_exists_ideal F n _).mp
    (S.isAutomorphicForm_ambient f).2.2.1
  refine ⟨I, hI, fun z hzI => ?_⟩
  have hslice : ∀ y : FiniteAdelicGL F n,
      finiteSmoothSlice F n y
        (S.ambient (S.envelopingAction (ArchimedeanGL.centerInclusion F n z) f)) = 0 :=
    fun y => (congrArg (finiteSmoothSlice F n y)
      (S.ambient_envelopingAction (ArchimedeanGL.centerInclusion F n z) f)).trans
        ((finiteSmoothSlice_envelopingAction F n _ (S.ambient f) y).trans (hz z hzI y))
  apply S.toContinuous_injective
  rw [map_zero]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  change evaluate F n (S.toContinuous
    (S.envelopingAction (ArchimedeanGL.centerInclusion F n z) f)) x = 0
  have hx := congrArg (fun s : ArchimedeanGL.SmoothFunctions F n => s.val (AdelicGL.infinite F n x))
    (hslice (AdelicGL.finite F n x))
  simp only [S.finiteSmoothSlice_ambient_apply,
    ← OperatorRealization.pair_eq_ofInfinite_mul_ofFinite, AdelicGL.pair_projections] at hx
  exact hx

/-- The standard compact orbit of a realized vector spans a finite-dimensional space. -/
theorem isFiniteVector_compactRepresentation (f : S.Space) :
    Langlands.FiniteVectors.IsFiniteVector S.compactRepresentation f :=
  S.compactRepresentation_isFiniteVector f

end Realization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

local instance jointFiniteSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _

set_option maxHeartbeats 400000 in
/-- Compact translation of the cusp function is right translation of the coefficient. -/
theorem coefficient_compactRepresentation (w : BandHilbertSpace F r)
    (k : standardInfiniteCompact F (r + 1)) (f : T.Space) (g : InfiniteAdelicGL F (r + 1)) :
    coefficient T w (T.realization.compactRepresentation k f) g =
      coefficient T w f (g * k.val) := by
  unfold coefficient integrand
  congr 1
  funext q
  rw [toQuotient_compactRepresentation, translate_translate, map_mul]

set_option maxHeartbeats 400000 in
/-- A coefficient map with the actual values intertwines the standard compact actions. -/
theorem compactRepresentation_intertwines (w : BandHilbertSpace F r)
    (C : T.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F (r + 1))
    (hval : ∀ f g, (C f).val g = coefficient T w f g)
    (k : standardInfiniteCompact F (r + 1)) (f : T.Space) :
    C (T.realization.compactRepresentation k f) =
      ArchimedeanGL.smoothRightAction F (r + 1) k.val (C f) := by
  refine Subtype.ext (funext fun g => ?_)
  change (C (T.realization.compactRepresentation k f)).val g = (C f).val (g * k.val)
  rw [hval, hval]
  exact coefficient_compactRepresentation T w k f g

/-- Any complex-linear coefficient map with the actual values and genuine enveloping
covariance sends every realized vector to a jointly finite smooth function. -/
theorem isJointFinite_of_covariant (w : BandHilbertSpace F r)
    (C : T.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F (r + 1))
    (hval : ∀ f g, (C f).val g = coefficient T w f g)
    (hcov : ∀ (a : ArchimedeanGL.EnvelopingAlgebra F (r + 1)) (f : T.Space),
      C (T.realization.envelopingAction a f) = ArchimedeanGL.envelopingAction F (r + 1) a (C f))
    (f : T.Space) : ArchimedeanGL.IsJointFinite F (r + 1) (C f) := by
  -- Center finiteness: the common ambient ideal kills `C f`.
  have hcenter : ArchimedeanGL.IsCenterFinite F (r + 1) (C f) := by
    obtain ⟨I, hI, hz⟩ := exists_center_ideal T.realization f
    change Module.Finite ℂ (ArchimedeanGL.centerOrbitSpan F (r + 1) (C f))
    rw [ArchimedeanGL.centerOrbitSpan_eq_range]
    let := hI
    have hle : I.restrictScalars ℂ ≤
        LinearMap.ker (ArchimedeanGL.centerOrbitMap F (r + 1) (C f)) := by
      intro z hzI
      rw [LinearMap.mem_ker, ArchimedeanGL.centerOrbitMap_apply,
        ArchimedeanGL.centerAction_apply, ← hcov, hz z hzI, map_zero]
    have : Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter F (r + 1) ⧸
        LinearMap.ker (ArchimedeanGL.centerOrbitMap F (r + 1) (C f))) :=
      Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    exact Module.Finite.equiv
      (ArchimedeanGL.centerOrbitMap F (r + 1) (C f)).quotKerEquivRange
  -- Compact finiteness: group finiteness transported, then differentiated.
  have hgroup : Langlands.FiniteVectors.IsFiniteVector
      ((ArchimedeanGL.smoothRightAction F (r + 1)).comp
        (standardInfiniteCompact F (r + 1)).subtype) (C f) := by
    let Φ : T.realization.compactRepresentation.IntertwiningMap
        ((ArchimedeanGL.smoothRightAction F (r + 1)).comp
          (standardInfiniteCompact F (r + 1)).subtype) :=
      { toLinearMap := C
        isIntertwining' := fun k => LinearMap.ext fun f =>
          compactRepresentation_intertwines T w C hval k f }
    exact (isFiniteVector_compactRepresentation T.realization f).map Φ
  exact ArchimedeanGL.separateJointFinite F (r + 1) (C f) hcenter
    (ArchimedeanGL.compactGroupFiniteDifferential F (r + 1) (C f) hgroup)

end CuspidalHilbertOrbitCoefficient

set_option maxHeartbeats 800000 in
/-- The target statement follows from integrability together with a complex-linear
coefficient map that has the actual values and genuine enveloping covariance: joint
finiteness is supplied by `isJointFinite_of_covariant`. -/
theorem cuspidalHilbertOrbitCoefficientStatement_of_covariant
    (h : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r : ℕ) (T : CuspidalOperatorRealization F r),
      Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      ∀ w : CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r,
        (∀ f g, Integrable (CuspidalHilbertOrbitCoefficient.integrand T w f g)
          (CuspidalHilbertOrbitCoefficient.bandMeasure F r)) ∧
        ∃ C : T.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F (r + 1),
          (∀ f g, (C f).val g = CuspidalHilbertOrbitCoefficient.coefficient T w f g) ∧
          (∀ (a : ArchimedeanGL.EnvelopingAlgebra F (r + 1)) (f : T.Space),
            C (T.realization.envelopingAction a f) =
              ArchimedeanGL.envelopingAction F (r + 1) a (C f))) :
    CuspidalHilbertOrbitCoefficientStatement.{u} := by
  intro F _ _ _ r T hT w
  obtain ⟨hint, C, hval, hcov⟩ := h F r T hT w
  exact ⟨hint, C, hval, hcov,
    CuspidalHilbertOrbitCoefficient.isJointFinite_of_covariant T w C hval hcov⟩

end Langlands.Automorphic
