import Langlands.Representation.Exponents.NormalizedTemperedCentralCharacterProof
import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Central-character data and the zero case for tempered representations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedCharacterDataAmbientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {hG : IsConnectedReductive G} {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
  {ω : Subgroup.center (rationalPoints G) →* ℂˣ}

/-- An actual unitary central-character datum for a tempered representation
with a scalar central character. On a zero carrier the construction uses the
trivial character; otherwise it retains the prescribed character. -/
def IsNormalizedExponentTempered.unitaryCentralCharacter
    (hπ : IsNormalizedExponentTempered hG π) (hω : π.HasCentralCharacter ω) :
    UnitaryCentralCharacter π.representation := by
  classical
  by_cases h : Nontrivial π
  · letI := h
    exact {
      character := ω
      isOpen_ker := hω.isOpen_ker π
      norm_eq_one := normalizedTemperedCentralCharacter k G hG π ω hπ hω
      acts := hω }
  · haveI : Subsingleton π := not_nontrivial_iff_subsingleton.mp h
    exact {
      character := 1
      isOpen_ker := by simp
      norm_eq_one := by simp
      acts := fun _ _ => Subsingleton.elim _ _ }

/-- On a nonzero carrier the constructed datum uses the original character. -/
@[simp]
theorem IsNormalizedExponentTempered.unitaryCentralCharacter_character [Nontrivial π]
    (hπ : IsNormalizedExponentTempered hG π) (hω : π.HasCentralCharacter ω) :
    (hπ.unitaryCentralCharacter hω).character = ω := by
  classical
  simp only [IsNormalizedExponentTempered.unitaryCentralCharacter,
    dite_eq_left (inferInstance : Nontrivial π)]

section Zero

variable [Subsingleton π]

/-- Every coefficient of a zero tempered representation is square-integrable
on the actual quotient by the full center, for every prescribed Haar measure. -/
theorem IsNormalizedExponentTempered.isSquareIntegrableModCenter_of_subsingleton
    [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
    (hπ : IsNormalizedExponentTempered hG π) (hω : π.HasCentralCharacter ω)
    (haar : MeasureTheory.Measure
      (rationalPoints G ⧸ Subgroup.center (rationalPoints G))) [haar.IsHaarMeasure] :
    IsSquareIntegrableModCenter π.representation haar := by
  refine ⟨hπ.isAdmissible, hπ.unitaryCentralCharacter hω, ?_⟩
  intro ℓ v
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  have hzero : (hπ.unitaryCentralCharacter hω).coefficientNorm ℓ 0 = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => simp [UnitaryCentralCharacter.coefficientNorm_mk, matrixCoefficient]
  rw [hzero]
  exact MeasureTheory.MemLp.zero

variable {P M U : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r)) {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)

/-- A zero source has zero unitary Jacquet part along every actual parabolic,
including the full parabolic. No temperedness premise is needed. -/
theorem unitaryJacquetPart_eq_bot_of_subsingleton :
    unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥ := by
  have : Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj π) :=
    (Jacquet.Localization.mk_surjective π.representation (pointImage (r ≫ p)) 1).subsingleton
  apply bot_unique
  intro x _
  change x = 0
  exact Subsingleton.elim _ _

end Zero

end Langlands.Aubert.General.RepresentedParabolic
