import Langlands.TraceFormula.CoordinateLeviPresentation
import Langlands.TraceFormula.CyclicAdelicTests
import Langlands.Global.AdelicSpectralTransformSpaces
import Langlands.Global.AdelicParabolicSpectrum
import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Langlands.Automorphic.RegularAlgebraic

/-! # Normalized induction from the discrete spectrum of a coordinate Levi -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme

namespace CoordinateLevi.Presentation

variable {n : ℕ} {L : CoordinateLevi n} (P : L.Presentation)
variable (F : Type) [Field F]

/-- The inclusion of the actual block parabolic. -/
abbrev parabolicInclusion : P.parabolic F ⟶ cyclicBaseGroup F n :=
  GroupScheme.GeneralLinear.blockParabolicHom (Fin n) (CommRingCat.of F) P.weight

/-- The embedding of the diagonal blocks in the parabolic. -/
abbrev leviInclusion : P.levi F ⟶ P.parabolic F :=
  GroupScheme.GeneralLinear.blockLeviToParabolic (Fin n) (CommRingCat.of F) P.weight

/-- The diagonal-block projection. -/
abbrev leviProjection : P.parabolic F ⟶ P.levi F :=
  GroupScheme.GeneralLinear.blockLimitHom (Fin n) (CommRingCat.of F) P.weight

/-- The inclusion of the actual unipotent radical in the parabolic. -/
abbrev unipotentInclusion : P.unipotent F ⟶ P.parabolic F :=
  Dynamic.unipotentToParabolic
    (GroupScheme.GeneralLinear.isRepresentedBy_parabolic_diagonalCocharacter
      (Fin n) (CommRingCat.of F) P.weight)
    (GroupScheme.GeneralLinear.isRepresentedBy_unipotent_diagonalCocharacter
      (Fin n) (CommRingCat.of F) P.weight)

scoped instance : IsClosedImmersion (P.parabolicInclusion F).hom.hom.left :=
  GroupScheme.GeneralLinear.isClosedSubgroup_blockParabolicHom _ _ _

scoped instance : IsClosedImmersion ((P.unipotentInclusion F) ≫
    (P.parabolicInclusion F)).hom.hom.left := by
  unfold unipotentInclusion parabolicInclusion
  rw [Dynamic.unipotentToParabolic_comp]
  exact GroupScheme.GeneralLinear.isClosedSubgroup_blockUnipotentHom _ _ _

scoped instance : IsAffine (cyclicBaseGroup F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

scoped instance : IsAffine (P.parabolic F).X.left :=
  isAffine_left_of_isClosedSubgroup F (P.parabolicInclusion F)
    (GroupScheme.GeneralLinear.isClosedSubgroup_blockParabolicHom _ _ _)

scoped instance : IsAffine (P.levi F).X.left :=
  isAffine_left_of_isClosedSubgroup F _ (GroupScheme.GeneralLinear.isClosedSubgroup_blockLeviHom
    (Fin n) (CommRingCat.of F) P.weight)

scoped instance : IsAffine (P.unipotent F).X.left :=
  isAffine_left_of_isClosedSubgroup F _
    (GroupScheme.GeneralLinear.isClosedSubgroup_blockUnipotentHom
      (Fin n) (CommRingCat.of F) P.weight)

scoped instance : LocallyOfFiniteType (cyclicBaseGroup F n).X.hom :=
  let : Smooth (cyclicBaseGroup F n).X.hom :=
    GroupScheme.GeneralLinear.smoothStatement _ _
  inferInstance

scoped instance : LocallyOfFiniteType (P.parabolic F).X.hom := by
  rw [← Over.w (P.parabolicInclusion F).hom.hom]
  infer_instance

scoped instance : LocallyOfFiniteType (P.levi F).X.hom := by
  let h := GroupScheme.GeneralLinear.blockLeviHom (Fin n) (CommRingCat.of F) P.weight
  let : IsClosedImmersion h.hom.hom.left :=
    GroupScheme.GeneralLinear.isClosedSubgroup_blockLeviHom _ _ _
  rw [← Over.w h.hom.hom]
  infer_instance

/-- The rational representative in the actual ambient group. -/
abbrev weylPoint (s : RegularWeyl L) :
    Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (cyclicBaseGroup F n).X :=
  GroupScheme.GeneralLinear.permPoint (CommRingCat.of F) (P.weylPermutation s)

end CoordinateLevi.Presentation

open scoped CoordinateLevi.Presentation

namespace NormOneLeviInduction

open Langlands.Global.ArchimedeanGL

section InfinitesimalCharacter

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

/-- The archimedean slice of an actual section at the specified finite adele. -/
def archimedeanSlice (φ : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ)
    (b : FiniteAdelicGL F n) : InfiniteAdelicGL F n → ℂ := fun a =>
  φ ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm
    (AdelicGL.ofInfinite F n a * AdelicGL.ofFinite F n b))

/-- The norm of the imaginary part of the shifted highest weight after orthogonal
projection away from the positive split-centre line. The sum uses one coordinate
per complex embedding, with the same average on every number field. -/
def imaginaryInfinitesimalNorm (weight : EmbeddingIndex F → Fin n → ℂ) : ℝ := by
  classical
  letI := Fintype.ofFinite (EmbeddingIndex F)
  let a (j : EmbeddingIndex F) (i : Fin n) :=
    (weight j i + ((((n : ℝ) - 1) / 2 - (i.val : ℝ)) : ℂ)).im
  let degree : ℝ := Fintype.card (EmbeddingIndex F)
  let mean := (∑ j, ∑ i, a j i) / (degree * n)
  exact Real.sqrt ((∑ j, ∑ i, (a j i - mean) ^ 2) / degree)

/-- Each smooth archimedean slice is an eigensection for the same infinitesimal
character. The parameter of that character lies on the specified norm slice. -/
def HasImaginaryInfinitesimalNorm (φ : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ)
    (t : ℝ) : Prop :=
  ∃ (χ : EnvelopingCenter F n →ₐ[ℂ] ℂ) (weight : EmbeddingIndex F → Fin n → ℂ),
    IsHighestWeightCharacter F n weight χ ∧ imaginaryInfinitesimalNorm F n weight = t ∧
    ∀ b : FiniteAdelicGL F n, ∃ v : SmoothFunctions F n,
      v.val = archimedeanSlice F n φ b ∧
        ∀ z : EnvelopingCenter F n, centerAction F n z v = χ z • v

end InfinitesimalCharacter

variable {n : ℕ} {L : CoordinateLevi n}
variable (F : Type) [Field F] [NumberField F] (P : L.Presentation)

/-- Compact-picture coordinates and measures for normalized induction from an actual
coordinate Levi. The cutoff has total mass one in the split-component coordinates. -/
structure Model where
  compact : Subgroup (AdelicGroupPoints F (cyclicBaseGroup F n))
  iwasawa : IsIwasawaCompact (P.parabolicInclusion F) compact
  leviReductive : IsConnectedReductive (P.levi F)
  relativeDimension : ℕ
  smooth : SmoothOfRelativeDimension relativeDimension (cyclicBaseGroup F n).X.hom
  differential : Langlands.Automorphic.GroupSchemeFunctions.AdelicDifferentialCommutator
    F (cyclicBaseGroup F n) smooth
  leviHaar : Measure (AdelicGroupPoints F (P.levi F))
  leviHaar_isHaar : leviHaar.IsHaarMeasure
  iwasawaMeasure : IsIwasawaCompatibleMeasure compact iwasawa.isCompact
    (P.parabolicInclusion F) (P.unipotentInclusion F) (P.leviInclusion F) leviHaar
  parameterDimension : ℕ
  coordinates : (Fin parameterDimension → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P.parabolic F)
  cutoff : (Fin parameterDimension → ℝ) → ℝ
  cutoff_nonnegative : ∀ y, 0 ≤ cutoff y
  cutoff_integrable : Integrable cutoff
  cutoff_integral : ∫ y, cutoff y = 1

/-- The canonical Levi quotient is the quotient by rational points and the positive
split component of that Levi. -/
abbrev LeviL2 := Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F (P.levi F))

/-- The normalized Levi restriction at the point `g`, evaluated using a representative
of the canonical quotient. -/
def normalizedLeviSlice (φ : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ)
    (g : AdelicGroupPoints F (cyclicBaseGroup F n)) :
    RestrictionSplitCentre.CanonicalQuotient F (P.levi F) → ℂ := fun q =>
  let m := AdelicGroupPoints.map F (P.levi F) (P.parabolic F) (P.leviInclusion F) q.out
  parameterPower F (P.parabolic F) (-halfModulusParameter F (P.parabolic F)) m *
    φ (AdelicGroupPoints.map F (P.parabolic F) (cyclicBaseGroup F n)
      (P.parabolicInclusion F) m * g)

namespace Model

variable {F P} (D : Model F P)

/-- The compact-picture measure used by the imaginary intertwining family. -/
abbrev sectionMeasure :=
  inducedL2Measure D.compact D.iwasawa.isCompact (P.leviInclusion F)
    D.leviHaar D.coordinates D.cutoff

/-- The genuine discrete part of the Levi's right regular representation. -/
def leviDiscrete : Submodule ℂ (LeviL2 F P) :=
  discreteSpectrum F (P.levi F) D.leviReductive

/-- A square-integrable, normalized section valued in the specified Levi subspace. -/
def IsSectionWithSupport (V : Submodule ℂ (LeviL2 F P))
    (φ : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ) : Prop :=
  IsSquareIntegrableInducedForm D.compact D.iwasawa.isCompact (𝟙 (cyclicBaseGroup F n))
    D.smooth D.differential (P.parabolicInclusion F) (P.unipotentInclusion F)
    (P.leviInclusion F) φ ∧
  ∀ g : AdelicGroupPoints F (cyclicBaseGroup F n), ∃ v : V,
    ⇑(v.val : LeviL2 F P) =ᵐ[RestrictionSplitCentre.canonicalMeasure F (P.levi F)]
      normalizedLeviSlice F P φ g

/-- A section and its compact-picture representative give the same vector almost everywhere. -/
def Represents (f : Lp ℂ 2 D.sectionMeasure)
    (φ : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ) : Prop :=
  ⇑f =ᵐ[D.sectionMeasure] inducedRestriction D.compact
    (P.parabolicInclusion F) (P.leviInclusion F) φ

/-- The closed induced subspace generated by sections with the given Levi support and
imaginary infinitesimal norm. -/
def hilbertSliceWithSupport (V : Submodule ℂ (LeviL2 F P)) (t : ℝ) :
    Submodule ℂ (Lp ℂ 2 D.sectionMeasure) :=
  (Submodule.span ℂ {f : Lp ℂ 2 D.sectionMeasure |
    ∃ φ, D.IsSectionWithSupport V φ ∧ HasImaginaryInfinitesimalNorm F n φ t ∧
      D.Represents f φ}).topologicalClosure

/-- The Hilbert slice of the normalized induction from the full discrete Levi spectrum. -/
abbrev hilbertSlice (t : ℝ) := D.hilbertSliceWithSupport D.leviDiscrete t

/-- The ambient Hilbert space of square-integrable induced sections in the same coordinates. -/
abbrev ambientInduction :=
  inducedHilbertSpace D.compact D.iwasawa.isCompact (𝟙 (cyclicBaseGroup F n))
    D.smooth D.differential (P.parabolicInclusion F) (P.unipotentInclusion F)
    (P.leviInclusion F) D.leviHaar D.coordinates D.cutoff

/-- Each supported norm slice is a closed subspace of the ambient induced model. -/
theorem hilbertSliceWithSupport_le (V : Submodule ℂ (LeviL2 F P)) (t : ℝ) :
    D.hilbertSliceWithSupport V t ≤ D.ambientInduction := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro f ⟨φ, hφ, _, hrep⟩
  exact ⟨φ, hφ.1, hrep⟩

end Model
end NormOneLeviInduction
end Langlands.TraceFormula
