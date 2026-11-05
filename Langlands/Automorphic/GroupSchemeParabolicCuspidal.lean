import Langlands.Automorphic.GroupSchemeParabolicRadicals
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.Automorphic.GroupSchemeConstantTermConsequences
import Langlands.Automorphic.GroupSchemeGrowth

/-! # All-proper-parabolic vanishing on actual adelic functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- Any represented parabolic radical has a compact actual subgroup rational quotient. -/
theorem IsRationalParabolicRadical.compactSpace_rationalQuotient
    {P U : SubgroupFunctor G} (hU : IsRationalParabolicRadical P U) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U) := by
  obtain ⟨P₀, U₀, p, r, hp, _, hr, rfl⟩ := hU
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : IsAffineHom P₀.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  let : IsAffineHom U₀.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : IsAffine U₀.X.left := isAffine_of_isAffineHom U₀.X.hom
  exact AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (r ≫ p)
    hr.smooth hr.connectedSpace hr.isUnipotent

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)

/-- Compactness for every member of the intrinsic all-proper-parabolic family. -/
theorem compactSpace_properRationalParabolicRadicalQuotient
    (P : ProperRationalParabolic G) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)) :=
  (rationalParabolicRadical_spec hPD hG P.val).compactSpace_rationalQuotient F G

variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))

/-- Continuous rational functions with convergent vanishing constant terms for every
proper rational parabolic; the measures are explicit supplied parameters. -/
def parabolicCuspidalSubrepresentation :
    Subrepresentation (continuousRightAction F G) :=
  familyVanishingConstantTermSubrepresentation F G
    (properRationalParabolicRadicals hPD hG) measuresU

/-- The actual continuous function carrier, before any square-integrability restriction. -/
abbrev ParabolicCuspidalContinuousFunctions :=
  (parabolicCuspidalSubrepresentation F G hPD hG measuresU).toSubmodule

def parabolicCuspidalRightAction :
    Representation ℂ (AdelicGroupPoints F G)
      (ParabolicCuspidalContinuousFunctions F G hPD hG measuresU) :=
  (parabolicCuspidalSubrepresentation F G hPD hG measuresU).toRepresentation

theorem mem_parabolicCuspidalSubrepresentation
    (f : ContinuousRationalFunctions F G) :
    f ∈ parabolicCuspidalSubrepresentation F G hPD hG measuresU ↔
      ∀ P : ProperRationalParabolic G,
        HasConvergentConstantTerm F G (properRationalParabolicRadicals hPD hG P)
          (measuresU P) f ∧
        ∀ g : AdelicGroupPoints F G,
          constantTerm F G (properRationalParabolicRadicals hPD hG P)
            (measuresU P) f g = 0 :=
  mem_familyVanishingConstantTermSubrepresentation F G _ _ f

/-- The inclusion into the original continuous representation is faithful and equivariant. -/
def parabolicCuspidalInclusion :
    (parabolicCuspidalRightAction F G hPD hG measuresU).IntertwiningMap
      (continuousRightAction F G) where
  toLinearMap := (parabolicCuspidalSubrepresentation F G hPD hG measuresU).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem parabolicCuspidalInclusion_injective :
    Function.Injective (parabolicCuspidalInclusion F G hPD hG measuresU) :=
  Subtype.val_injective

/-- Intersection with the existing smooth common-finite-stabilizer space. -/
def finitePlotSmoothParabolicCuspidalSubrepresentation :
    Subrepresentation (continuousRightAction F G) :=
  parabolicCuspidalSubrepresentation F G hPD hG measuresU ⊓
    finitePlotSmoothRationalSubrepresentation F G

/-- The existing slice-wise polynomial-growth condition can be imposed on the same carrier.
This does not assert uniform growth of all enveloping derivatives or center finiteness. -/
def finitePlotSmoothPolynomialGrowthParabolicCuspidalSubrepresentation
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    Subrepresentation (continuousRightAction F G) :=
  parabolicCuspidalSubrepresentation F G hPD hG measuresU ⊓
    finitePlotSmoothPolynomialGrowthSubrepresentation F G rho

section FiniteBorel

variable [∀ P : ProperRationalParabolic G,
  BorelSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  [∀ P : ProperRationalParabolic G, IsFiniteMeasure (measuresU P)]

/-- Compactness is proved here; a finite Borel measure remains an explicit input. -/
theorem hasConvergentProperParabolicConstantTerm (P : ProperRationalParabolic G)
    (f : ContinuousRationalFunctions F G) :
    HasConvergentConstantTerm F G (properRationalParabolicRadicals hPD hG P)
      (measuresU P) f := by
  let := compactSpace_properRationalParabolicRadicalQuotient F G hPD hG P
  exact hasConvergentConstantTerm_of_compact F G _ (measuresU P) f

/-- With the stated measure hypotheses, membership is exactly all-parabolic vanishing. -/
theorem mem_parabolicCuspidalSubrepresentation_iff
    (f : ContinuousRationalFunctions F G) :
    f ∈ parabolicCuspidalSubrepresentation F G hPD hG measuresU ↔
      ∀ (P : ProperRationalParabolic G) (g : AdelicGroupPoints F G),
        constantTerm F G (properRationalParabolicRadicals hPD hG P)
          (measuresU P) f g = 0 := by
  rw [mem_parabolicCuspidalSubrepresentation]
  exact ⟨fun hf P => (hf P).2,
    fun hf P => ⟨hasConvergentProperParabolicConstantTerm F G hPD hG measuresU P f, hf P⟩⟩

/-- Changing each finite measure by a scalar with nonzero real value preserves vanishing.
No assertion identifies either supplied family as Haar or probability measures. -/
theorem parabolicCuspidalSubrepresentation_eq_of_smul_measure
    (measuresV : ∀ P : ProperRationalParabolic G,
      Measure (AdelicSubgroupPoints.RationalQuotient F G
        (properRationalParabolicRadicals hPD hG P)))
    [∀ P : ProperRationalParabolic G, IsFiniteMeasure (measuresV P)]
    (cs : ProperRationalParabolic G → ℝ≥0∞)
    (hcs : ∀ P, (cs P).toReal ≠ 0) (hmeasure : ∀ P, measuresV P = cs P • measuresU P) :
    parabolicCuspidalSubrepresentation F G hPD hG measuresU =
      parabolicCuspidalSubrepresentation F G hPD hG measuresV := by
  ext f
  change f ∈ parabolicCuspidalSubrepresentation F G hPD hG measuresU ↔
    f ∈ parabolicCuspidalSubrepresentation F G hPD hG measuresV
  rw [mem_parabolicCuspidalSubrepresentation_iff, mem_parabolicCuspidalSubrepresentation_iff]
  constructor
  · intro hf P g
    rw [hmeasure P, constantTerm_smul_measure, hf P g, smul_zero]
  · intro hf P g
    have h := hf P g
    rw [hmeasure P, constantTerm_smul_measure] at h
    exact (smul_eq_zero.mp h).resolve_left (hcs P)

end FiniteBorel

end Langlands.Automorphic.GroupSchemeFunctions
