import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.Weil.Local.Assembly
import Langlands.Weil.Representation.CharacterLine
import Langlands.Weil.Representation.InductionContinuity
import Langlands.VirtualRepresentation.ExactInduction
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.HarmonicAnalysis.CharacterTransport

/-!
# Actual common-closure inputs for local constants

All groups are the fixing subgroups in one actual local Weil pullback.
The exact virtual group uses continuous complex representations, with a carrier
universe closed under the existing finite-index induction construction.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open LocalClassField Weil.Local
open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual finite intermediate fields of the specified algebraic closure. -/
abbrev Extension := FiniteIntermediateExtension F.Carrier

/-- The subgroup of the actual base Weil group fixing this intermediate field. -/
abbrev weilSubgroup (E : Extension F) : Subgroup (localWeilGroup F) :=
  pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)

instance weilSubgroup_finiteIndex (E : Extension F) : (weilSubgroup F E).FiniteIndex := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact pullbackFixingFiniteIndex F.Carrier E.field (localResidueDegree F)

theorem weilSubgroup_open (E : Extension F) :
    IsOpen (weilSubgroup F E : Set (localWeilGroup F)) :=
  pullbackFixingSubgroup_open F.Carrier E.field (localResidueDegree F)

/-- Ordinary continuity for actual finite-dimensional representations. -/
abbrev ContinuousPredicate (E : Extension F) :
    FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E) → Prop :=
  fun A => A.IsContinuous

/-- The genuine quotient by short exact relations, with no semisimplicity assumption. -/
abbrev Virtual (E : Extension F) := ExactGrothendieckGroup (ContinuousPredicate.{uF, uV} F E)

/-- The actual integer virtual dimension. -/
abbrev degree (E : Extension F) : Virtual.{uF, uV} F E →ₗ[ℤ] ℤ :=
  ExactGrothendieckGroup.degree (ContinuousPredicate F E)

/-- The kernel of actual virtual dimension. -/
abbrev DegreeZero (E : Extension F) :=
  ExactGrothendieckGroup.degreeZero (ContinuousPredicate.{uF, uV} F E)

section Nested

variable (E L : Extension F) (h : E.field ≤ L.field)

include h in
/-- The actual inclusion reverses the field inclusion. -/
theorem weilSubgroup_antitone : weilSubgroup F L ≤ weilSubgroup F E :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h)

/-- Rebracketing the smaller actual Weil subgroup as a subgroup of the larger one. -/
def nestedWeilEquiv :
    (weilSubgroup F L).subgroupOf (weilSubgroup F E) ≃ₜ* weilSubgroup F L :=
  subgroupOfEquiv (weilSubgroup_antitone F E L h)

/-- The nested subgroup inherits openness from the ambient Weil group. -/
theorem nestedWeil_open :
    IsOpen ((weilSubgroup F L).subgroupOf (weilSubgroup F E) : Set (weilSubgroup F E)) :=
  (weilSubgroup_open F L).preimage continuous_subtype_val

/-- Actual equivariant-function induction after rebracketing the subgroup.
The carrier universe `max uF uV` is unchanged by induction. -/
def inducedRepresentation
    (A : FiniteRepresentation.ContinuousObjects.{uF, max uF uV} (weilSubgroup F L)) :
    FiniteRepresentation.ContinuousObjects.{uF, max uF uV} (weilSubgroup F E) :=
  FiniteRepresentation.continuousInduce _ (nestedWeil_open F E L)
    (FiniteRepresentation.continuousRestrict
      (nestedWeilEquiv F E L h : _ →ₜ* _).toMonoidHom
      (nestedWeilEquiv F E L h).continuous A)

/-- Induction on actual continuous exact virtual groups. Algebraic exactness
and usual-topology continuity are supplied by the proved induction theorems. -/
def induce : Virtual.{uF, uV} F L →ₗ[ℤ] Virtual.{uF, uV} F E :=
  (ExactGrothendieckGroup.induce
    ((weilSubgroup F L).subgroupOf (weilSubgroup F E)) _ _
    (fun _ hA => FiniteRepresentation.isContinuous_induce _ (nestedWeil_open F E L) hA)).comp
    (ExactGrothendieckGroup.continuousRestrict
      (nestedWeilEquiv F E L h : _ →ₜ* _))

/-- The map is actual induction on each genuine representation generator. -/
@[simp]
theorem induce_ofRepresentation
    (A : FiniteRepresentation.ContinuousObjects.{uF, max uF uV} (weilSubgroup F L)) :
    induce F E L h (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F L) ⟨A.val, A.property⟩) =
      ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E)
        ⟨(inducedRepresentation F E L h A).val,
          (inducedRepresentation F E L h A).property⟩ := by
  change ExactGrothendieckGroup.induce _ _ _ _
    (ExactGrothendieckGroup.restrict _ _ _ _
      (ExactGrothendieckGroup.ofRepresentation _ ⟨A.val, A.property⟩)) = _
  rw [ExactGrothendieckGroup.restrict_ofRepresentation,
    ExactGrothendieckGroup.induce_ofRepresentation]
  rfl

/-- Dimension is multiplied by the index of the actual nested subgroup. -/
theorem degree_induce (x : Virtual.{uF, uV} F L) :
    degree F E (induce F E L h x) =
      (((weilSubgroup F L).subgroupOf (weilSubgroup F E)).index : ℤ) * degree F L x := by
  change ExactGrothendieckGroup.degree _
    (ExactGrothendieckGroup.induce _ _ _ _
      (ExactGrothendieckGroup.continuousRestrict _ x)) = _
  rw [ExactGrothendieckGroup.degree_induce,
    ExactGrothendieckGroup.degree_continuousRestrict]

/-- Degree-zero induction is a restriction of the same exact virtual map. -/
def induceDegreeZero : DegreeZero.{uF, uV} F L →ₗ[ℤ] DegreeZero.{uF, uV} F E :=
  (induce F E L h).restrict fun x hx => by
    change degree F E (induce F E L h x) = 0
    rw [degree_induce, (ExactGrothendieckGroup.mem_degreeZero _ x).mp hx, mul_zero]

end Nested

/-- Canonical local-field data on the same intermediate field. -/
abbrev fieldData (E : Extension F) := LocalClassField.CommonClosure.canonicalData F E

/-- Continuous nontrivial unitary additive characters for the canonical topology. -/
abbrev AdditiveCharacter (E : Extension F) :=
  @HarmonicAnalysis.UnitaryAdditiveCharacter E.field _ (fieldData F E).topology

/-- Actual regular additive Haar measures on the canonical Borel space. -/
abbrev HaarMeasure (E : Extension F) :=
  @HarmonicAnalysis.AdditiveHaarMeasure E.field _ (fieldData F E).topology
    (@borel E.field (fieldData F E).topology)

/-- Continuous complex quasicharacters of the intermediate field. -/
abbrev FieldCharacter (E : Extension F) :=
  letI := (fieldData F E).topology
  E.fieldˣ →ₜ* ℂˣ

/-- Positive finite Haar scaling with the actual Borel measure. -/
def scaleHaar (E : Extension F) (μ : HaarMeasure F E) (c : NNReal) (hc : 0 < c) :
    HaarMeasure F E := by
  letI := (fieldData F E).topology
  letI := (fieldData F E).valuativeRel
  letI := (fieldData F E).localField
  letI : MeasurableSpace E.field := borel E.field
  haveI : BorelSpace E.field := ⟨rfl⟩
  exact μ.scale c hc

/-- Pullback by the trace for the actual nested field inclusion. -/
def traceCharacter (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) : AdditiveCharacter F L := by
  letI : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  letI : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower (Padic p) E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  exact (fieldData F E).traceCharacter (fieldData F L) ψ

/-- The trace constructor has exactly the intended additive-character formula. -/
@[simp]
theorem traceCharacter_apply (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (x : L.field) :
    traceCharacter F E L h ψ x =
      ψ (@Algebra.trace E.field L.field _ _ (IntermediateField.inclusion h).toAlgebra x) := rfl

/-- Candidate reciprocity on all actual common-closure subgroups. No family is selected. -/
abbrev ReciprocityFamily := LocalClassField.CommonClosure.CandidateFamily F
  (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F)

/-- The precise normalized coherent relation remains an explicit hypothesis. -/
abbrev NormalizedReciprocity (e : ReciprocityFamily F) : Prop :=
  LocalClassField.CommonClosure.NormalizedSystemRelation F
    (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F)
    F.canonicalTopologicalData e

/-- Project to the actual abelianization, then apply the supplied component. -/
def reciprocityUnits (e : ReciprocityFamily F) (E : Extension F) :
    letI := (fieldData F E).topology
    weilSubgroup F E →ₜ* E.fieldˣ := by
  letI := (fieldData F E).topology
  exact (e E : _ →ₜ* E.fieldˣ).comp (abelianizationProjection (weilSubgroup F E))

/-- Pullback of a field character through the supplied reciprocity component. -/
def weilCharacter (e : ReciprocityFamily F) (E : Extension F) (χ : FieldCharacter F E) :
    weilSubgroup F E →ₜ* ℂˣ := by
  letI := (fieldData F E).topology
  exact χ.comp (reciprocityUnits F e E)

/-- The actual continuous character line inserted into the exact virtual group. -/
def characterClass (e : ReciprocityFamily F) (E : Extension F) (χ : FieldCharacter F E) :
    Virtual.{uF, uV} F E :=
  ExactGrothendieckGroup.characterClass (weilCharacter F e E χ)

@[simp]
theorem degree_characterClass (e : ReciprocityFamily F) (E : Extension F)
    (χ : FieldCharacter F E) : degree F E (characterClass.{uF, uV} F e E χ) = 1 :=
  ExactGrothendieckGroup.degree_characterClass _

end Langlands.LocalFactor.CommonClosure
