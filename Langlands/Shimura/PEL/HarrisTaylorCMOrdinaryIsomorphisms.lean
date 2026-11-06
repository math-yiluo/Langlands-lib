import Langlands.Shimura.PEL.HarrisTaylorCMTateIntegralIsomorphisms

/-! # The ordinary isomorphism relation on full Tate-normalized Harris CM models -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (P : Prerequisites.{0})
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ Z.obj.left)
  (hs : ∀ Y : Cover Z.obj.left, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "NRep" => TateNormalizedCMRepresentative D C P Z compatibility h s hs htor
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "lev" U:max => (hodgeLevelFunctor D C).obj U
local notation "Mult" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.property.pairAdditivity
local notation "transport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor Z.property.torsionUnits
  Z.property.pairAdditivity
local notation "pullZ" X:max Y:max =>
  integralDualPullbackHom P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability (X).hasDual (Y).hasDual (X).geometry (Y).geometry
    (X).inversePoincare (X).evaluation (Y).inversePoincare (Y).evaluation
local notation "Related" => TateNormalizedCMRelated D C P Z compatibility h s hs htor
local notation "nrepClass" => tateNormalizedCMRepresentativeClass D C P Z
  compatibility h s hs htor

omit [IsCMField F] in
/-- The original rational action is exactly the rational extension of its
supplied integral order action. -/
theorem tateNormalizedCM_integralActionRationalExtension {U : HarrisLevel D}
    (x : NRep U) :
    letI := auxiliaryStarRing D C
    integralActionRationalExtension x.data.1.actionObj.abelianScheme
      (D.harrisHodgePELIntegralBasis C) x.restriction.action = x.data.1.actionObj.action := by
  let := auxiliaryStarRing D C
  exact IntegralOrderExtension.extend_unique (D.harrisHodgePELIntegralBasis C)
    ((Rationalization.ofEnd x.data.1.actionObj.abelianScheme).comp x.restriction.action)
    x.data.1.actionObj.action (fun a => (x.restriction.agrees a).symm)

local notation "extension_eq" => tateNormalizedCM_integralActionRationalExtension D C P Z
  compatibility h s hs htor

/-- An actual integral-order equivariant isomorphism canonically induces an
isomorphism for the original full rational actions. -/
def tateNormalizedCMOrdinaryRationalIso {U : HarrisLevel D} (x y : NRep U) :
    letI := auxiliaryStarRing D C
    ∀ (g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme)
      (_ha : ∀ a : O, x.restriction.action a ≫ g.hom = g.hom ≫ y.restriction.action a),
      x.data.1.actionObj ≅ y.data.1.actionObj := by
  let := auxiliaryStarRing D C
  intro g ha
  refine RationalAlgebraAction.isoMk (Rationalization.inclusion.mapIso g) ?_
  intro a
  have he := integralActionRationalExtension_intertwines
    (D.harrisHodgePELIntegralBasis C) x.restriction.action y.restriction.action g.hom ha a
  rw [extension_eq x, extension_eq y] at he
  exact he

local notation "ordinaryIso" => tateNormalizedCMOrdinaryRationalIso D C P Z
  compatibility h s hs htor

omit [IsCMField F] in
/-- Both original rational arrows are precisely the rationalizations of the
actual scheme isomorphism, without denominator factors. -/
theorem tateNormalizedCMOrdinaryRationalIso_arrows {U : HarrisLevel D} (x y : NRep U) :
    letI := auxiliaryStarRing D C
    ∀ (g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme)
      (ha : ∀ a : O, x.restriction.action a ≫ g.hom = g.hom ≫ y.restriction.action a),
      (RationalAlgebraAction.underlyingIso (ordinaryIso x y g ha)).hom =
        Rationalization.ofHom g.hom ∧
      (RationalAlgebraAction.underlyingIso (ordinaryIso x y g ha)).inv =
        Rationalization.ofHom g.inv := by
  let := auxiliaryStarRing D C
  intro g ha
  exact ⟨rfl, rfl⟩

omit [IsCMField F] in
/-- The actual arrow determines the rational action isomorphism uniquely. -/
theorem tateNormalizedCMOrdinaryRationalIso_eq {U : HarrisLevel D} (x y : NRep U) :
    letI := auxiliaryStarRing D C
    ∀ (g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme)
      (ha : ∀ a : O, x.restriction.action a ≫ g.hom = g.hom ≫ y.restriction.action a)
      (e : x.data.1.actionObj ≅ y.data.1.actionObj)
      (_hg : Rationalization.ofHom g.hom = (RationalAlgebraAction.underlyingIso e).hom),
      ordinaryIso x y g ha = e := by
  let := auxiliaryStarRing D C
  intro g ha e hg
  apply Iso.ext
  apply RationalAlgebraAction.hom_ext
  exact hg

omit [IsCMField F] in
/-- The polarization equation for the induced rational isomorphism is exactly
integral cross-multiple data for the actual arrow and the same scalar. -/
theorem tateNormalizedCMOrdinary_multiple_iff {U : HarrisLevel D}
    (x y : NRep U) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme)
      (ha : ∀ a : O, x.restriction.action a ≫ g.hom = g.hom ≫ y.restriction.action a),
      Mult x.data.1 y.data.1 q (ordinaryIso x y g ha) ↔
      Nonempty (Rationalization.IntegralMultipleData
        ((pullZ x.data.1 y.data.1) g.hom y.data.1.polarization)
        x.data.1.polarization (q : ℚ)) := by
  let := auxiliaryStarRing D C
  intro g ha
  rw [← Rationalization.ofHom_eq_smul_iff_nonempty_integralMultipleData]
  change Mult x.data.1 y.data.1 q (ordinaryIso x y g ha) ↔
    homToHom0 ((pullZ x.data.1 y.data.1) g.hom y.data.1.polarization) =
      (q : ℚ) • homToHom0 x.data.1.polarization
  rw [← rationalDualPullbackHom0_homToHom0 P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability x.data.1.hasDual y.data.1.hasDual
    x.data.1.geometry y.data.1.geometry x.data.1.inversePoincare x.data.1.evaluation
    y.data.1.inversePoincare y.data.1.evaluation
    (Z.property.pairAdditivity x.data.1 y.data.1)]
  rfl

local notation "ordinary_multiple_iff" => tateNormalizedCMOrdinary_multiple_iff D C P Z
  compatibility h s hs htor

/-- Ordinary equivalence uses an actual isomorphism, exact integral-order
equivariance, the original scalar polarization and the original level equation.
There is no independently supplied rational action isomorphism. -/
def TateNormalizedCMOrdinaryRelated {U : HarrisLevel D} (x y : NRep U) : Prop :=
  letI := auxiliaryStarRing D C
  ∃ (q : ℚˣ)
    (g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme)
    (ha : ∀ a : O, x.restriction.action a ≫ g.hom = g.hom ≫ y.restriction.action a)
    (hpol : Nonempty (Rationalization.IntegralMultipleData
      ((pullZ x.data.1 y.data.1) g.hom y.data.1.polarization)
      x.data.1.polarization (q : ℚ))),
    transport x.data.1 y.data.1 (lev U) q (ordinaryIso x y g ha)
      ((ordinary_multiple_iff x y q g ha).mpr hpol) x.data.2 = y.data.2

local notation "OrdinaryRelated" => TateNormalizedCMOrdinaryRelated D C P Z
  compatibility h s hs htor

variable [IsAlgClosed Ω]

omit [IsCMField F] in
/-- At source-stabilizing levels the unchanged normalized relation is exactly
the ordinary actual-isomorphism relation. -/
theorem tateNormalizedCMRelated_iff_ordinaryRelated {U : HarrisLevel D}
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : NRep U) : Related x y ↔ OrdinaryRelated x y := by
  let := auxiliaryStarRing D C
  rw [tateNormalizedCMRelated_iff_integralIsoRelated D C P Z compatibility h s hs htor hU]
  constructor
  · rintro ⟨q, e, he, g, hg, hgi, ha, hai, hpol, hlev⟩
    have hge := tateNormalizedCMOrdinaryRationalIso_eq D C P Z compatibility h s hs htor
      x y g ha e hg
    refine ⟨q, g, ha, hpol, ?_⟩
    simpa only [hge] using hlev
  · rintro ⟨q, g, ha, hpol, hlev⟩
    let e := ordinaryIso x y g ha
    have he : Mult x.data.1 y.data.1 q e :=
      (ordinary_multiple_iff x y q g ha).mpr hpol
    have hgi : ∀ a : O, y.restriction.action a ≫ g.inv = g.inv ≫ x.restriction.action a := by
      intro a
      calc
        y.restriction.action a ≫ g.inv =
            g.inv ≫ (g.hom ≫ y.restriction.action a) ≫ g.inv := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
        _ = g.inv ≫ (x.restriction.action a ≫ g.hom) ≫ g.inv := by rw [ha]
        _ = g.inv ≫ x.restriction.action a := by simp only [Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
    exact ⟨q, e, he, g, rfl, rfl, ha, hgi, hpol, hlev⟩

/-- Equality of the original normalized classes is characterized by the ordinary
relation on these very full Tate-normalized representatives. -/
theorem tateNormalizedCMRepresentativeClass_eq_iff_ordinaryRelated
    {U : HarrisLevel D}
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : NRep U) : nrepClass x = nrepClass y ↔ OrdinaryRelated x y :=
  (tateNormalizedCMRelated_iff_class_eq D C P Z compatibility h s hs htor x y).symm.trans
    (tateNormalizedCMRelated_iff_ordinaryRelated D C P Z compatibility h s hs htor hU x y)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
