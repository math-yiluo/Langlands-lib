import Langlands.Shimura.PEL.HarrisTaylorCMTateGeometricFamilies
import Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionProof

/-! # Actual isomorphisms between full Tate-normalized Harris CM models -/

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
local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "Full" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation "toRat" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp
    (Over.mk s) (fun _ => True)
local notation "lattice" => harrisIntegralLevelLattice D C P compatibility h s hs htor
  Z.property.torsionUnits
local notation "Mult" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.property.pairAdditivity
local notation "transport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor Z.property.torsionUnits
  Z.property.pairAdditivity
local notation "restore" => PolarizedWeilLevel.multiple_iff_integralPolarizedMultiple
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality (D.harrisHodgePELIntegralBasis C)
  Z.property.pairAdditivity
local notation "pullZ" X:max Y:max =>
  integralDualPullbackHom P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability (X).hasDual (Y).hasDual (X).geometry (Y).geometry
    (X).inversePoincare (X).evaluation (Y).inversePoincare (Y).evaluation
local notation "Related" => TateNormalizedCMRelated D C P Z compatibility h s hs htor
local notation "nrepClass" => tateNormalizedCMRepresentativeClass D C P Z
  compatibility h s hs htor

omit [IsCMField F] in
/-- The original level equation identifies the full integral Tate images under
the original rational Tate isomorphism, preserving and reflecting membership. -/
theorem tateNormalizedCMIso_full_image_iff {U : HarrisLevel D}
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : NRep U) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : x.data.1.actionObj ≅ y.data.1.actionObj)
      (he : Mult x.data.1 y.data.1 q e)
      (_hlev : transport x.data.1 y.data.1 (lev U) q e he x.data.2 = y.data.2)
      (w : Rat x.data.1),
      Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.underlyingIso e).hom w ∈ Set.range (toRat y.data.1) ↔
      w ∈ Set.range (toRat x.data.1) := by
  let := auxiliaryStarRing D C
  intro e he hlev w
  have hx := (harrisIntegralLevelCondition_iff_lattice D C P compatibility h s hs htor
    Z.property.torsionUnits x.data.1 (lev U) hU x.data.2).mp x.normalized
  have hy := (harrisIntegralLevelCondition_iff_lattice D C P compatibility h s hs htor
    Z.property.torsionUnits y.data.1 (lev U) hU y.data.2).mp y.normalized
  have hr := harrisIntegralLevelLattice_isogeny D C P compatibility h s
    Z.property.pairAdditivity hs htor Z.property.torsionUnits
    x.data.1 y.data.1 (lev U) hU q e he x.data.2 w
  rw [hlev] at hr
  change Tate.rationalHomMap (Over.mk s) (fun _ => True)
      (RationalAlgebraAction.underlyingIso e).hom w ∈
        (lattice y.data.1 (lev U) hU y.data.2 : Set (Rat y.data.1)) ↔
    w ∈ (lattice x.data.1 (lev U) hU x.data.2 : Set (Rat x.data.1)) at hr
  rwa [hx, hy] at hr

omit [IsCMField F] in
/-- An actual lift of the original forward rational arrow retains its original
polarization multiplier as exact integral cross-multiple data. -/
theorem tateNormalizedCMIso_integral_polarization {U : HarrisLevel D}
    (x y : NRep U) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : x.data.1.actionObj ≅ y.data.1.actionObj)
      (_he : Mult x.data.1 y.data.1 q e)
      (g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme)
      (_hg : Rationalization.ofHom g.hom = (RationalAlgebraAction.underlyingIso e).hom),
      Nonempty (Rationalization.IntegralMultipleData
        ((pullZ x.data.1 y.data.1) g.hom y.data.1.polarization)
        x.data.1.polarization (q : ℚ)) := by
  let := auxiliaryStarRing D C
  intro e he g hg
  apply (Rationalization.ofHom_eq_smul_iff_nonempty_integralMultipleData _ _ _).mp
  change homToHom0 ((pullZ x.data.1 y.data.1) g.hom y.data.1.polarization) =
    (q : ℚ) • homToHom0 x.data.1.polarization
  rw [← rationalDualPullbackHom0_homToHom0 P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability x.data.1.hasDual y.data.1.hasDual
    x.data.1.geometry y.data.1.geometry x.data.1.inversePoincare x.data.1.evaluation
    y.data.1.inversePoincare y.data.1.evaluation
    (Z.property.pairAdditivity x.data.1 y.data.1)]
  have hg' : homToHom0 g.hom = (RationalAlgebraAction.underlyingIso e).hom := hg
  rw [hg']
  exact he

variable [IsAlgClosed Ω]

omit [IsCMField F] in
/-- Every original polarized rational equivalence of two normalized models at
a source-stabilizing level is an actual equivariant abelian-scheme isomorphism. -/
theorem tateNormalizedCMIso_integral {U : HarrisLevel D}
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : NRep U) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : x.data.1.actionObj ≅ y.data.1.actionObj)
      (he : Mult x.data.1 y.data.1 q e)
      (_hlev : transport x.data.1 y.data.1 (lev U) q e he x.data.2 = y.data.2),
      ∃ g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme,
        Rationalization.ofHom g.hom = (RationalAlgebraAction.underlyingIso e).hom ∧
        Rationalization.ofHom g.inv = (RationalAlgebraAction.underlyingIso e).inv ∧
        (∀ a : O, x.restriction.action a ≫ g.hom = g.hom ≫ y.restriction.action a) ∧
        (∀ a : O, y.restriction.action a ≫ g.inv = g.inv ≫ x.restriction.action a) := by
  let := auxiliaryStarRing D C
  intro e he hlev
  let := harrisCMGeometricPoint_charZero D C P Z ⟨Ω, s⟩
  let r := Tate.rationalIso (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.underlyingIso e)
  have hr := tateNormalizedCMIso_full_image_iff D C P Z compatibility h s hs htor
    hU x y q e he hlev
  have hf : ∀ a : Full x.data.1, ∃ b : Full y.data.1,
      Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.underlyingIso e).hom ((toRat x.data.1) a) =
          (toRat y.data.1) b := by
    intro a
    obtain ⟨b, hb⟩ := (hr ((toRat x.data.1) a)).mpr ⟨a, rfl⟩
    exact ⟨b, hb.symm⟩
  have hi : ∀ b : Full y.data.1, ∃ a : Full x.data.1,
      Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.underlyingIso e).inv ((toRat y.data.1) b) =
          (toRat x.data.1) a := by
    intro b
    have hb : r (r.symm ((toRat y.data.1) b)) ∈ Set.range (toRat y.data.1) := by
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := (hr (r.symm ((toRat y.data.1) b))).mp hb
    exact ⟨a, ha.symm⟩
  obtain ⟨g, hg, hgi⟩ := Tate.connectedIntegralLatticeReflection htor Z.obj.left
    Z.property.torsionUnits Ω s x.data.1.actionObj.abelianScheme
    y.data.1.actionObj.abelianScheme (RationalAlgebraAction.underlyingIso e) hf hi
  refine ⟨g, hg, hgi, ?_, ?_⟩
  · intro a
    apply Tate.ofHom_injective Z.property.torsionUnits
      x.data.1.actionObj.abelianScheme y.data.1.actionObj.abelianScheme
    rw [Rationalization.ofHom_comp, Rationalization.ofHom_comp, hg]
    change comp0 _ _ _ (homToHom0 (x.restriction.action a))
        (RationalAlgebraAction.hom0 e.hom) =
      comp0 _ _ _ (RationalAlgebraAction.hom0 e.hom)
        (homToHom0 (y.restriction.action a))
    rw [x.restriction.agrees, y.restriction.agrees]
    exact RationalAlgebraAction.intertwines e.hom (a : A)
  · intro a
    apply Tate.ofHom_injective Z.property.torsionUnits
      y.data.1.actionObj.abelianScheme x.data.1.actionObj.abelianScheme
    rw [Rationalization.ofHom_comp, Rationalization.ofHom_comp, hgi]
    change comp0 _ _ _ (homToHom0 (y.restriction.action a))
        (RationalAlgebraAction.hom0 e.inv) =
      comp0 _ _ _ (RationalAlgebraAction.hom0 e.inv)
        (homToHom0 (x.restriction.action a))
    rw [y.restriction.agrees, x.restriction.agrees]
    exact RationalAlgebraAction.intertwines e.inv (a : A)

/-- The actual-isomorphism formulation retains the original rational action iso,
its multiplier and exact original level equation, with no denominator on its lift. -/
def TateNormalizedCMIntegralIsoRelated {U : HarrisLevel D} (x y : NRep U) : Prop :=
  letI := auxiliaryStarRing D C
  ∃ (q : ℚˣ) (e : x.data.1.actionObj ≅ y.data.1.actionObj)
    (he : Mult x.data.1 y.data.1 q e)
    (g : x.data.1.actionObj.abelianScheme ≅ y.data.1.actionObj.abelianScheme),
    Rationalization.ofHom g.hom = (RationalAlgebraAction.underlyingIso e).hom ∧
    Rationalization.ofHom g.inv = (RationalAlgebraAction.underlyingIso e).inv ∧
    (∀ a : O, x.restriction.action a ≫ g.hom = g.hom ≫ y.restriction.action a) ∧
    (∀ a : O, y.restriction.action a ≫ g.inv = g.inv ≫ x.restriction.action a) ∧
    Nonempty (Rationalization.IntegralMultipleData
      ((pullZ x.data.1 y.data.1) g.hom y.data.1.polarization)
      x.data.1.polarization (q : ℚ)) ∧
    transport x.data.1 y.data.1 (lev U) q e he x.data.2 = y.data.2

local notation "ActualRelated" => TateNormalizedCMIntegralIsoRelated D C P Z
  compatibility h s hs htor

omit [IsCMField F] in
/-- The original relation on normalized models is exactly its actual-isomorphism
formulation, at a source-stabilizing level. -/
theorem tateNormalizedCMRelated_iff_integralIsoRelated {U : HarrisLevel D}
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : NRep U) : Related x y ↔ ActualRelated x y := by
  let := auxiliaryStarRing D C
  constructor
  · rintro ⟨q, e, hd, hlev⟩
    let he := (restore x.data.1 y.data.1 x.restriction y.restriction q e).mpr hd
    obtain ⟨g, hg, hgi, ha, hai⟩ := tateNormalizedCMIso_integral D C P Z
      compatibility h s hs htor hU x y q e he hlev
    exact ⟨q, e, he, g, hg, hgi, ha, hai,
      tateNormalizedCMIso_integral_polarization D C P Z compatibility h s hs htor
        x y q e he g hg, hlev⟩
  · rintro ⟨q, e, he, g, hg, hgi, ha, hai, hpol, hlev⟩
    exact ⟨q, e,
      (restore x.data.1 y.data.1 x.restriction y.restriction q e).mp he, hlev⟩

/-- Equality of the original CM classes of normalized models admits exactly
these actual equivariant isomorphisms, with the original scalar and level. -/
theorem tateNormalizedCMRepresentativeClass_eq_iff_integralIsoRelated
    {U : HarrisLevel D}
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : NRep U) : nrepClass x = nrepClass y ↔ ActualRelated x y :=
  (tateNormalizedCMRelated_iff_class_eq D C P Z compatibility h s hs htor x y).symm.trans
    (tateNormalizedCMRelated_iff_integralIsoRelated D C P Z compatibility h s hs htor hU x y)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
