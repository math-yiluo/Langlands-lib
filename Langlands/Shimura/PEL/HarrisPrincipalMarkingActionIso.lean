import Langlands.Shimura.PEL.HarrisIntegralPrincipalFullLevel
import Langlands.Shimura.PEL.HarrisIntegralLatticeIsogeny
import Langlands.Shimura.PEL.HarrisIntegralOrderActions
import Langlands.Shimura.PEL.PolarizedWeilOrderModel
import Langlands.AbelianScheme.PolarizedFiniteLevel.PrimitivePolarizationTransport
import Langlands.AbelianScheme.RelativeIntegralActionComparison
import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison

/-! # Compatible Harris markings under actual polarized action isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme.Tate (Index)

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A] [IsScalarTower ℚ E F]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {Φ : (E →+* ℝ) → (F →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (P : Prerequisites.{0})
    {S : Scheme.{0}} [QuasiSeparatedSpace S]

local notation "PObj" =>
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := S)
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation "OrderRestriction" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality O X

variable (X Y : PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := S))
    (e : letI := auxiliaryStarRing D C
      X.actionObj.abelianScheme ≅ Y.actionObj.abelianScheme)
    (aX : letI := auxiliaryStarRing D C
      PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability P.square P.universality
        (D.harrisHodgePELIntegralOrder C) X)
    (aY : letI := auxiliaryStarRing D C
      PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability P.square P.universality
        (D.harrisHodgePELIntegralOrder C) Y)
    (he : letI := auxiliaryStarRing D C
      ∀ z : D.harrisHodgePELIntegralOrder C,
        (aX.action z).asHom ≫ e.hom = e.hom ≫ (aY.action z).asHom)

omit [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] [QuasiSeparatedSpace S] in
private theorem extension_eq (V : PObj) (aV : OrderRestriction V) :
    letI := auxiliaryStarRing D C
    integralActionRationalExtension (BOf V) (D.harrisHodgePELIntegralBasis C) aV.action =
      V.actionObj.action := by
  let := auxiliaryStarRing D C
  exact IntegralOrderExtension.extend_unique (D.harrisHodgePELIntegralBasis C)
    ((Rationalization.ofEnd (BOf V)).comp aV.action)
    V.actionObj.action (fun z => CategoryTheory.End.ext (aV.agrees z).symm)

/-- Rationalization of an actual equivariant isomorphism is equivariant for
the full Harris actions. -/
def harrisIntegralActionIso :
    letI := auxiliaryStarRing D C
    X.actionObj ≅ Y.actionObj := by
  let := auxiliaryStarRing D C
  refine RationalAlgebraAction.isoMk (Rationalization.inclusion.mapIso e) ?_
  intro z
  have hz := integralActionRationalExtension_intertwines
    (D.harrisHodgePELIntegralBasis C) aX.action aY.action e.hom he z
  rw [extension_eq D C P X aX, extension_eq D C P Y aY] at hz
  exact hz

variable (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
    (additivity : PositivePairAdditivity D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
      P.universality (S := S))
    (hp : letI := auxiliaryStarRing D C
      X.polarization = DualWitness.transportMap P e
        (PolarizedWeilLevel.PolarizedAction.dualWitness P X)
        (PolarizedWeilLevel.PolarizedAction.dualWitness P Y) Y.polarization)

local notation "PAll" => (fun _ : ℕ => True)
local notation "T" => Over.mk s
local notation "Vf" => (Global.FiniteAdeles ℚ) ⊗[ℚ] A
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual
    (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "Norm" => HarrisIntegralFrameCondition D C P compatibility h s
local notation "red" => harrisIntegralFrameReduction D C P compatibility h s
local notation "eRat" => harrisIntegralActionIso D C P X Y e aX aY he

include hp in
omit [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] [QuasiSeparatedSpace S] in
private theorem multiple_one :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.Multiple P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      additivity X Y 1 eRat := by
  let := auxiliaryStarRing D C
  change IsRationalDualPullbackMultiple P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability X.hasDual Y.hasDual X.geometry Y.geometry
    X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation (additivity X Y)
    (1 : ℚ) (homToHom0 e.hom) (homToHom0 X.polarization) (homToHom0 Y.polarization)
  rw [IsRationalDualPullbackMultiple,
    rationalDualPullbackHom0_homToHom0 P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability X.hasDual Y.hasDual X.geometry Y.geometry
      X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation (additivity X Y), one_smul]
  exact congrArg homToHom0 hp.symm

/-- Transport the actual Weil frame along an integral polarized isomorphism. -/
def harrisIntegralPolarizedActionFrameIso : Frame X ≃ Frame Y := by
  let := auxiliaryStarRing D C
  exact Tate.weilAdelicFrameIsogeny P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability X.hasDual Y.hasDual X.geometry Y.geometry
    X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation (additivity X Y)
    X.polarization Y.polarization compatibility rationalWeilFunctoriality h
    X.actionObj.action Y.actionObj.action A (D.harrisHodgePELForm C) s 1
    (RationalAlgebraAction.underlyingIso eRat) (RationalAlgebraAction.intertwines (eRat).hom)
    (multiple_one D C P X Y e aX aY he additivity hp)

local notation "frameIso" =>
  harrisIntegralPolarizedActionFrameIso D C P X Y e aX aY he compatibility h s additivity hp

omit [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] in
private theorem rationalMap_frameIso (eta : Frame X) (v : Vf) :
    letI := auxiliaryStarRing D C
    (frameIso eta).val v = Tate.rationalMap T PAll e.hom (eta.val v) := by
  let := auxiliaryStarRing D C
  change Tate.rationalHomMap T PAll (Rationalization.ofHom e.hom) (eta.val v) = _
  rw [Tate.rationalHomMap_ofHom]

omit [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] in
/-- An isomorphism of the actual abelian schemes carries the two full
integral Tate images exactly onto one another. -/
theorem harrisIntegralFrameCondition_iff_of_tateMap
    (eta : Frame X) (xi : Frame Y)
    (hmap : letI := auxiliaryStarRing D C
      ∀ v : Vf, xi.val v = Tate.rationalMap T PAll e.hom (eta.val v)) :
    Norm X eta ↔ Norm Y xi := by
  let := auxiliaryStarRing D C
  have hinj : Function.Injective (Tate.rationalMap T PAll e.hom) := by
    have hh := (Tate.rationalIso T PAll (Rationalization.inclusion.mapIso e)).injective
    change Function.Injective (Tate.rationalHomMap T PAll (Rationalization.ofHom e.hom)) at hh
    rw [Tate.rationalHomMap_ofHom] at hh
    exact hh
  have himage (v : Vf) :
      (∃ x : GroupScheme.Tate.Full (BOf X).toGrp T,
        GroupScheme.Tate.toRational (BOf X).toGrp T PAll x = eta.val v) ↔
      (∃ y : GroupScheme.Tate.Full (BOf Y).toGrp T,
        GroupScheme.Tate.toRational (BOf Y).toGrp T PAll y = xi.val v) := by
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨Tate.map T PAll e.hom x, ?_⟩
      rw [hmap v, ← GroupScheme.Tate.rationalMap_toRational]
      exact congrArg (Tate.rationalMap T PAll e.hom) hx
    · rintro ⟨y, hy⟩
      refine ⟨Tate.map T PAll e.inv y, hinj ?_⟩
      have hr := GroupScheme.Tate.rationalMap_toRational T PAll (groupHom e.hom)
        (Tate.map T PAll e.inv y)
      change Tate.rationalMap T PAll e.hom _ = GroupScheme.Tate.toRational (BOf Y).toGrp T PAll
        ((Tate.map T PAll e.hom).comp (Tate.map T PAll e.inv) y) at hr
      rw [← Tate.map_comp, Iso.inv_hom_id, Tate.map_id, AddMonoidHom.id_apply] at hr
      exact hr.trans (hy.trans (hmap v))
  exact ⟨fun hn v => (hn v).trans (himage v), fun hn v => (hn v).trans (himage v).symm⟩

omit [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] in
/-- The matching torsion reductions are carried by the actual isomorphism on
the finite geometric torsion fibre. -/
theorem harrisIntegralFrameReduction_apply_iso (m : Index (fun _ => True))
    (eta : Frame X) (xi : Frame Y) (hn : Norm X eta) (hn' : Norm Y xi)
    (hmap : letI := auxiliaryStarRing D C
      ∀ v : Vf, xi.val v = Tate.rationalMap T PAll e.hom (eta.val v))
    (z : HarrisIntegralSourceMod D C m.val) :
    levelIsoLinear e T m.val (red X m eta hn z) = red Y m xi hn' z := by
  let := auxiliaryStarRing D C
  obtain ⟨v, rfl⟩ := (harrisIntegralSourceMultiples D C m.val).mkQ_surjective z
  rw [harrisIntegralFrameReduction_mkQ, harrisIntegralFrameReduction_mkQ]
  let full := harrisIntegralFrameFull D C P compatibility h s
  change GroupScheme.Tate.levelMap T (groupHom e.hom) m.val
      (GroupScheme.Tate.evaluation (BOf X).toGrp T PAll m (full X eta hn v)) = _
  rw [← GroupScheme.Tate.evaluation_map]
  apply congrArg (GroupScheme.Tate.evaluation (BOf Y).toGrp T PAll m)
  apply GroupScheme.Tate.full_toRational_injective (BOf Y).toGrp T
  rw [← GroupScheme.Tate.rationalMap_toRational, harrisIntegralFrameFull_toRational,
    harrisIntegralFrameFull_toRational]
  exact (hmap v.val).symm

variable [IsAlgClosed Ω]

local notation "gH" => Module.finrank ℚ E * n ^ 2
local notation "LiftAt" => HarrisPrincipalFullLevelCondition D C h P compatibility s

omit [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] [QuasiSeparatedSpace S] in
private theorem coordinates_apply_iso (m : Index (fun _ => True))
    (v : FullLevel (BOf X) gH m.val) (w : FullLevel (BOf Y) gH m.val)
    (hvw : ∀ j, levelIsoLinear e (Over.mk (𝟙 S)) m.val (v.sections j) = w.sections j)
    (r : Fin (2 * gH) → ZMod m.val) :
    levelIsoLinear e T m.val (v.fibreCoordinates Ω s r) = w.fibreCoordinates Ω s r := by
  have htuple : mapTuple e.hom v.sections = w.sections := funext hvw
  simp only [FullLevel.fibreCoordinates_apply, map_sum, LinearEquiv.map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change GroupScheme.Tate.levelMap T (groupHom e.hom) m.val (fibreTuple v.sections s i) = _
  rw [← fibreTuple_map, htuple]

include aX aY he additivity hp in
/-- Compatibility with the actual principal Harris marking is preserved and
reflected by a polarized order-equivariant isomorphism carrying its sections. -/
theorem harrisPrincipalFullLevelCondition_iff_actionIso (m : Index (fun _ => True))
    (v : FullLevel (BOf X) gH m.val) (w : FullLevel (BOf Y) gH m.val)
    (hvw : ∀ j, levelIsoLinear e (Over.mk (𝟙 S)) m.val (v.sections j) = w.sections j) :
    LiftAt X m v ↔ LiftAt Y m w := by
  let f := frameIso
  have hmap (eta : Frame X) := rationalMap_frameIso D C P X Y e aX aY he
    compatibility h s additivity hp eta
  have hc := coordinates_apply_iso D C P X Y e s m v w hvw
  constructor
  · rintro ⟨eta, hn, hη⟩
    have hn' := (harrisIntegralFrameCondition_iff_of_tateMap D C P X Y e
      compatibility h s eta (f eta) (hmap eta)).mp hn
    refine ⟨f eta, hn', fun r => ?_⟩
    have hr := harrisIntegralFrameReduction_apply_iso D C P X Y e
      compatibility h s m eta (f eta) hn hn' (hmap eta) (harrisPrincipalSourceCoordinates D C h m r)
    exact hr.symm.trans ((congrArg (levelIsoLinear e T m.val) (hη r)).trans (hc r))
  · rintro ⟨xi, hn', hξ⟩
    obtain ⟨eta, rfl⟩ := f.surjective xi
    have hn := (harrisIntegralFrameCondition_iff_of_tateMap D C P X Y e
      compatibility h s eta (f eta) (hmap eta)).mpr hn'
    refine ⟨eta, hn, fun r => (levelIsoLinear e T m.val).injective ?_⟩
    have hr := harrisIntegralFrameReduction_apply_iso D C P X Y e
      compatibility h s m eta (f eta) hn hn' (hmap eta) (harrisPrincipalSourceCoordinates D C h m r)
    exact hr.trans ((hξ r).trans (hc r).symm)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
