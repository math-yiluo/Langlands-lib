import Langlands.Shimura.PEL.HarrisTaylorCMSublevelPointLift
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf
import Langlands.AbelianScheme.Tate.WeilFrameLevelCovers
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof
import Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Étale-local sublevel lifting of unpointed normalized CM classes on connected bases -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteEtale

/-- The composite of the inclusion of a connected component of a finite étale cover of a
connected scheme with the covering map is surjective: the image of the component is
closed (finite maps are closed) and open (étale maps are open). -/
theorem surjective_componentι_comp_cover {S : Scheme.{0}} [ConnectedSpace S]
    (Y : Cover S) [IsLocallyNoetherian Y.obj.left] (c : _root_.ConnectedComponents Y.obj.left) :
    Surjective (componentι Y.obj.left c ≫ Y.obj.hom) := by
  obtain ⟨z, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  let Z : Set Y.obj.left := (componentOpen Y.obj.left (_root_.ConnectedComponents.mk z) : Set _)
  have hZclosed : IsClosed Z := by
    change IsClosed (componentOpen Y.obj.left (_root_.ConnectedComponents.mk z) : Set Y.obj.left)
    rw [componentOpen_mk]
    exact isClosed_connectedComponent
  have hclopen : IsClopen (Y.obj.hom '' Z) :=
    ⟨Y.obj.hom.isClosedMap _ hZclosed,
      Y.obj.hom.isOpenMap _ (componentOpen Y.obj.left (_root_.ConnectedComponents.mk z)).isOpen⟩
  have hne : (Y.obj.hom '' Z).Nonempty := ⟨Y.obj.hom z, z, rfl, rfl⟩
  have huniv := hclopen.eq_univ hne
  constructor
  intro x
  have hx : x ∈ Y.obj.hom '' Z := huniv ▸ Set.mem_univ x
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨⟨w, hw⟩, rfl⟩

/-- A geometric point of a locally Noetherian scheme lifts to the component scheme of the
component containing its image. -/
theorem range_subset_range_componentι {X : Scheme.{0}} [IsLocallyNoetherian X]
    {Ω : Type} [Field Ω] (y : Spec (.of Ω) ⟶ X) :
    Set.range y ⊆ Set.range (componentι X (_root_.ConnectedComponents.mk (y default))) := by
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q default]
  exact ⟨⟨y default, rfl⟩, rfl⟩

end Langlands.AlgebraicGeometry

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry
open GroupScheme.Tate (Index)

/-- The geometric point with the field of `a` and a given morphism. -/
def HarrisGeometricPoint.ofHom {S T : Scheme.{0}} (a : HarrisGeometricPoint T)
    (k : Spec (.of a.Ω) ⟶ S) : HarrisGeometricPoint S where
  Ω := a.Ω
  hom := k

/-- Reassembling a geometric point from its own field and morphism returns it. -/
theorem HarrisGeometricPoint.ofHom_self {S : Scheme.{0}} (a : HarrisGeometricPoint S) :
    a.ofHom a.hom = a :=
  rfl

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
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "tower" => unpointedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor
local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "levelSubgroup" U => ((hodgeLevelFunctor D C).obj U).toSubgroup
local notation "Hsim" =>
  ScalarExtensionSimilitudes A A (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "geo" => rationalWeilGeometricTransport
local notation "FrameAt" X:max a:max => Tate.WeilAdelicFrame preservation composition
  unitCoherence associativity comparison symmetry stability (X).hasDual (X).geometry
  (X).inversePoincare (X).evaluation compatibility (X).polarization h (X).actionObj.action A
  (D.harrisHodgePELForm C) a
local notation "rightAt" X:max a:max => Tate.weilAdelicFrameRightAction preservation
  composition unitCoherence associativity comparison symmetry stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) a

/-- Sublevel lifting after pullback to a connected base, tested at one geometric point
`t` of the new base: if, at the image point `s'` of `t` (with the field of `t`), the class
has a representative `x`, a frame `eta` in its level orbit, and the raw orbit of `eta` at
the smaller level is fixed by the image of `π₁(T, t)`, then the pulled class is the image
of a class at the smaller level. -/
theorem unpointedClassTowerPullback_exists_sublevel_of_point
    {S T : Bases} (f : T ⟶ S) {U U' : HarrisLevel D} (hle : U'.subgroup ≤ U.subgroup)
    (v : (tower S).obj U) (t : HarrisGeometricPoint T.obj.left)
    (s' : Spec (.of t.Ω) ⟶ S.obj.left) (hsq : t.hom ≫ f.hom.left = s')
    (x : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h s' (t.ofHom s').finiteFibers htor
      S.property.torsionUnits U)
    (hx : PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C S.obj.hom) x.1)
    (hn : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L
      S.obj.hom x.1)
    (hv : v.val (t.ofHom s') = HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C S.obj.hom) compatibility h s' (t.ofHom s').finiteFibers htor
      S.property.torsionUnits S.property.pairAdditivity L S.obj.hom x hx hn) :
    letI := auxiliaryStarRing D C
    letI : MulAction Hsimᵐᵒᵖ (FrameAt x.1 s') := rightAt x.1 s'
    letI : MulAction (FundamentalGroup s' (t.ofHom s').finiteFibers) (FrameAt x.1 s') :=
      Tate.weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
        comparison symmetry stability compatibility geo x.1.hasDual x.1.geometry
        x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action A
        (D.harrisHodgePELForm C) s' (t.ofHom s').finiteFibers htor S.property.torsionUnits
    letI : SMulCommClass (FundamentalGroup s' (t.ofHom s').finiteFibers) Hsimᵐᵒᵖ (FrameAt x.1 s') :=
      Tate.weilAdelicFrameActionsComm preservation composition unitCoherence associativity
        comparison symmetry stability compatibility geo x.1.hasDual x.1.geometry
        x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action A
        (D.harrisHodgePELForm C) s' (t.ofHom s').finiteFibers htor S.property.torsionUnits
    ∀ eta : FrameAt x.1 s', RightOrbit.mk (levelSubgroup U) eta = x.2.val →
      (∀ σ : FundamentalGroup t.hom t.finiteFibers,
        fundamentalGroupMap f.hom.left t.hom s' hsq t.finiteFibers (t.ofHom s').finiteFibers σ •
          RightOrbit.mk (levelSubgroup U') eta = RightOrbit.mk (levelSubgroup U') eta) →
      ∃ w : (tower T).obj U',
        (tower T).map (CompactOpenLevel.inclusion hle) w = (pull f).app U v := by
  subst hsq
  intro eta heta hfix
  obtain ⟨z, hz⟩ := classTowerBaseChangeAlong_exists_sublevel D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor f.hom.left S.obj.hom
    T.obj.hom t.hom (Over.w f.hom) (t.comp f.hom.left).finiteFibers t.finiteFibers
    S.property.lieNaturality S.property.torsionUnits T.property.torsionUnits
    (unpointedPullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality f)
    S.property.pairAdditivity T.property.pairAdditivity hle x hx hn eta heta hfix
  refine ⟨geometricFamilyExtension D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality T.obj.hom compatibility h htor
    T.property.torsionUnits T.property.pairAdditivity t U' z, ?_⟩
  apply (geometricFamilyEvaluationEquiv D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality T.obj.hom compatibility h
    htor T.property.torsionUnits T.property.pairAdditivity t U).injective
  change (geometricClassTower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality T.obj.hom compatibility h htor
      T.property.torsionUnits T.property.pairAdditivity t).map
      (CompactOpenLevel.inclusion hle)
      ((geometricClassComparison D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality T.obj.hom compatibility h htor
        T.property.torsionUnits T.property.pairAdditivity t t).hom.app U' z) =
    (geometricFamilyPointPullback D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor f.hom.left S.obj.hom T.obj.hom (Over.w f.hom)
      S.property.lieNaturality S.property.torsionUnits T.property.torsionUnits
      (unpointedPullbackDualData D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality f)
      S.property.pairAdditivity T.property.pairAdditivity t).app U
      (v.val (t.ofHom (t.hom ≫ f.hom.left)))
  rw [geometricClassComparison_refl, hv]
  exact hz

/-- Étale-local sublevel lifting on a connected admissible base: every unpointed class at
level `U` becomes, after pullback along an étale surjective morphism from a connected
admissible base, the image of an unpointed class at the smaller level `U'`. The new base is
the connected component, through a lift of a geometric point, of the finite étale cover whose
geometric fibre is the monodromy orbit of the raw `U'`-orbit of a frame in the level orbit. -/
theorem unpointedClassTower_exists_sublevel_etaleCover
    (S : Bases) {U U' : HarrisLevel D} (hle : U'.subgroup ≤ U.subgroup)
    (v : (tower S).obj U) :
    ∃ (T : Bases) (f : T ⟶ S), Etale f.hom.left ∧ Surjective f.hom.left ∧
      ∃ w : (tower T).obj U',
        (tower T).map (CompactOpenLevel.inclusion hle) w = (pull f).app U v := by
  let := auxiliaryStarRing D C
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  have : Module.Finite ℚ A := Module.Finite.trans E A
  have : IsSimpleRing A := D.simple
  let s0 : HarrisGeometricPoint S.obj.left :=
    HarrisGeometricPoint.ofResidue S.obj.left (Classical.arbitrary _)
  obtain ⟨x, hx, hn, hxq⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C S.obj.hom) compatibility h s0.hom s0.finiteFibers htor
    S.property.torsionUnits S.property.pairAdditivity L S.obj.hom (v.val s0)
  let K := (hodgeLevelFunctor D C).obj U
  let K' := (hodgeLevelFunctor D C).obj U'
  let := rightAt x.1 s0.hom
  let := Tate.weilAdelicFrameMonodromyAction preservation composition unitCoherence
    associativity comparison symmetry stability compatibility geo x.1.hasDual x.1.geometry
    x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action A
    (D.harrisHodgePELForm C) s0.hom s0.finiteFibers htor S.property.torsionUnits
  let := Tate.weilAdelicFrameActionsComm preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geo x.1.hasDual x.1.geometry
    x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action A
    (D.harrisHodgePELForm C) s0.hom s0.finiteFibers htor S.property.torsionUnits
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.2.val
  have heta' : RightOrbit.mk K.toSubgroup eta = x.2.val := heta
  have hfixU : RightOrbit.mk K.toSubgroup eta ∈
      MulAction.fixedPoints (FundamentalGroup s0.hom s0.finiteFibers)
        (RightOrbit (FrameAt x.1 s0.hom) K.toSubgroup) := by
    rw [heta']
    exact x.2.property
  let σ := (D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution
  let Y : Cover S.obj.left := Tate.weilAdelicFrameOrbitCover preservation composition
    unitCoherence associativity comparison symmetry stability compatibility x.1.hasDual
    x.1.geometry x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action A
    (D.harrisHodgePELForm C) s0.hom σ (hodgeRationalPELConditions D C) s0.finiteFibers htor
    S.property.torsionUnits eta K K' hfixU (RightOrbit.mk K'.toSubgroup eta)
  let y0 : Fiber s0.hom Y := Tate.weilAdelicFrameOrbitCoverPoint preservation composition
    unitCoherence associativity comparison symmetry stability compatibility x.1.hasDual
    x.1.geometry x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action A
    (D.harrisHodgePELForm C) s0.hom σ (hodgeRationalPELConditions D C) s0.finiteFibers htor
    S.property.torsionUnits eta K K' hfixU (RightOrbit.mk K'.toSubgroup eta)
  have : IsLocallyNoetherian Y.obj.left := LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  let y0l : Spec (.of s0.Ω) ⟶ Y.obj.left := y0.left
  let c0 : _root_.ConnectedComponents Y.obj.left := _root_.ConnectedComponents.mk (y0l default)
  let Ybar : Over (Spec (.of F)) := Over.mk (Y.obj.hom ≫ S.obj.hom)
  have : IsLocallyNoetherian Ybar.left := inferInstanceAs (IsLocallyNoetherian Y.obj.left)
  let T : Bases := ⟨componentCMOver Ybar c0,
    (componentwiseAdmissibleCMBase_of_relativeDual D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      relativeDualSchemeExistence relativeDualSchemeGeometry Ybar).components c0⟩
  let f : T ⟶ S := ObjectProperty.homMk (Over.homMk (componentι Y.obj.left c0 ≫ Y.obj.hom) (by
    change (componentι Y.obj.left c0 ≫ Y.obj.hom) ≫ S.obj.hom =
      componentι Y.obj.left c0 ≫ Y.obj.hom ≫ S.obj.hom
    rw [Category.assoc]))
  have hfleft : f.hom.left = componentι Y.obj.left c0 ≫ Y.obj.hom := rfl
  have hEtale : Etale f.hom.left := by
    rw [hfleft]
    infer_instance
  have hSurj : Surjective f.hom.left := by
    rw [hfleft]
    exact surjective_componentι_comp_cover Y c0
  let th : Spec (.of s0.Ω) ⟶ T.obj.left :=
    IsOpenImmersion.lift (componentι Y.obj.left c0) y0l (range_subset_range_componentι y0l)
  have hthι : th ≫ componentι Y.obj.left c0 = y0l := IsOpenImmersion.lift_fac _ _ _
  let t : HarrisGeometricPoint T.obj.left := { Ω := s0.Ω, hom := th }
  have hth : t.hom ≫ f.hom.left = s0.hom := by
    change th ≫ componentι Y.obj.left c0 ≫ Y.obj.hom = s0.hom
    rw [← Category.assoc, hthι]
    exact Over.w y0
  have hfix : ∀ σ' : FundamentalGroup t.hom t.finiteFibers,
      fundamentalGroupMap f.hom.left t.hom s0.hom hth t.finiteFibers s0.finiteFibers σ' •
        RightOrbit.mk K'.toSubgroup eta = RightOrbit.mk K'.toSubgroup eta := by
    intro σ'
    apply Tate.weilAdelicFrameOrbitCoverPoint_smul_eq preservation composition unitCoherence
      associativity comparison symmetry stability compatibility x.1.hasDual x.1.geometry
      x.1.inversePoincare x.1.evaluation x.1.polarization h x.1.actionObj.action A
      (D.harrisHodgePELForm C) s0.hom σ (hodgeRationalPELConditions D C) s0.finiteFibers htor
      S.property.torsionUnits eta K K' hfixU (RightOrbit.mk K'.toSubgroup eta)
    exact fundamentalGroupMap_smul_eq_of_factor f.hom.left t.hom s0.hom hth t.finiteFibers
      s0.finiteFibers y0 (componentι Y.obj.left c0) rfl hthι σ'
  refine ⟨T, f, hEtale, hSurj, ?_⟩
  exact unpointedClassTowerPullback_exists_sublevel_of_point D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor f hle v t s0.hom hth x hx hn
    hxq.symm eta heta' hfix

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
