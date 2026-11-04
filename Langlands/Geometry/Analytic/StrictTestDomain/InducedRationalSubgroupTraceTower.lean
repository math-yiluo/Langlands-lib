import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupTower

/-! # Original compact pullback and trace towers at finite rational levels -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology Opposite
open Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison
open Langlands.LocallyConstantCovering

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {U : OpenSubgroup G} (d : ρ.InvariantRationalDomain U)
  (R : Type u) [CommRing R]

namespace OpenSubgroupTransport.FiniteIndexLevel

local instance {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    ∀ y : (rationalObject d W).InducedSpectrum,
      Finite ((rationalArrow d f).inducedMap ⁻¹' {y}) :=
  finite_rationalArrow_fiber d f

/-- Original compact pullbacks on all finite levels, without a local stability premise. -/
def compactPullbackTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) where
  obj V := CompactSections.coefficientFunctor (rationalObject d V.unop)
  map {V _W} f := subgroupRestrictionCompactSupportPullbackNatTrans (leOfHom f.unop)
    ((ρ.invariantRestrictionFunctor V.unop.property.1).obj d)
  map_id V := by
    apply NatTrans.ext
    funext M
    ext s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    exact congrArg s.val (Hom.inducedMap_id (rationalObject d V.unop) z)
  map_comp {V _W _Z} f g := subgroupRestrictionCompactSupportPullbackNatTrans_comp
    (leOfHom f.unop) (leOfHom g.unop)
    ((ρ.invariantRestrictionFunctor V.unop.property.1).obj d)

/-- The original unnormalized compact traces form a covariant full coefficient tower. -/
def compactTraceTower :
    FiniteIndexLevel U ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) where
  obj V := CompactSections.coefficientFunctor (rationalObject d V)
  map {_V W} f := subgroupRestrictionCompactSupportTraceNatTrans (leOfHom f)
    ((ρ.invariantRestrictionFunctor W.property.1).obj d)
  map_id V := by
    apply NatTrans.ext
    funext M
    change (rationalArrow d (𝟙 V)).compactSupportTrace
      (isCoveringMap_rationalArrow d (𝟙 V)) M =
        𝟙 (CompactSections.smoothRepresentation (rationalObject d V) M)
    ext s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    let : ∀ y : (rationalObject d V).InducedSpectrum,
        Finite ((id : (rationalObject d V).InducedSpectrum → _) ⁻¹' {y}) :=
      finite_id_fiber
    change fiberSum (rationalArrow d (𝟙 V)).inducedMap s.val y = s.val y
    have hid : ⇑(rationalArrow d (𝟙 V)).inducedMap = id := by
      funext z
      exact (congrArg (fun f : rationalObject d V ⟶ rationalObject d V =>
        f.inducedMap z) ((rationalTower d).map_id V)).trans
          (Hom.inducedMap_id (rationalObject d V) z)
    exact (fiberSum_congr (p := id) hid s.val y).trans (fiberSum_id s.val y)
  map_comp {_V _W Z} f g := subgroupRestrictionCompactSupportTraceNatTrans_comp
    (leOfHom g) (leOfHom f)
    ((ρ.invariantRestrictionFunctor Z.property.1).obj d)

@[simp]
theorem compactPullbackTower_obj (V : FiniteIndexLevel U) :
    (compactPullbackTower d R).obj (op V) =
      CompactSections.coefficientFunctor (rationalObject d V) := rfl

@[simp]
theorem compactTraceTower_obj (V : FiniteIndexLevel U) :
    (compactTraceTower d R).obj V =
      CompactSections.coefficientFunctor (rationalObject d V) := rfl

@[simp]
theorem compactPullbackTower_map {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    (compactPullbackTower d R).map f.op =
      subgroupRestrictionCompactSupportPullbackNatTrans (R := R) (leOfHom f)
        ((ρ.invariantRestrictionFunctor W.property.1).obj d) := rfl

@[simp]
theorem compactTraceTower_map {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    (compactTraceTower d R).map f =
      subgroupRestrictionCompactSupportTraceNatTrans (R := R) (leOfHom f)
        ((ρ.invariantRestrictionFunctor W.property.1).obj d) := rfl

/-- Point evaluation of the original covariant trace uses its whole original fiber. -/
@[simp]
theorem compactTraceTower_map_apply {V W : FiniteIndexLevel U} (f : V ⟶ W)
    (M : SmoothRep.{u, u, u} R G)
    (s : CompactSections.Functions (R := R) (V := M) (rationalObject d V))
    (y : (rationalObject d W).InducedSpectrum) :
    (SmoothRep.hom (((compactTraceTower d R).map f).app M) s).val y =
      fiberSum (rationalArrow d f).inducedMap s.val y := rfl

/-- The relative-index degree identity holds on the entire original coefficient category. -/
theorem compactPullbackTrace_degree {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    (compactPullbackTower d R).map f.op ≫ (compactTraceTower d R).map f =
      (V.val.toSubgroup.relIndex W.val.toSubgroup) •
        𝟙 ((compactTraceTower d R).obj W) := by
  apply NatTrans.ext
  funext M
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  exact subgroupRestrictionCompactSupportTrace_pullback_apply (leOfHom f) _ M s y

/-- Whole-group invariants of the original proper pullbacks, with no stability premise. -/
def invariantCompactPullbackTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  compactPullbackTower d R ⋙
    (Functor.whiskeringRight _ _ _).obj (smoothInvariants R G)

/-- Whole-group invariants of the same original finite-fiber trace tower. -/
def invariantCompactTraceTower :
    FiniteIndexLevel U ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  compactTraceTower d R ⋙
    (Functor.whiskeringRight _ _ _).obj (smoothInvariants R G)

/-- The unnormalized trace restricts the very same fiber sum to invariant functions. -/
@[simp]
theorem invariantCompactTraceTower_map_apply {V W : FiniteIndexLevel U} (f : V ⟶ W)
    (M : SmoothRep.{u, u, u} R G)
    (s : ((invariantCompactTraceTower d R).obj V).obj M)
    (y : (rationalObject d W).InducedSpectrum) :
    ((((invariantCompactTraceTower d R).map f).app M).hom s).val.val y =
      fiberSum (rationalArrow d f).inducedMap s.val.val y := rfl

/-- The same relative-index identity after actual whole-group invariants. -/
theorem invariantCompactPullbackTrace_degree {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    (invariantCompactPullbackTower d R).map f.op ≫
        (invariantCompactTraceTower d R).map f =
      (V.val.toSubgroup.relIndex W.val.toSubgroup) •
        𝟙 ((invariantCompactTraceTower d R).obj W) := by
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  ext s
  apply Subtype.ext
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  exact subgroupRestrictionCompactSupportTrace_pullback_apply (leOfHom f) _ M s.val y

/-- The canonical intersection span acts by original pullback followed by original trace. -/
def commonRefinementCorrespondence (V W : FiniteIndexLevel U) :
    (compactTraceTower d R).obj V ⟶ (compactTraceTower d R).obj W :=
  (compactPullbackTower d R).map (homOfLE (commonRefinement_le_left V W)).op ≫
    (compactTraceTower d R).map (homOfLE (commonRefinement_le_right V W))

/-- Every coefficient intertwiner commutes with the canonical intersection-span operator. -/
@[reassoc]
theorem commonRefinementCorrespondence_naturality (V W : FiniteIndexLevel U)
    {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    ((compactTraceTower d R).obj V).map a ≫
        (commonRefinementCorrespondence d R V W).app N =
      (commonRefinementCorrespondence d R V W).app M ≫
        ((compactTraceTower d R).obj W).map a :=
  (commonRefinementCorrespondence d R V W).naturality a

/-- Its formula sums over the entire original right-leg fiber of the intersection. -/
@[simp]
theorem commonRefinementCorrespondence_apply (V W : FiniteIndexLevel U)
    (M : SmoothRep.{u, u, u} R G)
    (s : CompactSections.Functions (R := R) (V := M) (rationalObject d V))
    (y : (rationalObject d W).InducedSpectrum) :
    (SmoothRep.hom ((commonRefinementCorrespondence d R V W).app M) s).val y =
      fiberSum (rationalArrow d (homOfLE (commonRefinement_le_right V W))).inducedMap
        (s.val ∘ (rationalArrow d (homOfLE (commonRefinement_le_left V W))).inducedMap) y :=
  rfl

/-- The same intersection operator on whole-group invariant compact functions. -/
def invariantCommonRefinementCorrespondence (V W : FiniteIndexLevel U) :
    (invariantCompactTraceTower d R).obj V ⟶
      (invariantCompactTraceTower d R).obj W :=
  Functor.whiskerRight (commonRefinementCorrespondence d R V W) (smoothInvariants R G)

variable [targetStable : HasStableNeighbourhoods ((inclusion U).obj d).subgroup.toSubgroup
  ((inclusion U).obj d).LocalSpectrum]

/-- When the Godement tower is available, its compact-function pullbacks are unchanged. -/
theorem compactPullbackTower_eq_compactFunctionsTower :
    compactPullbackTower d R = compactFunctionsTower d R := rfl

/-- The same equality after whole-group invariants. -/
theorem invariantCompactPullbackTower_eq_invariantCompactFunctionsTower :
    invariantCompactPullbackTower d R = invariantCompactFunctionsTower d R := rfl

end OpenSubgroupTransport.FiniteIndexLevel

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
