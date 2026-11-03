import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalProperTransport
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothGodementZero
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothGodementEdge

/-! # Full coefficient cohomology diagrams on proper induced rational transport -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory HomologicalComplex Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.SmoothProperTransport

open SmoothCohomology OpenSubgroupTransport.Hom

variable (ρ : RationalSpectralAction G P)

/-- Full compact functions and every original coefficient intertwiner, with
proper spatial pullback, form a contravariant diagram. -/
def compactFunctionsDiagram :
    (SmoothProperTransport ρ)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) where
  obj X := CompactSections.coefficientFunctor X.unop.transport
  map f := compactSupportPullbackNatTrans (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap f.unop)
  map_id X := compactSupportPullbackNatTrans_id X.unop.transport
  map_comp f g := compactSupportPullbackNatTrans_comp
    (Hom.transport g.unop) (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap g.unop) (Hom.isProperMap_inducedMap f.unop)

/-- Whole-group invariants of the original compact-function diagram. -/
def invariantCompactFunctionsDiagram :
    (SmoothProperTransport ρ)ᵒᵖ ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  compactFunctionsDiagram (R := R) ρ ⋙
    (Functor.whiskeringRight _ _ _).obj (smoothInvariants R G)

/-- The actual compact smooth Godement complexes, with their original proper
coefficient and spatial chain maps. -/
def godementCompactDiagram :
    (SmoothProperTransport ρ)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ CochainComplex (SmoothRep.{u, u, u} R G) ℕ) where
  obj X := godementCompactComplex X.unop.transport
  map f := godementCompactPullbackNatTrans (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap f.unop)
  map_id _X := godementCompactPullbackNatTrans_id
  map_comp f g := godementCompactPullbackNatTrans_comp
    (Hom.transport g.unop) (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap g.unop) (Hom.isProperMap_inducedMap f.unop)

/-- Invariant compact sections of the same Godement complexes, before homology. -/
def godementInvariantCompactDiagram :
    (SmoothProperTransport ρ)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ CochainComplex (ModuleCat.{u} R) ℕ) where
  obj X := godementInvariantCompactComplex X.unop.transport
  map f := godementInvariantCompactPullbackNatTrans (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap f.unop)
  map_id _X := godementInvariantCompactPullbackNatTrans_id
  map_comp f g := godementInvariantCompactPullbackNatTrans_comp
    (Hom.transport g.unop) (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap g.unop) (Hom.isProperMap_inducedMap f.unop)

/-- The complex comparison is natural in both proper rational transport and
every original smooth coefficient intertwiner. -/
def godementInvariantCompactDiagramIso :
    godementCompactDiagram (R := R) ρ ⋙
        (Functor.whiskeringRight _ _ _).obj
          ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)) ≅
      godementInvariantCompactDiagram (R := R) ρ :=
  NatIso.ofComponents
    (fun X => godementInvariantCompactComplexIso X.unop.transport)
    (fun f => godementInvariantCompactPullbackNatTrans_comparison
      (Hom.transport f.unop) (Hom.isProperMap_inducedMap f.unop))

/-- Apply actual smooth-representation homology to the compact complex diagram. -/
def godementCohomologyDiagram (q : ℕ) :
    (SmoothProperTransport ρ)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) :=
  godementCompactDiagram (R := R) ρ ⋙
    (Functor.whiskeringRight _ _ _).obj
      (homologyFunctor (SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q)

/-- Apply module homology after the termwise whole-group invariants. -/
def godementInvariantCohomologyDiagram (q : ℕ) :
    (SmoothProperTransport ρ)ᵒᵖ ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  godementInvariantCompactDiagram (R := R) ρ ⋙
    (Functor.whiskeringRight _ _ _).obj
      (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q)

/-- The original invariants edge is a natural transformation of spatial
diagrams in every degree, retaining the full coefficient functors. -/
def godementInvariantsEdgeDiagram (q : ℕ) :
    godementInvariantCohomologyDiagram (R := R) ρ q ⟶
      godementCohomologyDiagram (R := R) ρ q ⋙
        (Functor.whiskeringRight _ _ _).obj (smoothInvariants R G) where
  app X := godementInvariantsEdge X.unop.transport q
  naturality _ _ f := godementInvariantsEdge_pullback
    (Hom.transport f.unop) (Hom.isProperMap_inducedMap f.unop) q

instance isIso_godementInvariantsEdgeDiagram_zero :
    IsIso (godementInvariantsEdgeDiagram (R := R) ρ 0) := by
  have : ∀ X : (SmoothProperTransport ρ)ᵒᵖ,
      IsIso ((godementInvariantsEdgeDiagram (R := R) ρ 0).app X) := fun X => by
    change IsIso (godementInvariantsEdge (R := R) X.unop.transport 0)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

instance isIso_godementInvariantsEdgeDiagram
    [(smoothInvariants R G).PreservesHomology] (q : ℕ) :
    IsIso (godementInvariantsEdgeDiagram (R := R) ρ q) := by
  have : ∀ X : (SmoothProperTransport ρ)ᵒᵖ,
      IsIso ((godementInvariantsEdgeDiagram (R := R) ρ q).app X) := fun X => by
    change IsIso (godementInvariantsEdge (R := R) X.unop.transport q)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The same all-degree edge diagram with each original commuting square
retained as an actual arrow-category morphism. -/
def godementInvariantsArrowDiagram (q : ℕ) :
    (SmoothProperTransport ρ)ᵒᵖ ⥤
      Arrow (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) where
  obj X := godementInvariantsEdgeArrow X.unop.transport q
  map f := godementInvariantsEdgePullback (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap f.unop) q
  map_id _X := godementInvariantsEdgePullback_id q
  map_comp f g := godementInvariantsEdgePullback_comp
    (Hom.transport g.unop) (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap g.unop) (Hom.isProperMap_inducedMap f.unop) q

/-- Degree-zero sheaf-derived compact sections, with the existing transported
proper pullback. Only degree zero is used in this spatial diagram. -/
def compactDerivedZeroDiagram :
    (SmoothProperTransport ρ)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) where
  obj X := compactDerived X.unop.transport 0
  map f := compactDerivedZeroPullback (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap f.unop)
  map_id _X := compactDerivedZeroPullback_id
  map_comp f g := compactDerivedZeroPullback_comp
    (Hom.transport g.unop) (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap g.unop) (Hom.isProperMap_inducedMap f.unop)

/-- Degree-zero sheaf-derived invariant compact sections and their original
proper transported maps. -/
def invariantCompactDerivedZeroDiagram :
    (SmoothProperTransport ρ)ᵒᵖ ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) where
  obj X := invariantCompactDerived X.unop.transport 0
  map f := invariantCompactDerivedZeroPullback (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap f.unop)
  map_id _X := invariantCompactDerivedZeroPullback_id
  map_comp f g := invariantCompactDerivedZeroPullback_comp
    (Hom.transport g.unop) (Hom.transport f.unop)
    (Hom.isProperMap_inducedMap g.unop) (Hom.isProperMap_inducedMap f.unop)

/-- The actual all-degree compact Godement diagram recovers the original
compact-function diagram in degree zero. -/
def godementCohomologyZeroDiagramIso :
    godementCohomologyDiagram (R := R) ρ 0 ≅ compactFunctionsDiagram (R := R) ρ :=
  NatIso.ofComponents
    (fun X => godementCompactCohomologyZeroIso X.unop.transport)
    (fun f => godementCohomologyPullbackNatTrans_zero_toFunctions
      (Hom.transport f.unop) (Hom.isProperMap_inducedMap f.unop))

/-- The invariant all-degree diagram recovers the same original invariant
compact functions in degree zero. -/
def godementInvariantCohomologyZeroDiagramIso :
    godementInvariantCohomologyDiagram (R := R) ρ 0 ≅
      invariantCompactFunctionsDiagram (R := R) ρ :=
  NatIso.ofComponents
    (fun X => godementInvariantCompactCohomologyZeroIso X.unop.transport)
    (fun f => godementInvariantCohomologyPullbackNatTrans_zero_toFunctions
      (Hom.transport f.unop) (Hom.isProperMap_inducedMap f.unop))

/-- The actual sheaf-derived degree-zero diagram recovers all original
compact functions, naturally in spatial transport and coefficients. -/
def compactDerivedZeroDiagramIso :
    compactDerivedZeroDiagram (R := R) ρ ≅ compactFunctionsDiagram (R := R) ρ :=
  NatIso.ofComponents (fun X => compactDerivedZeroIso X.unop.transport)
    (fun f => compactDerivedZeroPullback_toFunctions
      (Hom.transport f.unop) (Hom.isProperMap_inducedMap f.unop))

/-- The same natural degree-zero recovery after whole-group invariants. -/
def invariantCompactDerivedZeroDiagramIso :
    invariantCompactDerivedZeroDiagram (R := R) ρ ≅
      invariantCompactFunctionsDiagram (R := R) ρ :=
  NatIso.ofComponents (fun X => invariantCompactDerivedZeroIso X.unop.transport)
    (fun f => invariantCompactDerivedZeroPullback_toFunctions
      (Hom.transport f.unop) (Hom.isProperMap_inducedMap f.unop))

/-- The two degree-zero routes agree as spatial diagrams of coefficient
functors, using the same canonical compact-function identifications. -/
def godementDerivedZeroDiagramIso :
    godementCohomologyDiagram (R := R) ρ 0 ≅ compactDerivedZeroDiagram (R := R) ρ :=
  godementCohomologyZeroDiagramIso ρ ≪≫ (compactDerivedZeroDiagramIso ρ).symm

/-- The invariant Godement and sheaf-derived degree-zero spatial diagrams
agree through their original invariant compact functions. -/
def godementInvariantDerivedZeroDiagramIso :
    godementInvariantCohomologyDiagram (R := R) ρ 0 ≅
      invariantCompactDerivedZeroDiagram (R := R) ρ :=
  godementInvariantCohomologyZeroDiagramIso ρ ≪≫
    (invariantCompactDerivedZeroDiagramIso ρ).symm

@[simp]
theorem godementDerivedZeroDiagramIso_hom_app (X : (SmoothProperTransport ρ)ᵒᵖ) :
    (godementDerivedZeroDiagramIso (R := R) ρ).hom.app X =
      (godementDerivedZeroIso X.unop.transport).hom := rfl

@[simp]
theorem godementInvariantDerivedZeroDiagramIso_hom_app
    (X : (SmoothProperTransport ρ)ᵒᵖ) :
    (godementInvariantDerivedZeroDiagramIso (R := R) ρ).hom.app X =
      (godementInvariantDerivedZeroIso X.unop.transport).hom := rfl

/-- The spatial diagram comparison preserves the compact-function
identification, as an equality of natural transformations of diagrams. -/
@[reassoc (attr := simp)]
theorem godementDerivedZeroDiagramIso_hom_comp :
    (godementDerivedZeroDiagramIso (R := R) ρ).hom ≫
        (compactDerivedZeroDiagramIso ρ).hom =
      (godementCohomologyZeroDiagramIso ρ).hom := by
  simp [godementDerivedZeroDiagramIso]

@[reassoc (attr := simp)]
theorem godementInvariantDerivedZeroDiagramIso_hom_comp :
    (godementInvariantDerivedZeroDiagramIso (R := R) ρ).hom ≫
        (invariantCompactDerivedZeroDiagramIso ρ).hom =
      (godementInvariantCohomologyZeroDiagramIso ρ).hom := by
  simp [godementInvariantDerivedZeroDiagramIso]

end OpenSubgroupTransport.SmoothProperTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
