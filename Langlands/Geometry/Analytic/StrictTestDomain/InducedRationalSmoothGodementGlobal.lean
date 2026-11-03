import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothGodementTransport
import Langlands.Cohomology.SmoothGodement.CoefficientGlobal

/-! # Global Godement pullback and support comparison on induced rational spectra -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory HomologicalComplex Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementCohomology
open Langlands.Cohomology.SmoothGodementCohomology.Spatial

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.SmoothCohomology

variable (X : ρ.OpenSubgroupTransport) [HasStableNeighbourhoods G X.InducedSpectrum]

/-- All global sections of the separate smooth Godement complex of the full
coefficient sheaf on the actual induced rational spectrum. -/
def godementGlobalComplex :
    SmoothRep.{u, u, u} R G ⥤ CochainComplex (Rep.{u} R G) ℕ :=
  sheafFunctor X ⋙ smoothGodementGlobalComplex R G X.InducedSpectrum

/-- Actual algebraic-representation homology of that global-section complex. -/
def godementGlobalCohomology (q : ℕ) :
    SmoothRep.{u, u, u} R G ⥤ Rep.{u} R G :=
  godementGlobalComplex X ⋙ homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q

/-- The actual compact-support inclusion, natural in all original coefficients. -/
def godementForgetSupportComplex :
    godementCompactComplex (R := R) X ⋙
        SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ) ⟶
      godementGlobalComplex X :=
  Functor.whiskerLeft (sheafFunctor X) (forgetSupportComplex R G X.InducedSpectrum)

@[simp]
theorem godementForgetSupportComplex_apply (M : SmoothRep.{u, u, u} R G) (n : ℕ)
    (s : ((godementCompactComplex X).obj M).X n) :
    (((godementForgetSupportComplex X).app M).f n).hom s = s.val := rfl

/-- The existing exact-inclusion homology comparison followed by homology
of the actual compact-support inclusion. -/
def godementForgetSupport (q : ℕ) :
    godementCompactCohomology (R := R) X q ⋙ SmoothRep.toRep ⟶
      godementGlobalCohomology X q :=
  Functor.whiskerLeft (sheafFunctor X) (forgetSupport R G X.InducedSpectrum q)

theorem godementForgetSupport_app (q : ℕ) (M : SmoothRep.{u, u, u} R G) :
    (godementForgetSupport X q).app M =
      (Langlands.Cohomology.DerivedPlus.mapHomologicalComplexHomologyIso
        (SmoothRep.toRep (R := R) (G := G)) (ComplexShape.up ℕ) q).inv.app
          ((godementCompactComplex X).obj M) ≫
        (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map
          ((godementForgetSupportComplex X).app M) :=
  forgetSupport_app R G X.InducedSpectrum ((sheafFunctor X).obj M) q

end OpenSubgroupTransport.SmoothCohomology

namespace OpenSubgroupTransport.Hom

open SmoothCohomology

variable {X Y Z : ρ.OpenSubgroupTransport}
  [HasStableNeighbourhoods G X.InducedSpectrum]
  [HasStableNeighbourhoods G Y.InducedSpectrum]
  [HasStableNeighbourhoods G Z.InducedSpectrum]

/-- Actual global chain pullback along every induced rational transport map. -/
def godementGlobalPullbackNatTrans (f : X ⟶ Y) :
    godementGlobalComplex (R := R) Y ⟶ godementGlobalComplex X :=
  coefficientGlobalNatTrans f.inducedMap f.inducedMap_smul

theorem godementGlobalPullbackNatTrans_app (f : X ⟶ Y)
    (M : SmoothRep.{u, u, u} R G) :
    (godementGlobalPullbackNatTrans f).app M =
      (smoothGodementGlobalComplex R G Y.InducedSpectrum).map
          (SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M) ≫
        globalMap f.inducedMap f.inducedMap_smul ((sheafFunctor X).obj M) := rfl

/-- The formula acts on original global sections in every chain degree. -/
@[simp]
theorem godementGlobalPullbackNatTrans_apply (f : X ⟶ Y)
    (M : SmoothRep.{u, u, u} R G) (n : ℕ)
    (s : ((godementGlobalComplex Y).obj M).X n) :
    (((godementGlobalPullbackNatTrans f).app M).f n).hom s =
      ((((Godement.SmoothSpatial.complexMap f.inducedMap f.inducedMap_smul
        ((sheafFunctor X).obj M)).f n).hom.hom.app
          (Opposite.op ActionOpens.top)).hom
        ((((smoothGodementGlobalComplex R G Y.InducedSpectrum).map
          (SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M)).f n).hom
            s)).val := rfl

@[reassoc]
theorem godementGlobalPullbackNatTrans_naturality (f : X ⟶ Y)
    {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (godementGlobalComplex Y).map a ≫ (godementGlobalPullbackNatTrans f).app N =
      (godementGlobalPullbackNatTrans f).app M ≫ (godementGlobalComplex X).map a :=
  (godementGlobalPullbackNatTrans f).naturality a

@[simp]
theorem godementGlobalPullbackNatTrans_id :
    godementGlobalPullbackNatTrans (R := R) (𝟙 X) =
      𝟙 (godementGlobalComplex X) := by
  exact (coefficientGlobalNatTrans_congr
    (inducedMap_smul (𝟙 X)) (fun (_ : G) (_ : X.InducedSpectrum) => rfl)
    (SheafVariation.inducedMap_id_eq X)).trans coefficientGlobalNatTrans_id

/-- Strict contravariant global composition uses the equality of actual induced maps. -/
theorem godementGlobalPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    godementGlobalPullbackNatTrans (R := R) (f ≫ g) =
      godementGlobalPullbackNatTrans g ≫ godementGlobalPullbackNatTrans f := by
  calc
    _ = coefficientGlobalNatTrans (R := R) (g.inducedMap.comp f.inducedMap)
        (fun k x => by
          change g.inducedMap (f.inducedMap (k • x)) =
            k • g.inducedMap (f.inducedMap x)
          rw [f.inducedMap_smul, g.inducedMap_smul]) :=
      coefficientGlobalNatTrans_congr _ _ (SheafVariation.inducedMap_comp_eq f g)
    _ = _ := coefficientGlobalNatTrans_comp
      f.inducedMap f.inducedMap_smul g.inducedMap g.inducedMap_smul

/-- Actual homology of the constructed global chain pullback, in every degree. -/
def godementGlobalCohomologyPullbackNatTrans (f : X ⟶ Y) (q : ℕ) :
    godementGlobalCohomology (R := R) Y q ⟶ godementGlobalCohomology X q :=
  Functor.whiskerRight (godementGlobalPullbackNatTrans f)
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q)

theorem godementGlobalCohomologyPullbackNatTrans_app (f : X ⟶ Y) (q : ℕ)
    (M : SmoothRep.{u, u, u} R G) :
    (godementGlobalCohomologyPullbackNatTrans f q).app M =
      (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map
        ((godementGlobalPullbackNatTrans f).app M) := rfl

@[reassoc]
theorem godementGlobalCohomologyPullbackNatTrans_naturality (f : X ⟶ Y) (q : ℕ)
    {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (godementGlobalCohomology Y q).map a ≫
        (godementGlobalCohomologyPullbackNatTrans f q).app N =
      (godementGlobalCohomologyPullbackNatTrans f q).app M ≫
        (godementGlobalCohomology X q).map a :=
  (godementGlobalCohomologyPullbackNatTrans f q).naturality a

@[simp]
theorem godementGlobalCohomologyPullbackNatTrans_id (q : ℕ) :
    godementGlobalCohomologyPullbackNatTrans (R := R) (𝟙 X) q =
      𝟙 (godementGlobalCohomology X q) := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [godementGlobalPullbackNatTrans_id]
  exact (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map_id _

theorem godementGlobalCohomologyPullbackNatTrans_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    godementGlobalCohomologyPullbackNatTrans (R := R) (f ≫ g) q =
      godementGlobalCohomologyPullbackNatTrans g q ≫
        godementGlobalCohomologyPullbackNatTrans f q := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [godementGlobalPullbackNatTrans_comp f g]
  exact Functor.map_comp _ _ _

/-- Proper compact pullback commutes with the original support inclusions. -/
@[reassoc]
theorem godementCompactPullbackNatTrans_forgetSupport (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G) :
    (SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((godementCompactPullbackNatTrans f hf).app M) ≫
        (godementForgetSupportComplex X).app M =
      (godementForgetSupportComplex Y).app M ≫
        (godementGlobalPullbackNatTrans f).app M :=
  coefficientCompactNatTrans_forgetSupport f.inducedMap f.inducedMap_smul hf M

/-- The support square is an equality of full coefficient natural transformations. -/
theorem godementCompactPullbackNatTrans_forgetSupport_natTrans (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    Functor.whiskerRight (godementCompactPullbackNatTrans (R := R) f hf)
        (SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ)) ≫
        godementForgetSupportComplex X =
      godementForgetSupportComplex Y ≫ godementGlobalPullbackNatTrans f := by
  apply NatTrans.ext
  funext M
  exact godementCompactPullbackNatTrans_forgetSupport f hf M

/-- The same square holds for actual compact and global Godement homology. -/
@[reassoc]
theorem godementCohomologyPullbackNatTrans_forgetSupport (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) (M : SmoothRep.{u, u, u} R G) :
    SmoothRep.toRep.map ((godementCohomologyPullbackNatTrans f hf q).app M) ≫
        (godementForgetSupport X q).app M =
      (godementForgetSupport Y q).app M ≫
        (godementGlobalCohomologyPullbackNatTrans f q).app M :=
  coefficientCohomologyNatTrans_forgetSupport f.inducedMap f.inducedMap_smul hf q M

theorem godementCohomologyPullbackNatTrans_forgetSupport_natTrans (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) :
    Functor.whiskerRight (godementCohomologyPullbackNatTrans (R := R) f hf q)
        SmoothRep.toRep ≫ godementForgetSupport X q =
      godementForgetSupport Y q ≫ godementGlobalCohomologyPullbackNatTrans f q := by
  apply NatTrans.ext
  funext M
  exact godementCohomologyPullbackNatTrans_forgetSupport f hf q M

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
