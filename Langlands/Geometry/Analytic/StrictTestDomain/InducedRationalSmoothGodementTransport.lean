import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothCohomology
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactComplex
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalDirectImage
import Langlands.Cohomology.SmoothGodement.CoefficientSpatial

/-! # All-degree smooth Godement pullback on actual induced rational spectra -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory HomologicalComplex Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementCohomology.Spatial

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.Hom

open SmoothCohomology

variable {X Y Z : ρ.OpenSubgroupTransport}
  [HasStableNeighbourhoods G X.InducedSpectrum]
  [HasStableNeighbourhoods G Y.InducedSpectrum]
  [HasStableNeighbourhoods G Z.InducedSpectrum]

/-- Pull back the actual compact smooth Godement complexes of the full
coefficient sheaves along a proper induced rational transport map. -/
def godementCompactPullbackNatTrans (f : X ⟶ Y) (hf : IsProperMap f.inducedMap) :
    godementCompactComplex (R := R) Y ⟶ godementCompactComplex X :=
  coefficientCompactNatTrans f.inducedMap f.inducedMap_smul hf

/-- The component resolves the original coefficient sheaf pullback before
applying the actual proper spatial chain map. -/
theorem godementCompactPullbackNatTrans_app (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G) :
    (godementCompactPullbackNatTrans f hf).app M =
      (Langlands.Cohomology.SmoothGodementCohomology.smoothGodementCompactComplex
          R G Y.InducedSpectrum).map
        (SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M) ≫
      compactMap f.inducedMap f.inducedMap_smul hf ((sheafFunctor X).obj M) := rfl

/-- Every degree acts on original compact sections by the constructed
coefficient and spatial sheaf maps. -/
@[simp]
theorem godementCompactPullbackNatTrans_apply (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G) (n : ℕ)
    (s : ((godementCompactComplex Y).obj M).X n) :
    (SmoothRep.hom (((godementCompactPullbackNatTrans f hf).app M).f n) s).val =
      ((((Godement.SmoothSpatial.complexMap f.inducedMap f.inducedMap_smul
        ((sheafFunctor X).obj M)).f n).hom.hom.app
          (Opposite.op ActionOpens.top)).hom
        (SmoothRep.hom
          (((Langlands.Cohomology.SmoothGodementCohomology.smoothGodementCompactComplex
              R G Y.InducedSpectrum).map
            (SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M)).f n)
          s).val).val := rfl

/-- All original coefficient intertwiners commute with the chain pullback. -/
@[reassoc]
theorem godementCompactPullbackNatTrans_naturality (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (godementCompactComplex Y).map a ≫ (godementCompactPullbackNatTrans f hf).app N =
      (godementCompactPullbackNatTrans f hf).app M ≫
        (godementCompactComplex X).map a :=
  (godementCompactPullbackNatTrans f hf).naturality a

@[simp]
theorem godementCompactPullbackNatTrans_id :
    godementCompactPullbackNatTrans (R := R) (𝟙 X) (isProperMap_inducedMap_id X) =
      𝟙 (godementCompactComplex X) := by
  exact (coefficientCompactNatTrans_congr
    (inducedMap_smul (𝟙 X)) (fun (_ : G) (_ : X.InducedSpectrum) => rfl)
    (isProperMap_inducedMap_id X) isProperMap_id (SheafVariation.inducedMap_id_eq X)).trans
      coefficientCompactNatTrans_id

/-- The actual proper rational transport maps give strict contravariant
chain maps, without an assumed inverse to any lax comparison. -/
theorem godementCompactPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    godementCompactPullbackNatTrans (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      godementCompactPullbackNatTrans g hg ≫ godementCompactPullbackNatTrans f hf := by
  calc
    _ = coefficientCompactNatTrans (R := R) (g.inducedMap.comp f.inducedMap)
        (fun k x => by
          change g.inducedMap (f.inducedMap (k • x)) =
            k • g.inducedMap (f.inducedMap x)
          rw [f.inducedMap_smul, g.inducedMap_smul]) (hg.comp hf) :=
      coefficientCompactNatTrans_congr _ _ _ _ (SheafVariation.inducedMap_comp_eq f g)
    _ = _ := coefficientCompactNatTrans_comp
      f.inducedMap f.inducedMap_smul g.inducedMap g.inducedMap_smul hf hg

/-- The actual all-degree map on the already constructed smooth Godement
cohomology is homology of the compact chain pullback. -/
def godementCohomologyPullbackNatTrans (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (q : ℕ) :
    godementCompactCohomology (R := R) Y q ⟶ godementCompactCohomology X q :=
  Functor.whiskerRight (godementCompactPullbackNatTrans f hf)
    (homologyFunctor (SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q)

/-- Every cohomology component is the image of the constructed chain map. -/
theorem godementCohomologyPullbackNatTrans_app (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) (M : SmoothRep.{u, u, u} R G) :
    (godementCohomologyPullbackNatTrans f hf q).app M =
      (homologyFunctor (SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map
        ((godementCompactPullbackNatTrans f hf).app M) := rfl

@[reassoc]
theorem godementCohomologyPullbackNatTrans_naturality (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (godementCompactCohomology Y q).map a ≫
        (godementCohomologyPullbackNatTrans f hf q).app N =
      (godementCohomologyPullbackNatTrans f hf q).app M ≫
        (godementCompactCohomology X q).map a :=
  (godementCohomologyPullbackNatTrans f hf q).naturality a

@[simp]
theorem godementCohomologyPullbackNatTrans_id (q : ℕ) :
    godementCohomologyPullbackNatTrans (R := R) (𝟙 X) (isProperMap_inducedMap_id X) q =
      𝟙 (godementCompactCohomology X q) := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map _ = 𝟙 _
  rw [godementCompactPullbackNatTrans_id]
  exact (homologyFunctor (SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map_id _

/-- Proper rational transport composes contravariantly in every cohomology degree. -/
theorem godementCohomologyPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) (q : ℕ) :
    godementCohomologyPullbackNatTrans (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) q =
      godementCohomologyPullbackNatTrans g hg q ≫
        godementCohomologyPullbackNatTrans f hf q := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [godementCompactPullbackNatTrans_comp f g hf hg]
  exact Functor.map_comp _ _ _

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
