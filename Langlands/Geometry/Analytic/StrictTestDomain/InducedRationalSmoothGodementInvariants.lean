import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothGodementTransport
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalInvariantComplex
import Langlands.Cohomology.SmoothGodement.CoefficientInvariants

/-! # Invariant compact Godement pullback on actual induced rational spectra -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory HomologicalComplex Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementCohomology
open Langlands.Cohomology.SmoothGodementCohomology.Spatial
open Langlands.Cohomology.SmoothGodementComparison

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.SmoothCohomology

variable (X : ρ.OpenSubgroupTransport) [HasStableNeighbourhoods G X.InducedSpectrum]

/-- The constructed invariant complex is the degreewise invariants of the
existing compact smooth Godement complex. -/
def godementInvariantCompactComplexIso :
    godementCompactComplex (R := R) X ⋙
        (smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      godementInvariantCompactComplex X :=
  Functor.isoWhiskerLeft (sheafFunctor X)
    (smoothGodementInvariantCompactComplexIso R G X.InducedSpectrum)

end OpenSubgroupTransport.SmoothCohomology

namespace OpenSubgroupTransport.Hom

open SmoothCohomology

variable {X Y Z : ρ.OpenSubgroupTransport}
  [HasStableNeighbourhoods G X.InducedSpectrum]
  [HasStableNeighbourhoods G Y.InducedSpectrum]
  [HasStableNeighbourhoods G Z.InducedSpectrum]

/-- Pull back the actual invariant compact smooth Godement complexes of the full
coefficient sheaves along a proper induced rational transport map. -/
def godementInvariantCompactPullbackNatTrans (f : X ⟶ Y) (hf : IsProperMap f.inducedMap) :
    godementInvariantCompactComplex (R := R) Y ⟶ godementInvariantCompactComplex X :=
  coefficientInvariantCompactNatTrans f.inducedMap f.inducedMap_smul hf

/-- The component resolves the original coefficient sheaf pullback before
applying the actual proper spatial chain map. -/
theorem godementInvariantCompactPullbackNatTrans_app (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G) :
    (godementInvariantCompactPullbackNatTrans f hf).app M =
      (Langlands.Cohomology.SmoothGodementCohomology.smoothGodementInvariantCompactComplex
          R G Y.InducedSpectrum).map
        (SmoothDirectImage.coefficientMap f.inducedMap f.inducedMap_smul M) ≫
      invariantCompactMap f.inducedMap f.inducedMap_smul hf ((sheafFunctor X).obj M) := rfl

/-- The coefficient map is exactly degreewise invariants of the existing
compact smooth Godement pullback. -/
theorem godementInvariantCompactPullbackNatTrans_app_eq_map (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G) :
    (godementInvariantCompactPullbackNatTrans f hf).app M =
      ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((godementCompactPullbackNatTrans f hf).app M) :=
  coefficientInvariantCompactNatTrans_app_eq_map f.inducedMap f.inducedMap_smul hf M

/-- Each term restricts the actual compact chain map to invariant submodules. -/
@[simp]
theorem godementInvariantCompactPullbackNatTrans_f (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G) (n : ℕ) :
    ((godementInvariantCompactPullbackNatTrans f hf).app M).f n =
      (smoothInvariants R G).map
        (((godementCompactPullbackNatTrans f hf).app M).f n) :=
  coefficientInvariantCompactNatTrans_f f.inducedMap f.inducedMap_smul hf M n

/-- Forgetting the invariant witness gives the original compact chain map. -/
@[simp]
theorem godementInvariantCompactPullbackNatTrans_apply (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (M : SmoothRep.{u, u, u} R G) (n : ℕ)
    (s : ((godementInvariantCompactComplex Y).obj M).X n) :
    ((((godementInvariantCompactPullbackNatTrans f hf).app M).f n).hom s).val =
      SmoothRep.hom (((godementCompactPullbackNatTrans f hf).app M).f n) s.val :=
  coefficientInvariantCompactNatTrans_apply f.inducedMap f.inducedMap_smul hf M n s

/-- The actual complex comparison commutes with proper rational pullback. -/
@[reassoc]
theorem godementInvariantCompactPullbackNatTrans_comparison (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) :
    Functor.whiskerRight (godementCompactPullbackNatTrans (R := R) f hf)
        ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)) ≫
        (godementInvariantCompactComplexIso X).hom =
      (godementInvariantCompactComplexIso Y).hom ≫
        godementInvariantCompactPullbackNatTrans f hf := by
  apply NatTrans.ext
  funext M
  ext n s
  rfl

/-- All original coefficient intertwiners commute with the chain pullback. -/
@[reassoc]
theorem godementInvariantCompactPullbackNatTrans_naturality (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (godementInvariantCompactComplex Y).map a ≫ (godementInvariantCompactPullbackNatTrans f hf).app N =
      (godementInvariantCompactPullbackNatTrans f hf).app M ≫
        (godementInvariantCompactComplex X).map a :=
  (godementInvariantCompactPullbackNatTrans f hf).naturality a

@[simp]
theorem godementInvariantCompactPullbackNatTrans_id :
    godementInvariantCompactPullbackNatTrans (R := R) (𝟙 X) (isProperMap_inducedMap_id X) =
      𝟙 (godementInvariantCompactComplex X) := by
  exact (coefficientInvariantCompactNatTrans_congr
    (inducedMap_smul (𝟙 X)) (fun (_ : G) (_ : X.InducedSpectrum) => rfl)
    (isProperMap_inducedMap_id X) isProperMap_id (SheafVariation.inducedMap_id_eq X)).trans
      coefficientInvariantCompactNatTrans_id

/-- The actual proper rational transport maps give strict contravariant
chain maps, without an assumed inverse to any lax comparison. -/
theorem godementInvariantCompactPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    godementInvariantCompactPullbackNatTrans (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) =
      godementInvariantCompactPullbackNatTrans g hg ≫ godementInvariantCompactPullbackNatTrans f hf := by
  calc
    _ = coefficientInvariantCompactNatTrans (R := R) (g.inducedMap.comp f.inducedMap)
        (fun k x => by
          change g.inducedMap (f.inducedMap (k • x)) =
            k • g.inducedMap (f.inducedMap x)
          rw [f.inducedMap_smul, g.inducedMap_smul]) (hg.comp hf) :=
      coefficientInvariantCompactNatTrans_congr _ _ _ _ (SheafVariation.inducedMap_comp_eq f g)
    _ = _ := coefficientInvariantCompactNatTrans_comp
      f.inducedMap f.inducedMap_smul g.inducedMap g.inducedMap_smul hf hg

/-- The actual all-degree map on invariant compact Godement
cohomology takes module homology after invariants of the compact chain pullback. -/
def godementInvariantCohomologyPullbackNatTrans (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (q : ℕ) :
    godementInvariantCompactCohomology (R := R) Y q ⟶ godementInvariantCompactCohomology X q :=
  Functor.whiskerRight (godementInvariantCompactPullbackNatTrans f hf)
    (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q)

/-- Every cohomology component is the image of the constructed chain map. -/
theorem godementInvariantCohomologyPullbackNatTrans_app (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) (M : SmoothRep.{u, u, u} R G) :
    (godementInvariantCohomologyPullbackNatTrans f hf q).app M =
      (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
        ((godementInvariantCompactPullbackNatTrans f hf).app M) := rfl

@[reassoc]
theorem godementInvariantCohomologyPullbackNatTrans_naturality (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) {M N : SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (godementInvariantCompactCohomology Y q).map a ≫
        (godementInvariantCohomologyPullbackNatTrans f hf q).app N =
      (godementInvariantCohomologyPullbackNatTrans f hf q).app M ≫
        (godementInvariantCompactCohomology X q).map a :=
  (godementInvariantCohomologyPullbackNatTrans f hf q).naturality a

@[simp]
theorem godementInvariantCohomologyPullbackNatTrans_id (q : ℕ) :
    godementInvariantCohomologyPullbackNatTrans (R := R) (𝟙 X) (isProperMap_inducedMap_id X) q =
      𝟙 (godementInvariantCompactCohomology X q) := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map _ = 𝟙 _
  rw [godementInvariantCompactPullbackNatTrans_id]
  exact (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map_id _

/-- Proper rational transport composes contravariantly in every cohomology degree. -/
theorem godementInvariantCohomologyPullbackNatTrans_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) (q : ℕ) :
    godementInvariantCohomologyPullbackNatTrans (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) q =
      godementInvariantCohomologyPullbackNatTrans g hg q ≫
        godementInvariantCohomologyPullbackNatTrans f hf q := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map _ = _
  rw [godementInvariantCompactPullbackNatTrans_comp f g hf hg]
  exact Functor.map_comp _ _ _

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
