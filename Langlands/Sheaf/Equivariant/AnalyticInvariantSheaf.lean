import Langlands.Sheaf.Equivariant.NaturalActionSheaf
import Langlands.Sheaf.Equivariant.AnalyticInvariantPresheaf
import Langlands.Sheaf.ImagePullbackContinuity

/-!
# The sheaf of invariant sections `(b_*F)^G` on `X(G)_qét` and `X(G)_ét`

Let `X` be a `G`-space. Suppose that the forgetful functor `Qét(X(G)) → Qét(X)` has image
pullbacks: every cospan of `Qét(X(G))` has a commutative square over it which becomes a
fibre product in `Qét(X)`. Berkovich (proof of Theorem 1.4.2) uses fibre products of
`G`-spaces with the diagonal action for this. Then the forgetful functor is continuous, so
`b : X → X(G)` is a morphism of sites. The presheaf `V(G) ↦ F(V)^G` of invariant sections
is then a sheaf on `X(G)_qét`: Berkovich's sheaf `(b_*F)^G`. Its value at `X(G)` is
`Γ_{X(G)}(F)`. The same holds for `Ét(X(G))` under the analogous hypothesis.

The image pullback hypotheses are not proved here.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology
open Langlands.Sheaf (HasImagePullbacks)

universe u v uL z uR w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G] (X : GSpace.{u, v, v} K G)

section QuasiEtale

/-- If the forgetful functor `Qét(X(G)) → Qét(X)` has image pullbacks, it is continuous. -/
theorem toQuasiEtaleSite_isContinuous
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).IsContinuous
      (equivariantQuasiEtaleTopology X) (quasiEtaleTopology X.obj.V) :=
  hX.isContinuous _ _ fun _ _ h => h

/-- If the forgetful functor `Qét(X(G)) → Qét(X)` has image pullbacks, then
`Qét(X(G)) → ` twisted quasi-étale site of `X` is continuous. -/
theorem quasiEtaleToTwisted_isContinuous
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    (quasiEtaleToTwisted X).IsContinuous (equivariantQuasiEtaleTopology X)
      (twistedQuasiEtaleTopology X.obj.ρAut) :=
  have := toQuasiEtaleSite_isContinuous X hX
  Functor.isContinuous_comp _ _ _ (quasiEtaleTopology X.obj.V) _

variable (R : Type uR) [CommRing R]

/-- Berkovich's sheaf `(b_*F)^G : V(G) ↦ F(V)^G` on `X(G)_qét` of invariant sections of
module sheaves on the twisted quasi-étale site, assuming image pullbacks. -/
def quasiEtaleInvariantSheaf
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤
      Sheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{w} R) :=
  have := quasiEtaleToTwisted_isContinuous X hX
  (quasiEtaleNaturalAction X).sheafInvariantSheafFunctor R
    (twistedQuasiEtaleTopology X.obj.ρAut) (equivariantQuasiEtaleTopology X)

/-- The underlying presheaf of `(b_*F)^G` is the presheaf of invariant sections. -/
def quasiEtaleInvariantSheafCompIso
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    quasiEtaleInvariantSheaf X R hX ⋙
        sheafToPresheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{w} R) ≅
      quasiEtaleInvariantPresheaf X R :=
  have := quasiEtaleToTwisted_isContinuous X hX
  (quasiEtaleNaturalAction X).sheafInvariantSheafFunctorCompIso R
    (twistedQuasiEtaleTopology X.obj.ρAut) (equivariantQuasiEtaleTopology X)

/-- The sheaf `(b_*F)^G` is left exact in the sheaf `F`. -/
instance quasiEtaleInvariantSheaf_preservesFiniteLimits
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    PreservesFiniteLimits (quasiEtaleInvariantSheaf X R hX :
      Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤ _) :=
  have := quasiEtaleToTwisted_isContinuous X hX
  inferInstanceAs (PreservesFiniteLimits ((quasiEtaleNaturalAction X).sheafInvariantSheafFunctor
    R (twistedQuasiEtaleTopology X.obj.ρAut) (equivariantQuasiEtaleTopology X)))

/-- The sheaf `(b_*F)^G` on `X(G)_qét` for quasi-étale `G`-sheaves `F`. -/
def quasiEtaleGSheafInvariantSheaf
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤
      Sheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{w} R) :=
  (compactLiftSystem X.obj.ρAut).discreteSheafInclusion _ _ ⋙ quasiEtaleInvariantSheaf X R hX

variable [HasSheafify (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R)]
variable [(compactLiftSystem X.obj.ρAut).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology X.obj.ρAut)]

/-- The sheaf `(b_*F)^G` is left exact on quasi-étale `G`-sheaves. -/
instance quasiEtaleGSheafInvariantSheaf_preservesFiniteLimits
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    PreservesFiniteLimits (quasiEtaleGSheafInvariantSheaf X R hX :
      QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ _) :=
  comp_preservesFiniteLimits _ _

end QuasiEtale

section QuasiEtaleBase

variable [IsTopologicalGroup G] (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The value at `X(G)` of the sheaf `(b_*F)^G` of a quasi-étale `G`-sheaf `F` is
Berkovich's `Γ_{X(G)}(F)`. -/
def quasiEtaleGSheafInvariantSheafBaseIso
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    quasiEtaleGSheafInvariantSheaf X R hX ⋙
        sheafToPresheaf (equivariantQuasiEtaleTopology X)
          (ModuleCat.{max u (v + 1) uL} R) ⋙
        (CategoryTheory.evaluation (EquivariantQuasiEtaleSite X)ᵒᵖ
          (ModuleCat.{max u (v + 1) uL} R)).obj (op (equivariantQuasiEtaleBase X)) ≅
      quasiEtaleGSheafInvariantSections.{u, v, uL} X.obj.ρAut R :=
  quasiEtaleGSheafInvariantPresheafBaseIso X R

end QuasiEtaleBase

section Etale

/-- If the forgetful functor `Ét(X(G)) → Ét(X)` has image pullbacks, it is continuous. -/
theorem toEtaleSite_isContinuous
    (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    (EquivariantEtaleSite.toEtaleSite X).IsContinuous
      (equivariantEtaleTopology X) (etaleTopology X.obj.V) :=
  hX.isContinuous _ _ fun _ _ h =>
    map_toEtaleSite_mem_etalePrecoverage_iff.2 h

/-- If the forgetful functor `Ét(X(G)) → Ét(X)` has image pullbacks, then
`Ét(X(G)) → ` twisted étale site of `X` is continuous. -/
theorem etaleToTwisted_isContinuous
    (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    (etaleToTwisted X).IsContinuous (equivariantEtaleTopology X)
      (twistedEtaleTopology X.obj.ρAut) :=
  have := toEtaleSite_isContinuous X hX
  Functor.isContinuous_comp _ _ _ (etaleTopology X.obj.V) _

variable (R : Type uR) [CommRing R]

/-- Berkovich's sheaf `(b_*F)^G : V(G) ↦ F(V)^G` on `X(G)_ét` of invariant sections of
module sheaves on the twisted étale site, assuming image pullbacks. -/
def etaleInvariantSheaf (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤
      Sheaf (equivariantEtaleTopology X) (ModuleCat.{w} R) :=
  have := etaleToTwisted_isContinuous X hX
  (etaleNaturalAction X).sheafInvariantSheafFunctor R
    (twistedEtaleTopology X.obj.ρAut) (equivariantEtaleTopology X)

/-- The underlying presheaf of `(b_*F)^G` is the presheaf of invariant sections. -/
def etaleInvariantSheafCompIso (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    etaleInvariantSheaf X R hX ⋙
        sheafToPresheaf (equivariantEtaleTopology X)
          (ModuleCat.{w} R) ≅
      etaleInvariantPresheaf X R :=
  have := etaleToTwisted_isContinuous X hX
  (etaleNaturalAction X).sheafInvariantSheafFunctorCompIso R
    (twistedEtaleTopology X.obj.ρAut) (equivariantEtaleTopology X)

/-- The sheaf `(b_*F)^G` is left exact in the sheaf `F`. -/
instance etaleInvariantSheaf_preservesFiniteLimits
    (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    PreservesFiniteLimits (etaleInvariantSheaf X R hX :
      Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤ _) :=
  have := etaleToTwisted_isContinuous X hX
  inferInstanceAs (PreservesFiniteLimits ((etaleNaturalAction X).sheafInvariantSheafFunctor
    R (twistedEtaleTopology X.obj.ρAut) (equivariantEtaleTopology X)))

/-- The sheaf `(b_*F)^G` on `X(G)_ét` for étale `G`-sheaves `F`. -/
def etaleGSheafInvariantSheaf (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    EtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤
      Sheaf (equivariantEtaleTopology X) (ModuleCat.{w} R) :=
  (distinguishedLiftSystem X.obj.ρAut).smoothSheafInclusion _ _ ⋙ etaleInvariantSheaf X R hX

variable [HasSheafify (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{w} R)]
variable [(distinguishedLiftSystem X.obj.ρAut).HasAdmissibleRefinements
  (twistedEtaleTopology X.obj.ρAut)]

/-- The sheaf `(b_*F)^G` is left exact on étale `G`-sheaves. -/
instance etaleGSheafInvariantSheaf_preservesFiniteLimits
    (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    PreservesFiniteLimits (etaleGSheafInvariantSheaf X R hX :
      EtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ _) :=
  have : PreservesFiniteLimits ((distinguishedLiftSystem X.obj.ρAut).smoothSheafInclusion
      (ModuleCat.{w} R) (twistedEtaleTopology X.obj.ρAut)) := inferInstance
  comp_preservesFiniteLimits _ _

end Etale

section EtaleBase

variable [IsTopologicalGroup G] (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The value at `X(G)` of the sheaf `(b_*F)^G` of an étale `G`-sheaf `F` is Berkovich's
`Γ_{X(G)}(F)`. -/
def etaleGSheafInvariantSheafBaseIso
    (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    etaleGSheafInvariantSheaf X R hX ⋙
        sheafToPresheaf (equivariantEtaleTopology X)
          (ModuleCat.{max u (v + 1) uL} R) ⋙
        (CategoryTheory.evaluation (EquivariantEtaleSite X)ᵒᵖ
          (ModuleCat.{max u (v + 1) uL} R)).obj (op (equivariantEtaleBase X)) ≅
      etaleGSheafInvariantSections.{u, v, uL} X.obj.ρAut R :=
  etaleGSheafInvariantPresheafBaseIso X R

end EtaleBase

end Langlands.Sheaf.Equivariant.Analytic
