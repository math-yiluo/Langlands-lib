import Langlands.Geometry.Building.KPLocalMoyPrasadGroupProperties
import Langlands.GroupScheme.Rational.StandardParabolic

/-!
# Positive-depth sign product cover over the maximal unramified field

The constant-positive-depth torus-filtration variant of KP Lemma 7.3.11 and
Proposition 7.3.12, for the actual generated groups `BuildingData.moyPrasad`.
Only the explicit commutator clause of KP Definition 7.2.1 is assumed.
This module states the conditional product cover; it does not prove it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The actual positive-depth Moy–Prasad group over `K = F^ur` is the set product
of its negative root-filtration span, its torus-depth image and its positive
root-filtration span, assuming only the explicit local commutator clause. -/
def LocalMoyPrasadPositiveProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffineHom H.X.hom]
    (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z),
    (∀ (x : B.Apartment) (a : relativeRoots B.i) (u u' : rationalPoints H),
      u ∈ B.rootGroup a.1 → u ≠ 1 → u' ∈ B.rootGroup (-a.1) → u' ≠ 1 →
      ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
      ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
        v' ∈ B.rootGroup (-a.1) → v ∈ B.rootGroup a.1 →
        u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
        z ∈ B.centralizerTorusFiltration hZ r) →
    ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r →
      ∀ mu : cocharacterLattice B.S, IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H))

end Langlands.Geometry.Building.MaximalUnramified
