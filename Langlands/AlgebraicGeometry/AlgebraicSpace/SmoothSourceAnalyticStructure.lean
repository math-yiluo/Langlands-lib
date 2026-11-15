import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticPointUniqueness

/-! # Varying-dimension analytic structures on all smooth-space rational points -/

noncomputable section

universe u

open CategoryTheory Set Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

/-- Polynomial affine `n`-space is structurally smooth over `Spec K`. -/
theorem affineSpace_smoothOverBase (n : ℕ) :
    SmoothOverBase ((schemeToSpace _).obj (affineSpaceOver K n)) := by
  let := smoothOfRelativeDimension_affineSpace (K := K) n
  exact SmoothOverBase.of_scheme _ (SmoothOfRelativeDimension.smooth n _)

/-- Polynomial affine `n`-space is quasi-separated as an algebraic space. -/
theorem affineSpace_isQuasiSeparated (n : ℕ) :
    IsQuasiSeparated ((schemeToSpace _).obj (affineSpaceOver K n)) :=
  (isSmoothPureDimensional_affineSpace (K := K) n).1.1.1

/-- Polynomial affine `n`-space is locally separated as an algebraic space. -/
theorem affineSpace_isLocallySeparated (n : ℕ) :
    IsLocallySeparated ((schemeToSpace _).obj (affineSpaceOver K n)) :=
  (isSmoothPureDimensional_affineSpace (K := K) n).1.2

namespace DimensionPointAtlas

variable {X : AlgebraicSpace (Spec (CommRingCat.of K))} {hX : SmoothOverBase X}
  (A : DimensionPointAtlas hX)

/-- Analyticity of a map from the original points into a coordinate space `Kᵐ`.
It includes continuity for the original topology and is tested in every chart
of every dimension, on that chart's full target. -/
def AnalyticToModel {m : ℕ} (g : RingPoints K X K → (Fin m → K)) : Prop :=
  letI := etaleChartTopology K X
  Continuous g ∧ ∀ n, ∀ e ∈ A.atlas n, ContDiffOn K ω (g ∘ e.symm) e.target

/-- Analyticity of a map from a coordinate space `Kᵐ` into the original points.
It includes continuity for the original topology and is tested in every chart
of every dimension, on the full preimage of that chart's source. -/
def AnalyticFromModel {m : ℕ} (h : (Fin m → K) → RingPoints K X K) : Prop :=
  letI := etaleChartTopology K X
  Continuous h ∧ ∀ n, ∀ e ∈ A.atlas n, ContDiffOn K ω (e ∘ h) (h ⁻¹' e.source)

end DimensionPointAtlas

variable (K) in
/-- A choice of varying-dimension atlas on the original rational points of every
smooth, quasi-separated, locally separated algebraic space over `Spec K`. The
dimension may vary from point to point; no analytic law is a field. -/
structure DimensionAnalyticStructure where
  /-- The atlas on `X(K)`, for the étale-chart topology. -/
  atlas : ∀ (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : SmoothOverBase X),
    IsQuasiSeparated X → IsLocallySeparated X → DimensionPointAtlas hX

namespace DimensionAnalyticStructure

variable (Φ Ψ : DimensionAnalyticStructure K)

/-- Every atlas of the family has analytic transition maps. -/
def IsAnalytic : Prop :=
  ∀ (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : SmoothOverBase X)
    (hqs : IsQuasiSeparated X) (hls : IsLocallySeparated X),
    (Φ.atlas X hX hqs hls).IsAnalytic

/-- Every morphism of spaces in the class induces an analytic map of actual
rational points, in every pair of source and target charts. -/
def IsFunctorial : Prop :=
  ∀ (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : SmoothOverBase X) (hY : SmoothOverBase Y)
    (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
    (hYqs : IsQuasiSeparated Y) (hYls : IsLocallySeparated Y) (f : X ⟶ Y),
    (Φ.atlas X hX hXqs hXls).AnalyticMap (Φ.atlas Y hY hYqs hYls)
      (RingPoints.map (A := K) f)

/-- Every étale morphism of spaces in the class induces a local analytic
isomorphism of actual rational points, preserving intrinsic dimension. -/
def IsEtaleLocalIso : Prop :=
  ∀ (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : SmoothOverBase X) (hY : SmoothOverBase Y)
    (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
    (hYqs : IsQuasiSeparated Y) (hYls : IsLocallySeparated Y) (f : X ⟶ Y),
    IsEtaleMorphism f →
      (Φ.atlas X hX hXqs hXls).IsLocalAnalyticIso (Φ.atlas Y hY hYqs hYls)
        (RingPoints.map (A := K) f)

/-- Agreement with the scheme case in the normalizing form: on polynomial affine
`n`-space, the actual coordinate map `Aⁿ(K) → Kⁿ` is a bijection that is
analytic in both directions. -/
def AgreesWithAffineSpace : Prop :=
  ∀ n : ℕ, ∃ c : RingPoints K ((schemeToSpace _).obj (affineSpaceOver K n)) K ≃ (Fin n → K),
    (∀ x, c x = affineSpaceCoordinates K n x) ∧
      (Φ.atlas _ (affineSpace_smoothOverBase n) (affineSpace_isQuasiSeparated n)
          (affineSpace_isLocallySeparated n)).AnalyticToModel c ∧
      (Φ.atlas _ (affineSpace_smoothOverBase n) (affineSpace_isQuasiSeparated n)
          (affineSpace_isLocallySeparated n)).AnalyticFromModel c.symm

/-- The conditions of the varying-dimension analytic-manifold assertion. -/
def IsAdmissible : Prop :=
  Φ.IsAnalytic ∧ Φ.IsFunctorial ∧ Φ.IsEtaleLocalIso ∧ Φ.AgreesWithAffineSpace

/-- Two families agree when, on every space of the class, the actual identity of
`X(K)` is analytic in both directions between their atlases. -/
def Equivalent : Prop :=
  ∀ (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : SmoothOverBase X)
    (hqs : IsQuasiSeparated X) (hls : IsLocallySeparated X),
    (Φ.atlas X hX hqs hls).Equivalent (Ψ.atlas X hX hqs hls)

end DimensionAnalyticStructure

namespace AnalyticPointStructure

/-- The family of concrete lifted atlases determined by a pure-dimensional family:
on each space it is `σ.dimensionAtlas`. -/
def dimensionStructure (σ : AnalyticPointStructure K) (hK : IsHenselianValuedField K) :
    DimensionAnalyticStructure K where
  atlas _ hX hqs hls := σ.dimensionAtlas hK hX hqs hls

@[simp]
theorem dimensionStructure_atlas (σ : AnalyticPointStructure K)
    (hK : IsHenselianValuedField K) (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : SmoothOverBase X) (hqs : IsQuasiSeparated X) (hls : IsLocallySeparated X) :
    (σ.dimensionStructure hK).atlas X hX hqs hls = σ.dimensionAtlas hK hX hqs hls :=
  rfl

end AnalyticPointStructure

end Langlands.AlgebraicGeometry.AlgebraicSpace
