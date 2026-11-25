import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.IntegralModel.AffineWeilPoints
import Langlands.GroupScheme.Examples.SU3RootParametersTowerValuation
import Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates

/-! # Valued scheme-level unitary coordinates of multipliable root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme.SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- The unitary parameter group `U_{L/k}` is affine: it is the corepresenting bilinear
coordinate group of the canonical chart. -/
instance unitaryParameterGroup_isAffine : IsAffine (unitaryParameterGroup k L).X.left := by
  change IsAffine (BilinearCoordinate.groupScheme (CommRingCat.of k)
    (canonicalCoordinateData.{u, u, u} k L).coeff).X.left
  let := BilinearCoordinate.isAffineHom (CommRingCat.of k)
    (canonicalCoordinateData.{u, u, u} k L).coeff
  exact isAffine_of_isAffineHom (BilinearCoordinate.groupScheme (CommRingCat.of k)
    (canonicalCoordinateData.{u, u, u} k L).coeff).X.hom

/-- The unitary parameter group `U_{L/k}` is of finite type over `k`. -/
instance unitaryParameterGroup_locallyOfFiniteType :
    LocallyOfFiniteType (unitaryParameterGroup k L).X.hom := by
  change LocallyOfFiniteType (BilinearCoordinate.groupScheme (CommRingCat.of k)
    (canonicalCoordinateData.{u, u, u} k L).coeff).X.hom
  exact BilinearCoordinate.locallyOfFiniteType (CommRingCat.of k)
    (canonicalCoordinateData.{u, u, u} k L).coeff

end Langlands.GroupScheme.SU3Root

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom G.X.hom]

attribute [local instance 1100] Module.Free.of_divisionRing in
/-- **Valued scheme-level unitary coordinates of a root group.** For building data `B` over
the maximal unramified field `K = inertiaFixedField F` and a character `b` of the maximal split
torus, this records a finite separable extension `E / K` (the field of definition of the double
root), a separable quadratic extension `L / E` (the field of definition of the root), and an
actual homomorphism of `K`-group schemes from the Weil restriction `R_{E/K} U_{L/E}` of the
unitary parameter group into `G` which represents the root subgroup `U_b`. On rational points
the coordinates are the parameters `(u, v) ∈ L²` with `v + σ(v) = u σ(u)`. The record also
gives a point `origin` of the apartment at which the value of `b` on the coordinate point of
`(u, v)` is `ω(v) / 2`, for `ω` the unique extension to `L` of the valuation of `K` normalized
by `ω(K^×) = ℤ` (`SU3Root.towerDepth`).

This is the scheme-level form of the quasi-split description of a multipliable root group:
the isomorphism `R_{k_b̃/k} U_{k_ã/k_b̃} → U_a` of Kaletha–Prasad, *Bruhat–Tits theory: a new
approach*, Construction 2.9.16, display (2.9.3), together with the unshifted Chevalley
valuation `φ_a((u, v)) = ω(v) / 2` of Construction 6.1.17 (a point of the apartment by
Proposition 6.1.19). The record only requires a homomorphism representing the root subgroup;
it does not itself assert existence. -/
structure ValuedUnitaryRootGroupCoordinates (B : MaximalUnramified.BuildingData F G)
    (b : characterLattice B.S) where
  /-- The field of definition `E` of the double root. -/
  base : Type u
  /-- The field of definition `L` of the root. -/
  extension : Type u
  [baseField : Field base]
  [field : Field extension]
  [baseAlgebra : Algebra (inertiaFixedField F) base]
  [quadraticAlgebra : Algebra base extension]
  [algebra : Algebra (inertiaFixedField F) extension]
  [scalarTower : IsScalarTower (inertiaFixedField F) base extension]
  [baseFinite : FiniteDimensional (inertiaFixedField F) base]
  [baseSeparable : Algebra.IsSeparable (inertiaFixedField F) base]
  [quadratic : Algebra.IsQuadraticExtension base extension]
  [quadraticSeparable : Algebra.IsSeparable base extension]
  [separable : Algebra.IsSeparable (inertiaFixedField F) extension]
  /-- The actual homomorphism `R_{E/K} U_{L/E} → G`. -/
  inclusion : AffineWeil.groupScheme (inertiaFixedField F) base
      (SU3Root.unitaryParameterGroup base extension) ⟶ G
  /-- It represents the root subgroup `U_b`. -/
  isRootSubgroup : (RelativeRoot.subgroup B.i b).IsRepresentedBy inclusion
  /-- A point of the apartment normalizing the coordinates. -/
  origin : B.Apartment
  /-- At `origin`, the value of `b` on the coordinate point of `(u, v)` is `ω(v) / 2`. -/
  depth : ∀ p : SU3Root.rationalParameters base extension,
    origin.val b (rationalPoints.map inclusion
        ((AffineWeil.sectionsEquiv (inertiaFixedField F) base
          (SU3Root.unitaryParameterGroup base extension)).symm
          ((SU3Root.unitaryRationalPointsEquiv base extension).symm p))) =
      SU3Root.towerDepth (inertiaFixedField F) base extension (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) p

attribute [instance] ValuedUnitaryRootGroupCoordinates.baseField
  ValuedUnitaryRootGroupCoordinates.field ValuedUnitaryRootGroupCoordinates.baseAlgebra
  ValuedUnitaryRootGroupCoordinates.quadraticAlgebra ValuedUnitaryRootGroupCoordinates.algebra
  ValuedUnitaryRootGroupCoordinates.scalarTower ValuedUnitaryRootGroupCoordinates.baseFinite
  ValuedUnitaryRootGroupCoordinates.baseSeparable ValuedUnitaryRootGroupCoordinates.quadratic
  ValuedUnitaryRootGroupCoordinates.quadraticSeparable
  ValuedUnitaryRootGroupCoordinates.separable

/-- **Existence of valued unitary root-group coordinates.** For every nonarchimedean local
field `F`, every affine group scheme `G` over the maximal unramified field with supplied
building data `B`, and every relative root `b` whose double `2 • b` is again a relative root,
the root group `U_b` admits valued scheme-level unitary coordinates. -/
def MultipliableRootGroupCoordinatesExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (B : MaximalUnramified.BuildingData F G)
    (b : relativeRoots B.i),
    2 • (b : characterLattice B.S) ∈ relativeRoots B.i →
      Nonempty (ValuedUnitaryRootGroupCoordinates B b)

end Langlands.Geometry.Building
