import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.GroupScheme.Rational.ValuedBoundedProducts

/-! # Algebraic boundedness under restriction between split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private instance restrictedBoundsAffine {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable {k : Type u} [Field k] [ValuativeRel k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [Mono i.hom.hom.left] {φ : RootFunctionFamily T G}

/-- An ordered product of finitely many bounded actual root filtrations is bounded. -/
theorem isAlgebraicallyBounded_orderedRootFiltrationProduct
    (hφ : IsRootDatumValuation i φ) {n : ℕ}
    (a : Fin n → characterLattice T) (d : Fin n → ℝ)
    (hB : ∀ j, IsAlgebraicallyBounded k G.X (rootFiltration i φ (a j) (d j))) :
    IsAlgebraicallyBounded k G.X (orderedRootFiltrationProduct i φ a d) := by
  exact isAlgebraicallyBounded_range_orderedProduct_of_finiteType
    (fun j => hφ.filtrationSubgroup (a j) (d j)) hB

variable [Smooth G.X.hom]

/-- Multiplier-scaled boundedness of the upper root filtrations bounds the
actual restricted subgroup at the prescribed depth. -/
theorem isAlgebraicallyBounded_torusRestrictedRootDepthSubgroup
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (hα : α ≠ 0) (r : ℝ)
    (hB : ∀ a ∈ relativeRoots i, ∀ m : ℕ, 0 < m →
      IsAlgebraicallyBounded k G.X (rootFiltration i φ a (m * r))) :
    IsAlgebraicallyBounded k G.X
      (torusRestrictedRootDepthSubgroup hφ f α r : Set (rationalPoints G)) := by
  obtain ⟨n, a, m, _, hrange, hm⟩ :=
    exists_torusRestrictionRootDepth_enumeration (i := i) hT f α
  rw [← orderedRootFiltrationProduct_eq_torusRestrictedRootDepthSubgroup
    hS hT hE hφ f α hα r a m hrange (fun j => (hm j).2)]
  exact isAlgebraicallyBounded_orderedRootFiltrationProduct hφ a _
    (fun j => hB (a j) (hrange ▸ Set.mem_range_self j).1 (m j) (hm j).1)

/-- Restriction between split tori preserves algebraic boundedness of every
zero-depth filtration when it is known for the upper root family. -/
theorem isAlgebraicallyBounded_zeroRootFiltration_torusRestrict
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T)
    (hB : ∀ a ∈ relativeRoots i,
      IsAlgebraicallyBounded k G.X (rootFiltration i φ a 0))
    (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) :
    IsAlgebraicallyBounded k G.X
      (rootFiltration (CommGroupScheme.groupHom f ≫ i)
        (torusRestrictedRootFunctionFamily hS hT hE hφ f) α 0) := by
  rw [rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f α hα 0]
  apply isAlgebraicallyBounded_torusRestrictedRootDepthSubgroup hS hT hE hφ f α hα.1 0
  intro a ha m _
  simpa only [mul_zero] using hB a ha

/-- Generic zero-depth boundedness transport for the canonical restriction
of an actual valued root family between split tori. -/
def TorusRestrictedZeroRootFiltrationBoundedStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (S T : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth G.X.hom] [Mono i.hom.hom.left]
    (φ : RootFunctionFamily T G)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T),
    (∀ a ∈ relativeRoots i,
      IsAlgebraicallyBounded k G.X (rootFiltration i φ a 0)) →
    ∀ α : characterLattice S,
      α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i) →
      IsAlgebraicallyBounded k G.X
        (rootFiltration (CommGroupScheme.groupHom f ≫ i)
          (torusRestrictedRootFunctionFamily hS hT hE hφ f) α 0)

/-- Finite ordered products establish the transport statement. -/
theorem torusRestrictedZeroRootFiltrationBounded :
    TorusRestrictedZeroRootFiltrationBoundedStatement.{u} := by
  intro k _ _ S T G i _ _ _ _ φ hS hT hE hφ f hB α hα
  exact isAlgebraicallyBounded_zeroRootFiltration_torusRestrict hS hT hE hφ f hB α hα

end Langlands.Geometry.Building
