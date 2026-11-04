import Langlands.GroupScheme.IdentityComponent
import Mathlib.AlgebraicGeometry.ResidueField

/-! # The all-test relative identity-component criterion

The residue fibres are actual group-scheme pullbacks. Membership is the fibre-image
condition of SGA 3, VI_B, Definition 3.1. The representation predicate specifies an
open subgroup with precisely these points; it does not assert its existence.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)

namespace RelativeIdentityComponent

/-- The actual group scheme over the residue field of a point of the base. -/
abbrev residueFiber (s : S) : GroupScheme (Spec (S.residueField s)) :=
  (GroupScheme.baseChange (S.fromSpecResidueField s)).obj G

/-- The pullback of an arbitrary test point to the residue field of a base point. -/
abbrev residueFiberPoint {T : Over S} (x : T ⟶ G.X) (s : S) :
    (Over.pullback (S.fromSpecResidueField s)).obj T ⟶ (residueFiber G s).X :=
  (Over.pullback (S.fromSpecResidueField s)).map x

end RelativeIdentityComponent

/-- A point on any test scheme belongs to the relative identity component when
its image in every residue fibre lies in the connected component of the identity. -/
def InRelativeIdentityComponent {T : Over S} (x : T ⟶ G.X) : Prop :=
  ∀ s : S, Set.range (RelativeIdentityComponent.residueFiberPoint G x s).left ⊆
    IdentityComponent.identitySet (RelativeIdentityComponent.residueFiber G s)

/-- The relative identity-component condition is preserved by restricting a test point. -/
theorem InRelativeIdentityComponent.precomp {T U : Over S} {x : T ⟶ G.X}
    (hx : InRelativeIdentityComponent G x) (a : U ⟶ T) :
    InRelativeIdentityComponent G (a ≫ x) := by
  intro s y hy
  rcases hy with ⟨z, rfl⟩
  change ((Over.pullback (S.fromSpecResidueField s)).map (a ≫ x)).left z ∈ _
  rw [Functor.map_comp, Over.comp_left, Scheme.Hom.comp_apply]
  exact hx s ⟨_, rfl⟩

/-- An actual open subgroup represents the relative identity component if
factorization through it agrees, on all test schemes, with the fibre-image criterion. -/
structure IsRelativeIdentityComponent {H : GroupScheme S} (i : H ⟶ G) : Prop where
  isOpenImmersion : IsOpenImmersion i.hom.hom.left
  factors_iff : ∀ (T : Over S) (x : T ⟶ G.X),
    (∃ y : T ⟶ H.X, y ≫ i.hom.hom = x) ↔ InRelativeIdentityComponent G x

end Langlands.GroupScheme
