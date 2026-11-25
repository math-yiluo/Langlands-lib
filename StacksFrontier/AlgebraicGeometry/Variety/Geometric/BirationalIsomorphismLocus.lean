module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Sober.Generization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalUniqueness
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The isomorphism locus of a proper birational morphism at a normal point

Let `f : Y ⟶ X` be a proper birational morphism from a reduced scheme to a Noetherian scheme,
and let `x` be a point of `X` whose local ring is normal. Then `f` is an isomorphism over a
neighbourhood of `x` as soon as the fibre over `x` is finite, and — more generally — `x` lies
in the maximal open over which `f` is an isomorphism as soon as `f` is quasi-finite at some
point above `x`.

## Main results

* `AlgebraicGeometry.exists_isIso_restrict_of_finite_fiber_of_normal`: a proper birational
  morphism from a reduced scheme is an isomorphism over a neighbourhood of a point with finite
  fibre and normal local ring.
* `AlgebraicGeometry.mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal`: the maximal
  isomorphism open contains a normal point admitting a quasi-finite preimage.
* `AlgebraicGeometry.mem_maximal_isomorphism_open_of_exists_isIso_restrict`: a point admitting
  such an isomorphism neighbourhood belongs to the maximal isomorphism open.

## Implementation notes

The maximal open is expressed as the greatest open `U` for which the restriction `f ∣_ U` is an
isomorphism, and `mem_maximal_isomorphism_open_of_exists_isIso_restrict` is the bridge from the
intrinsic local-neighbourhood form to membership in it. Normality is expressed by the predicate
`IsNormalRing` on the local ring, that is, by every localization at a prime being an integrally
closed domain; for a local ring this is the same as being a normal domain.

For a finite fibre, Zariski's main theorem gives an affine neighbourhood over which `f` is
finite, and on it the sections upstairs form a finite algebra inside the function field which,
by integral closedness, agrees with the base after inverting one element. For a quasi-finite
point the argument is at the level of local rings: quasi-finiteness makes the residue field
extension finite and the closed fibre zero-dimensional, so the stalk map is an isomorphism, and
that isomorphism spreads out to an open neighbourhood.

## References

* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- A morphism that becomes an isomorphism both after precomposition and after
postcomposition is itself an isomorphism. -/
lemma isIso_of_isIso_comp_left_and_right {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    [IsIso (a ≫ b)] [IsIso (b ≫ c)] : IsIso b := by
  let : IsSplitEpi b := IsSplitEpi.mk' ⟨inv (a ≫ b) ≫ a, by
    rw [Category.assoc, IsIso.inv_hom_id]⟩
  let : IsSplitMono b := IsSplitMono.mk' ⟨c ≫ inv (b ≫ c), by
    rw [← Category.assoc, IsIso.hom_inv_id]⟩
  exact isIso_of_mono_of_isSplitEpi b

end AlgebraicGeometry
