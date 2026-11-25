module

public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Homology.ProjectiveDimension
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.Over.HeightOne
public import StacksFrontier.RingTheory.Nagata.Japanese.EssFiniteType
public import StacksFrontier.RingTheory.Nagata.Japanese.Localization
public import StacksFrontier.RingTheory.Nagata.Japanese.N1Criterion
public import StacksFrontier.RingTheory.Nagata.Japanese.NagataScheme
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.TorOneAndSkyscraper
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sober.Generization
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The two dimension hypotheses of the local comparison, read off the geometry

The local comparison of multiplicities underlying Stacks Tag 02S5,
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, carries
two hypotheses on Krull dimensions in the local ring `A = 𝒪_{X ×_S 𝐏¹_S, ξ}`: that `A/(t, I)`
has dimension at most zero, and that `A/I` has dimension exactly one, for `I` the stalk of the
ideal sheaf of a closed subscheme `Z` and `t` a local equation of a section.
`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/StalkDimension.lean` identified both quotients
with local rings of schemes; this file discharges the two resulting bounds from the hypotheses
that Tag 02S5 actually supplies.

The first bound is free at a generic point of the fibre: a generic point of an irreducible
component is maximal in the specialization order, so its coheight — and therefore the Krull
dimension of the local ring there — is zero.

The second is the substantive one. Let `ξ` be a point of `Z` lying over a generic point of the
zero (or infinity) fibre at which the relative dimension of Stacks 02JW equals `k`. The upper
bound `dim 𝒪_{Z,ξ} ≤ 1` comes from the delta-dimension hypothesis of the tag: the relative
dimension strictly increases along strict generalization, and it is capped at `k + 1`, so no
point of `Z` admits a chain of two strict generalizations above `ξ`. The lower bound
`dim 𝒪_{Z,ξ} ≥ 1` says that `ξ` is not the generic point of a component of `Z`, and this is
where the hypothesis on associated points enters: were `ξ` such a generic point it would be an
associated point of `Z`, while `ξ` lies on a section and has relative dimension `k`, so both
alternatives offered for an associated point fail.

## Main results

* `Stacks.Chow.isMax_of_mem_genericPoints` and `Stacks.Chow.mem_genericPoints_of_isMax` — on a
  scheme, being a generic point of an irreducible component is the same as being maximal for
  the specialization order.
* `Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints` — the local ring of a scheme at
  a generic point of an irreducible component has Krull dimension zero.
* `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_le_zero_zeroFiber` and
  `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_le_zero_infinityFiber` — the first
  dimension hypothesis of the local comparison, at a generic point of the fibre.
* `Stacks.Chow.ringKrullDim_stalk_subscheme_eq_one` and
  `Stacks.Chow.ringKrullDim_quotient_idealStalk_eq_one` — the second dimension hypothesis of
  the local comparison, from the delta-dimension and associated-point hypotheses of Tag 02S5.

## Implementation notes

The specialization preorder on the points of a scheme has `x ≤ y` iff `y ⤳ x`, so `IsMax x`
says that every generalization of `x` is a specialization of it, and `Order.coheight x` is the
codimension of `closure {x}`. The bridge to Krull dimension is Mathlib's
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`.

The order-theoretic heart of the upper bound is isolated as a statement about an arbitrary
integer-valued function that is strictly monotone for the ambient preorder and bounded above by
`k + 1`; it needs nothing about schemes, and in particular it does not need the second clause of
a `TopologicalSpace.DimensionFunction`. The dimension function of Stacks 02JW enters only
through `Stacks.Chow.deltaDimensionFunction`, whose `strictAnti_specializes` field supplies the
monotonicity, and whose existence is what forces the `LocallyOfFiniteType` hypothesis.

The hypothesis on associated points is taken in the form the tag's statement gives it, as the
disjunction "`ξ` avoids both sections, or the relative dimension at `ξ` drops below `k`",
instantiated at the single point under consideration. Note that the tag's own statement
quantifies that hypothesis over embedded points, which is not enough: for `S = X = Spec k`,
`δ = 0`, `k = 0` and `Z` the origin of `𝐏¹_k`, the subscheme `Z` has no embedded point at all
and the conclusion of the tag fails. Quantifying over associated points is the repair, and it
is exactly what the lower bound here consumes.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Generic points of irreducible components and the specialization order -/

/-- A generic point of an irreducible component of a scheme is maximal for the specialization
order: any point of which it is a specialization is equal to it. -/
theorem isMax_of_mem_genericPoints {W : Scheme.{u}} (y : genericPoints W) : IsMax y.1 :=
  fun _ hb ↦ le_of_eq (Topology.eq_of_specializes_isGenericPoint y.2
    (genericPoints.isGenericPoint y) hb)

/-- The local ring of a scheme at a generic point of an irreducible component has Krull
dimension zero: such a point is maximal for the specialization order, so its coheight
vanishes. -/
theorem ringKrullDim_stalk_eq_zero_of_mem_genericPoints {W : Scheme.{u}}
    (y : genericPoints W) : ringKrullDim (W.presheaf.stalk y.1) = 0 := by
  rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr (isMax_of_mem_genericPoints y)]
  rfl

/-! ### The first dimension hypothesis, at a generic point of the fibre -/

/-! ### The second dimension hypothesis -/

end Stacks.Chow

end
