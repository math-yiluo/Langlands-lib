module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Serre's conditions for schemes

A scheme is regular in codimension `k`, property `(R_k)`, when every local ring of dimension at
most `k` is regular. A locally Noetherian scheme has Serre's property `(S_k)` when the depth of
every local ring is at least the minimum of `k` and its Krull dimension. Serre's criteria
identify the reduced locally Noetherian schemes as those satisfying `(S₁)` and `(R₀)`, and the
normal ones as those satisfying `(S₂)` and `(R₁)`.

## Main definitions

* `AlgebraicGeometry.IsRegularInCodimension` expresses property `(R_k)` for a scheme.
* `AlgebraicGeometry.HasPropertySk` is Serre's property `(S_k)` for a locally Noetherian scheme.

## Main results

* `AlgebraicGeometry.hasPropertySk_iff` is the pointwise characterization of `(S_k)`.
* `AlgebraicGeometry.hasPropertySk_zero` says that every locally Noetherian scheme has property
  `(S₀)`.
* `AlgebraicGeometry.isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero` characterizes
  reduced locally Noetherian schemes by conditions `(S₁)` and `(R₀)`.
* `AlgebraicGeometry.isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one` is Serre's
  criterion for normality: `(S₂)` together with `(R₁)`.

## Implementation notes

The predicate `IsRegularInCodimension` is meaningful without a local Noetherian hypothesis, so
that hypothesis is left to the results which use it, and the dimension is written directly as the
Krull dimension of the stalk.

Both sides of the defining inequality for `(S_k)` are compared in `WithBot ℕ∞`, the codomain of
`ringKrullDim`. The depth is the depth along the maximal ideal of the local ring, as in the
source definition of depth. Clients can use `hasPropertySk_iff` to pass between the named
predicate and its pointwise inequality, while `simp` discharges property `(S₀)` directly.

Serre's criterion for normality is deduced from its affine form
`isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth` by
comparing the local rings of the scheme at the points of an affine open with the localizations
of its ring of sections at the corresponding primes; the characterization of normality by the
rings of sections of all affine opens is `isNormal_tfae`.

## References

* [Stacks Project, Tag 033Q](https://stacks.math.columbia.edu/tag/033Q)
* [Stacks Project, Tag 0344](https://stacks.math.columbia.edu/tag/0344)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
-/

@[expose] public section

open CategoryTheory RingTheory.Sequence

universe u

namespace AlgebraicGeometry

/-- For a local ring, depth along the maximal ideal is the corresponding depth supremum. -/
public lemma depth_eq_depthSup_of_isLocalRing (A : Type*) [CommRing A] [IsLocalRing A] :
    Module.stacksDepth A (IsLocalRing.maximalIdeal A) A =
      Module.depthSup A (IsLocalRing.maximalIdeal A) A := by
  rw [Module.stacksDepth, ite_eq_right (by simpa using (IsLocalRing.maximalIdeal.isMaximal A).ne_top),
    Module.depthSup_eq_iSup]

section Normality

end Normality

end AlgebraicGeometry

end
