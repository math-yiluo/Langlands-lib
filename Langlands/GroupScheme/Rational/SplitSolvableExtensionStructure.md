# Structure of the canonical extension of a split solvable group

Author: Worker 755.

This module identifies the kernel and the quotient of the extension in
`SplitSolvableExtensionSectionsStatement` (module
[`SplitSolvableSectionsStatement`](../SplitSolvableSectionsStatement.md)).
It is a helper for [`SplitSolvableSectionsProof`](../SplitSolvableSectionsProof.md)
and introduces no definition from the literature.

## Two general lemmas

Over an arbitrary base scheme `S`:

- `kernelι_comp_eq_zero_of_range_le`: for homomorphisms `q : G ⟶ Q` and
  `q' : G ⟶ Q'` with `range (kernelι q) ≤ range (kernelι q')` (on every test
  scheme), `kernelι q ≫ q' = 0`. Check on the generic point of the kernel
  with `mem_range_kernelι_iff`.
- `fppfQuotientIso` (definition): if `q` and `q'` are flat, surjective and
  locally of finite presentation on schemes, and their scheme kernels have
  the same range, then `Q ≅ Q'`. The two maps are the descents
  `FppfHomDescent.hom q q'` and `FppfHomDescent.hom q' q` (module
  [`FppfHomDescent`](../FppfHomDescent.md)), and both composites are
  identities by the uniqueness part `FppfHomDescent.unique`.

## The structure theorem

`IsSplitSolvableGroupScheme.canonicalExtension_structure`: let `k` be a
field, `G` a group scheme over `Spec k` with `IsSplitSolvableGroupScheme G`,
`i : U ⟶ G` a closed subgroup with `IsUnipotent U`, `q : G ⟶ D` with
`RelativeRoot.IsFppfQuotient (range i) q`, and `IsMultiplicativeType D`.
Then there are `U'` and `i' : U' ⟶ G` with `IsClosedSubgroup i'`, `U'`
smooth and connected, `IsUnipotent U'`, `RelativeRoot.IsSplitUnipotent U'`
and `range i' = range i`; moreover `IsSplitTorus D`. Normality of
`range i` is not needed.

Proof.

1. `G` is smooth, affine and connected, and has a pointed split-torus
   domination by `IsSplitSolvableGroupScheme.hasPointedSplitTorusDomination`
   (module [`SplitSolvableTorusDomination`](SplitSolvableTorusDomination.md)).
   The Library's `splitTorusDominatedSolvableQuotient` then gives a closed
   subgroup `i' : U' ⟶ G`, smooth, connected and unipotent, and an fppf
   quotient `q' : G ⟶ D'` by `range i'` with `IsTorus D'`.
2. `range i ≤ range i'`: for a point `y` of `U`, `y ≫ i ≫ q'` is trivial
   because a homomorphism from a unipotent group to a torus is trivial
   (`IsUnipotent.comp_eq_one_of_isTorus`), so `i(y)` lies in the kernel of
   `q'`, whose range is `range i'`.
3. `range i' ≤ range i`: the homomorphism `i' ≫ q` from the unipotent `U'`
   to the multiplicative-type `D` has trivial range by the Library's
   `unipotentMultiplicativeTriviality` (part 3), so `i'(y)` lies in the
   kernel of `q`, whose range is `range i`.
4. Hence the kernels of `q` and `q'` have the same range, and
   `fppfQuotientIso q q'` gives `D ≅ D'`, so `D` is a torus
   (`IsTorus.of_iso`).
5. `U'` is split unipotent by the Library's
   `TorusKernelDomination.representative_isSplitUnipotent_of_stableVector`,
   applied with the published `unipotentSplitTorusDomination` and
   `RelativeRoot.splitUnipotentStableVectorSubgroup`.
6. The domination of `G` pushed forward along the dominant `q`
   (`HasPointedSplitTorusDomination.postcomp`) dominates the torus `D`, so
   `D` is split (`HasPointedSplitTorusDomination.isSplitTorus`).
