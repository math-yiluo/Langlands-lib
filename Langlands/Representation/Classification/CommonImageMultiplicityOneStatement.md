# Common-image multiplicity-one criterion

`Langlands.Classification.CommonImageMultiplicityOneStatement` is an internal
abstract criterion for constructing strong irreducible endpoints. Its group
`G`, monoid `H`, smooth carrier, functor-image carrier and test carrier have
the independent universe parameters `uG`, `uH`, `uV`, `uW` and `uT`.

## The proposition

Let `G` be a group with an arbitrary topology and `H` an arbitrary monoid.
Let `F` be an additive functor from complex smooth `G`-representations to
complex `H`-representations which preserves epimorphisms and monomorphisms.
Suppose the images of two actual smooth representations `A` and `B` each
have Jordan–Hölder multiplicity one at the same test representation `τ`.
These multiplicity hypotheses retain actual finite simple-series witnesses.
Suppose also that every actual nonzero surjective map from `A`, and every
actual nonzero injective map into `B`, has a functor-image target or source,
respectively, with a positive finite-series `τ`-count. The detection
hypotheses apply to arbitrary smooth representations in the smooth carrier
universe, without an irreducibility restriction.

For every actual nonzero map `f : A ⟶ B`, the assertion supplies a smooth
representation `P` and actual maps `q : A ⟶ P` and `j : P ⟶ B`. The map `q`
is surjective, `j` is injective, and `f = q ≫ j`. Moreover, `P` is a strong
irreducible head of `A` and a strong irreducible socle of `B`, in the sense
of `IsIrreducibleHead` and `IsIrreducibleSocle` from
`Classification.ConstituentRelations`. The head conclusion includes equality
of the kernels of all irreducible quotient maps of `A`; the socle conclusion
includes equality of the images of all irreducible embeddings into `B`. Both
quantify over irreducible representations on carriers in the smooth carrier
universe. Since `P` is irreducible, the kernel of `q` is the common kernel
and the image of `j` is the common image.

This statement neither assumes ambient finite length nor assumes the
existence of a simple endpoint. It does assume finite simple series and
positive counts for the particular functor images specified above. It
assumes neither that `τ` is irreducible nor that `F` is exact or faithful.
There is no assertion that an arbitrary induction or Jacquet functor
satisfies these hypotheses.

## Why it holds

This module only defines the proposition. The following informal argument
explains why it holds. The separately published proof
`Langlands.Classification.commonImageMultiplicityOne` in
`Classification.CommonImageMultiplicityOneProof` follows this route.

1. Let `I` be the actual image of `f`: its invariant range in `B` with the
   induced smooth action. The range restriction `q : A ⟶ I` is surjective,
   the inclusion `j : I ⟶ B` is injective, and `f = q ≫ j`. Since `f` is
   nonzero, so is `q`.
2. Source-quotient detection applied to `q` gives a positive count for
   `F(I)`. Because `F` preserves epimorphisms, `F(q)` is surjective.
   Surjective multiplicity monotonicity bounds this count by the count one
   on `F(A)`, so `F(I)` has count exactly one.
3. Suppose `I` were not irreducible. Since `I` is nonzero, it would have an
   invariant subrepresentation `S` that is neither zero nor all of `I`.
   Then the inclusion `S ⟶ I ⟶ B` is injective and nonzero, so
   target-subobject detection gives `F(S)` a positive count. The composite
   `A ⟶ I ⟶ I/S` is surjective and nonzero because `S` is proper, so
   source-quotient detection gives `F(I/S)` a positive count.
4. The composite `S ⟶ I ⟶ I/S` is zero. Functoriality and additivity
   (`F` preserves zero maps) make `F(S) ⟶ F(I) ⟶ F(I/S)` zero. Since `F`
   preserves monomorphisms and epimorphisms, the first mapped map is
   injective and the second is surjective.
5. Let `K` be the actual kernel of `F(I) ⟶ F(I/S)`. The short exact
   decomposition `K ⟶ F(I) ⟶ F(I/S)` gives finite-series counts on `K` and
   `F(I/S)` that sum to the count one on `F(I)`. The mapped inclusion
   factors injectively through `K`, so injective monotonicity bounds the
   positive count of `F(S)` by the count of `K`. Uniqueness of counts
   identifies the count of `F(I/S)` with its positive detected count. Two
   positive natural numbers cannot sum to one, a contradiction. Hence `I`
   is irreducible.
6. An actual surjection onto an irreducible representation, or an
   injection from one, is nonzero. So the detection hypotheses give the
   positivity hypotheses of the published multiplicity-one constituent
   criteria (`multiplicityOneHeadCore` and `multiplicityOneSocleCore` in
   `Classification.MultiplicityOneConstituentProof`), with `I` as the
   supplied irreducible endpoint. These criteria give equality of all
   actual irreducible quotient kernels of `A` and of all actual irreducible
   embedding images in `B`. The canonical head-kernel and socle-image
   characterizations then give the strong relations for `I` itself.
   Setting `P = I` keeps the factorization `f = q ≫ j`.

The multiplicity operations used are the actual short-exact decomposition
and monotonicity results for `HasJordanHolderMultiplicity` from
`Filtration.MultiplicityAdditivityProof`. No ambient finite-length theorem
is used.

## Provenance and scope

The provenance is an internal elementary deduction. It supplements the
published `MultiplicityOneConstituentCriterionStatement` and
`SimpleEndpointMultiplicityOneStatement`, which already assume that a
simple endpoint exists; here that existence is derived from the actual
image. No printed theorem is attributed to this abstract assertion. It
reuses only published category, smooth subquotient, constituent and
multiplicity definitions and results. It draws no segment, multisegment,
tempered or analytic classification conclusion.
