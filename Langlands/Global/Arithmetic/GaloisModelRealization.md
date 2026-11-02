# Totally real realization from a global Galois model

This module supplies the global descent and completion comparison used in
totally real realization. Its main theorem,
`Langlands.Global.FieldRealization.totallyRealRealization_of_galoisModel`,
starts with the actual supplied p-adic Galois extension `E/F`, a finite
Galois extension `Ω/Padic p` containing `E` through a compatible scalar tower,
and a totally real rational Galois number field `N : Type 0`. A ring
embedding `ι : N →+* Ω` must have image generating `Ω` over `Padic p`.
The theorem then supplies every clause of the realization conclusion for
`F,E`, with their canonical topologies. It does not construct the input
number field, ambient local extension or generating embedding.

## Preimages and generation

The algebraic construction uses an algebra structure `N → Ω`; the final
theorem obtains this structure from `ι.toAlgebra`. For an intermediate field
`X` of `Ω/Padic p`, `modelPreimage p X` is the inverse image of `X` in `N`,
as an intermediate field of `N/ℚ`. The restriction homomorphism
`restrictModel` sends local automorphisms of `Ω/Padic p` to rational
automorphisms of `N`. Rational normality of `N` makes this restriction
well-defined. Generation by `N` makes it injective.

The lemma `exists_restrictModel_eq` uses Galois correspondence to show that
every rational automorphism fixing the preimage of `X` is the restriction
of an automorphism fixing `X`. More explicitly, the fixed field of the
image of `X.fixingSubgroup` is contained in the preimage of `X`, which
puts the given automorphism in that image. The lemma
`adjoin_image_modelPreimage` combines this extension property with
injectivity of restriction to prove that the preimage generates precisely
`X` over the p-adic scalars.

For a field `A` embedded in `Ω`, `modelField p Ω N A` specializes that
preimage to the image of `A`. Its elements are exactly those elements
of `N` whose image in `Ω` comes from `A`. The definition `modelEmbedding`
factors their inclusion through the injective map `A → Ω`. This uses
the auxiliary `factorRingHom`, together with its exact factorization
equation. The corresponding generation results hold for these embeddings.

Set `K := modelField p Ω N F`. The inclusion of the image of `F` in
the image of `E` gives an inclusion of their preimages. The definition
`topModel p Ω N F E` expresses the preimage of `E` as an intermediate
field of `N/K`; call its carrier `L`. Thus both `K,L` are number fields
in `Type 0` when `N` is. Their embeddings `baseEmbedding : K →+* F` and
`topEmbedding : L →+* E` commute with the supplied map `F → E`, as
proved by `topEmbedding_algebraMap`.

## Galois groups and degree

The lemmas `exists_localCompat` and `exists_modelCompat` show that the
relation

\[
\tau(j_L(y))=j_L(\sigma(y))\qquad(y\in L)
\]

is total in both directions, for `σ ∈ Gal(L/K)` and `τ ∈ Gal(E/F)`.
For the first direction, lift `σ` to the normal rational model, use the
restriction extension property, and restrict the resulting local
automorphism to the normal extension `E/F`. For the other direction,
lift `τ` to `Ω`, restrict to `N`, and then restrict to its preimage of
`E`; this restriction fixes the preimage of `F`.

Generation of `E` by the image of `L` gives uniqueness on the local side.
Injectivity of `L → E` gives uniqueness on the global side. The relation
respects multiplication, so `exists_mulEquiv_of_rel` packages it into
the group equivalence `exists_galoisEquiv`, with the displayed action
compatibility.

An element of `L` fixed by every global automorphism has image in `E`
fixed by every local automorphism. Since `E/F` is Galois, that image
comes from `F`, placing the original element in `K`. The lemma
`isGalois_topModel` uses this fixed-field characterization to prove that
`L/K` is Galois. The lemma `finrank_topModel` then compares both
degrees through the orders of their automorphism groups. Total reality
of both model fields follows from their embeddings in the totally real
field `N`.

## Density, primes and completions

The lemma `denseRange_of_adjoin_eq_top` proves that a characteristic-zero
field embedding with generating image in a normed p-adic algebra is
dense. Its image closure contains all rational scalars, hence all
p-adic scalars by density of the rationals. The closure is therefore
a p-adic subalgebra containing the generating image, so it is the
whole target.

The theorem `exists_completionData` first assumes complete nontrivial
ultrametric norms on `F,E`, compatible with their p-adic structures.
It also assumes that `F → E` preserves the norm and that every element
of `Gal(E/F)` preserves the norm on `E`. The preceding density result
lets `DenseCompletionComparison.exists_adicCompletion_ringEquiv` construct
actual primes `vK,wL` and actual adic-completion ring equivalences to
`F,E`, continuous in both directions. Membership in either prime is
characterized by the corresponding embedded algebraic integer having
norm less than one.

The commuting embedding equation and norm compatibility show that `wL`
lies over `vK`. The global/local action comparison transfers norm
invariance to the global embedding of `L`. The imported lemma
`prime_unique_of_norm_invariant` then proves that every prime over `vK`
equals `wL`. The equations extending the original dense embeddings give
both the base-field diagram and the required Galois action equation on
every element of `L`.

## Spectral norms and the specified topologies

The intermediate theorem `exists_realization` constructs the required
norms using the spectral norm on each finite extension of `Padic p`.
The auxiliary existential lemmas `exists_spectralNormedField` and
`exists_spectralNormedAlgebra` retain equality with the supplied field
and algebra structures. The spectral norm gives compatible normed
algebras, complete ultrametric field structures, preservation of norm
along `F → E`, and invariance under the supplied local automorphisms.
It therefore supplies all hypotheses of `exists_completionData`.

Finite-dimensional normed p-adic spaces have their module topologies.
The proof uses this equality to transport the four continuity conclusions
to `moduleTopology (Padic p) F` and `moduleTopology (Padic p) E`.
These are definitionally the `canonicalTopology` values of the supplied
`PadicField` objects. No equality between the numerical normalization of
an adic valuation and the spectral norm is required. The final theorem
installs the algebra structure from the ring embedding and applies
`exists_realization`; its ambient field and its two local carriers may
lie in independent universes.

## Provenance and authorship

This is an internal derived construction. Henniart (2000), Section 3.3,
printed page 449 (PDF page 11), motivates the totally real global fields,
the local identifications respecting the given extension, and the Galois
comparison. Henniart (1984), Lemma 3.6, printed pages 34–35 (PDF pages
35–36), motivates passage from an approximation model to global fields
with full decomposition group. Here the implemented descent uses
preimages in a rational normal model and Galois correspondence, followed
by explicit dense-completion comparison. It is not an assertion that
those sources contain the precise definitions or the implemented proof.
The exact source registrations and correspondence are in
`FieldRealizationStatement.md`. This module imports the established
prime and completion constructions and does not assume the realization
statement it is intended to support.

Worker 785 authored the Lean descent, Galois and spectral-norm comparison.
Worker 37 prepared this Markdown from that implementation and checked its
composition with the normal-closure model; both workers contributed to
the imported norm-invariant prime construction.
