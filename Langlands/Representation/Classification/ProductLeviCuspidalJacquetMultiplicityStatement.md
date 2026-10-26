# Opposite cuspidal Jacquet multiplicities inside a product Levi

Author: Worker 165.

`Langlands.ProductLeviCuspidalJacquetMultiplicityStatement` is a proposition
about the full opposite self-Jacquet module of normalized cuspidal induction
inside an actual product Levi. It is a derived specialization of the original
cuspidal Weyl-factor formulas below. This file states the result; it does not
prove the representation-theoretic formula or its transport and reindexing.

## Actual representations and scope

For every prime `p`, finite extension `F : PadicField.{uF} p`, supplied compatible
topological data `T`, positive rank `n`, block shape `B : BlockShape n`, and
refinement `S : BlockRefinement B`, put `C = B.flatten S`. Let `σ` be an
irreducible cuspidal representation of the actual product `C.Levi F.Carrier`
on a complex vector space in universe `uV`.

Here `IsLeviCuspidal C σ` includes admissibility, hence smoothness, and
vanishing of actual unipotent coinvariants for every proper standard
refinement. Irreducibility is a separate hypothesis. No external tensor
factorization of `σ` is assumed.

The constructed equivalence

```text
e = flattenedLeviEquiv F.Carrier B S
  : C.Levi F.Carrier ≃* refinedLevi F.Carrier B S
```

identifies the fine product with the actual subgroup of `B.Levi F.Carrier`.
Transport the action by `σ.comp e.symm.toMonoidHom`, induce it using
`T.normalizedRefinedInduced B S`, and apply
`T.normalizedRefinedOppositeJacquet B S`. The bundled result is `J` in the
Lean proposition. All intermediate `Rep.of` expressions retain the actual
carriers, additive groups, modules and actions; they only share dependent
expressions. There are no new construction definitions or supplied group
identifications.

For every irreducible `τ` of `C.Levi F.Carrier` on an independently quantified
complex vector space in universe `uW`, the comparison representation is
`Rep.of (τ.comp e.symm.toMonoidHom)`, using exactly the same equivalence.
The universes `uF`, `uV`, and `uW` are independent. The induced function space
and its quotient have universe `max uF uV`; equivalences to the comparison
representation are permitted across carrier universes.

## Full length and exact multiplicity

The first conclusion is `HasCompositionSeriesLength J L`, where

```text
L = Nat.card {w : MinimalConjugatingPermutations C C //
                w.val.val ∈ blockWeyl B}.
```

This supplies an actual finite filtration from zero to the whole module,
with irreducible successive quotients. It concerns the full opposite Jacquet
module, with no tempered-part restriction.

For every irreducible `τ` and every natural number `m`, the second conclusion is

```text
HasJordanHolderMultiplicity J (Rep.of (τ.comp e.symm.toMonoidHom)) m
  ↔ m = Nat.card {w : AssociatingPermutations C C σ τ //
                     w.val.val.val ∈ blockWeyl B}.
```

The multiplicity predicate supplies an actual composition series with exactly
`m` factors equivalent to the comparison representation. The biconditional
asserts existence at the prescribed count and rules out all other counts.
Repeated isomorphic factors are counted separately, and the count may be
zero. No semisimplicity or multiplicity-one claim is made.

Both indexing types are literal finite subtypes of the published permutation
constructions. `MinimalConjugatingPermutations C C` already requires the
minimal positive-root conditions and conjugation of the entire embedded
fine Levi to itself. `AssociatingPermutations C C σ τ` adds actual equivalence
of the inverse-conjugation transport of `σ` to `τ`. Its additional subtype
layer explains the three `.val` projections in the multiplicity formula.
The field parameter in the length count is the actual `F.Carrier`; in the
multiplicity count it is inferred from `σ` and `τ`.

## Why this is the internal Weyl index

The coarse group is `B.Levi`, whose Weyl permutations are precisely
`blockWeyl B`: they preserve every coarse block. Each fine block of
`C = B.flatten S` lies within a coarse block, as expressed by the published
`B.flatten_index S`. Consequently the fine Weyl group `blockWeyl C` is a
subgroup of `blockWeyl B`.

The published `IsMinimalRepresentative C C w` asks that `w` be strictly
increasing on every fine source block and that `w.symm` be strictly increasing
on every fine target block. It does not ask for monotonicity on whole coarse
blocks. Restricted to `blockWeyl B`, these are exactly the positive-root
conditions for the fine Levi inside the product of the coarse general linear
groups.

The published `CuspidalSupport.minimalConjugatingCosets` gives, for a conjugating
permutation `w`, a unique minimal conjugating representative `v` with
`w = v * b`, where `b ∈ blockWeyl C`. If `w ∈ blockWeyl B`, then
`v = w * b⁻¹` also lies in `blockWeyl B`. Thus restricting to the coarse Weyl
group retains exactly one representative of each internal right fine-Weyl
coset. It excludes permutations exchanging different coarse blocks, even
when their sizes agree. It also removes the redundant permutations inside
individual fine blocks. This explains the literal restriction used here;
a formal proof of the restricted parametrization is required in the proof
successor, not assumed as data in the proposition.

The embedding identity `flattenedLeviEquiv_embedding` identifies the
fine-Levi action with its actual ambient matrix embedding. For a coarse-block
preserving permutation, its ambient permutation matrix lies in the coarse
Levi (`CuspidalSupport.permutation_mem_levi_iff`). The proof successor must
use these facts to identify the internal conjugation action with
`CuspidalSupport.transport C C`, including the inverse in that action, and
to transport irreducibility, filtrations and multiplicities through `e`.
For the opposite target, the required parabolic conjugation and reindexing
must be performed inside the coarse blocks. No opposite transport or
reindexing certificate is a hypothesis here.

## Normalization

`normalizedRefinedInduced` uses the actual smooth covariant functions with
right translation and the positive half of the upper refined full modulus.
`normalizedRefinedOppositeJacquet` takes coinvariants by the actual opposite
refined unipotent subgroup. Its full modulus is the inverse of the upper
refined modulus, so its normalizing scalar is the positive half of the upper
modulus. This is the published opposite quotient construction, not an upper
quotient with a substituted scalar.

No genericity, unitarity, chamber or positivity condition, outer ambient
Jacquet comparison, Langlands quotient theorem, supplied composition series,
or tensor decomposition occurs among the hypotheses. Only the opposite
self-Levi family is stated; general target refinements and nonassociated
vanishing are outside its scope.

## Original sources and derived provenance

The following registered originals were read at the stated locations, and
the displayed formulas were checked in rendered page images. No errata note
for these sources was present in the supplied Library.

- Allan J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
  Groups* (1979), Theorem 5.4.1.1, printed pp.287–288, PDF pp.293–294.
  Literature ID `silberger-1979-harmonic-analysis`; SHA-256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
  For cuspidal input, the theorem gives the full finite composition length
  equal to the relative Weyl group order and the character sum of the
  Weyl-transformed inputs, with the displayed half-modulus. Its two
  parabolics have a common Levi. The bracketed discrete-series version uses
  the maximal tempered part and is not used here.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups. I* (1977), Corollary 2.13(c) and §2.15(3), printed p.449,
  PDF p.10. Literature ID `bernstein-zelevinsky-1977-induced-i`; SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  The corollary supplies the associated-Levi filtration indexed by the
  right cosets of the source Weyl group in the conjugating permutations.
  Section 2.15(3) identifies constituent multiplicity with the number of
  cosets transporting the input to that constituent.

Apply the general reductive-group cuspidal formulas to the coarse product
of general linear groups `B.Levi`, with its refined parabolic and common
refined Levi. The actual flattened equivalence and the restricted Weyl
parametrization above give the present formulation. It is a derived
product-Levi specialization, not a verbatim theorem from either source.
The published `GLCuspidalJacquetMultiplicityStatement` is the standard
single-general-linear-group analogue and fixes the same length, multiplicity
and normalization conventions; importing a proposition does not prove it.

An exact proof successor must prove this proposition without adding tensor
factorization or relative generic comparison as assumptions. A route through
factorwise formulas would first need proved arbitrary irreducible-Levi tensor
factorization and compatibility of the actual functors. A route through the
geometric lemma must reuse the existing associated-filtration work, establish
the product-Levi and opposite transport, and count its irreducible factors
using Jordan–Hölder independence. These obligations remain open in this pair.
