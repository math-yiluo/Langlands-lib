# Generic relative Jacquet comparison and heads

This file states a derived GL_n version of the constituent-restricted argument
in Silberger's Lemma 5.3 and the generic head argument in Lemma 5.5. It contains
proposition definitions, not proofs. The all-regular tempered case of Lemma 5.6,
relative recovery in Propositions 5.7–5.8, and cosocle multiplicities in
Proposition 5.9 remain separate obligations.

## Actual data and normalization

The quantifiers range over every prime, finite extension `F` of Q_p, compatible
local-field realization `T`, positive rank `n`, ordered block shape `B`, and
actual refinement `S` of its blocks. Write `C = B.flatten S`, `G = GL_n(F)`,
`L = B.Levi F`, and `M = refinedLevi F B S`. The constructed
`flattenedLeviEquiv F B S : C.Levi F ≃* M` identifies the fine product with the
actual subgroup of `L`. No arbitrary equivalence or compatibility certificate
is an input. Equality of the fine and coarse parabolics is allowed.

The fine representation `ω` is an actual bundled complex representation of
`C.Levi F`. It is assumed irreducible, cuspidal, and unitarizable.
`IsLeviCuspidal` includes admissibility (and hence smoothness) and vanishing of
actual unipotent coinvariants for every proper standard refinement.
`IsUnitarizable` means existence of an invariant positive definite Hermitian
form; it does not impose finite dimension or a chosen carrier topology.

The real vectors `v₀ : Fin C.length → ℝ` and `t : Fin B.length → ℝ` satisfy
`IsRelativeGenericParameter C B v₀ t`. In concrete coordinates, `t` is injective
and every permutation preserving the fine partition and the shifted real
coordinate vector `v₀ - t|C` belongs to the coarse block Weyl group. Neither
strict descending order nor positivity of individual entries is required for
this generic assertion.

`fineTwist T B S ω v₀ t` is the actual representation `τ` of `M` obtained by
multiplying `ω` by

`∏ k |det(m_k)|^(-v₀(k) + t(parent(k)))`

and pulling back along the inverse of `flattenedLeviEquiv`. Here
`parent(k) = ((B.flattenBlockEquiv S).symm k).1`; the absolute value is the
residue-normalized `q^(-valuation)`. Silberger's source character
`+i(v₀ - v'')` therefore corresponds to these negative fine and positive coarse
determinant exponents. The stabilizer predicate uses the opposite real vector,
which has exactly the same stabilizer.

`innerInduced` bundles the actual normalized upper induction `I_M^L(τ)`;
`CuspidalJacquetMultiplicity.induced T B μ` is `I_L^G(μ)`. Both use right
translation and positive-half-modulus covariance. `innerJacquet` is the actual
normalized opposite Jacquet module `r_(op M)^L(μ)`, and `ambientJacquet` is
`r_(op M)^G(I_L^G(μ))` using the composed opposite radical. Both are actions of
the same actual refined subgroup. Their normalization is the inverse half of
the opposite full modulus, equivalently the positive half of the corresponding
upper full modulus. These four bundlers merely share existing constructions
and their carrier instances; they introduce no new intrinsic mathematical law.

## Proposition definitions

`GLRelativeGenericJacquetMultiplicityStatement` quantifies over every actual
irreducible admissible representation `μ` of `L` that is a subquotient of
`I_M^L(τ)`. This restriction is explicit: there must be an invariant subspace
`U` of that induced representation and an actual surjective intertwiner from
`U` to `μ`. The conclusion supplies a natural number `m` with

* `HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m`;
* `HasJordanHolderMultiplicity (ambientJacquet T B S μ) τ m`;
* `0 < m` if and only if an actual surjective intertwiner `I_M^L(τ) → μ` exists.

Each multiplicity predicate supplies an actual finite composition series with
exactly `m` factors equivalent to `τ`. Thus existence of composition series is
part of the conclusion; equality is not encoded as an equivalence that could
hold merely because both series predicates fail. Jordan–Hölder independence
is a proof dependency.

`GLRelativeGenericHeadStatement` uses the same fine data and generic parameter,
and assumes instead that the irreducible admissible `μ` is a quotient of
`I_M^L(τ)` via an actual surjective intertwiner. It concludes
`HasIrreducibleHead (I_L^G(μ))`: existence of an irreducible quotient and equality
of the kernels of all irreducible quotient maps. This is uniqueness as a
quotient object, stronger than uniqueness of the target isomorphism class.
Existence of an outer irreducible quotient is a conclusion, not an input.

`GLRelativeGenericComparisonStatement` is the conjunction of those two
proposition definitions. The independent universes `uF`, `uV`, and `uW` belong
to the field, fine representation, and coarse constituent. The inner induced
carrier is in `max uF uV`; the outer induced carrier is in `max uF uW`.
Subquotient and quotient witnesses allow these differing carrier universes.
The head predicate tests all quotient targets in the universe of its source,
as in the existing canonical-head definition.

## Original source and precise derived scope

A. J. Silberger, *The Langlands Quotient Theorem for p-adic Groups*,
Mathematische Annalen **236** (1978), 95–104: setup and genericity on p.99;
Lemma 5.3 and its complete summation proof on p.100; Lemma 5.5 on pp.100–101.
The retained original is `literature/Silberger (1978), The Langlands quotient
theorem for p-adic groups.pdf`, registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 19 read the entire article and reread these original pages, including
the p.100 formula image. No retained erratum was located.

The unrestricted printed Lemma 5.3 has a GL₂ obstruction documented in
[the published scope audit](../../../notes/jacquet/silberger-lemma53-scope.md).
Its last proof paragraph only establishes the comparison for components of
the specified inner induction. This file retains precisely that restriction;
it does not assert the unrestricted Lemma 5.3 or Corollary 5.4.

The arbitrary `v₀` in this file is an explicitly derived generalization of the
p.99 setup, not a transcription that silently omits its intermediate
discrete-series support and positive-root condition. The generic summation
argument uses the following facts:

1. Opposite reciprocity gives an occurrence of `μ` in the opposite Jacquet
   module of `I_L^G(μ)`. Exactness and transitivity therefore give the
   constituentwise multiplicity inequality `a(μ) ≤ b(μ)`.
2. Apply this inequality to a composition series of `I_M^L(τ)`. Exactness and
   induction in stages express the sum of the `a(μ)` and the sum of the
   `b(μ)`, counted with constituent multiplicity, as the inner and ambient
   cuspidal-induced Jacquet multiplicities of `τ`.
3. The cuspidal Weyl formula counts the stabilizer of the inducing class.
   Unitarity of `ω` implies that a Weyl equivalence of its real twist preserves
   the real determinant-exponent vector. Genericity forces that stabilizer
   into the coarse Levi Weyl group, so the two total counts coincide.
4. Nonnegative differences with equal finite totals vanish for each actual
   constituent of the inner induction. Opposite reciprocity and the
   fixed-central-exponent projectivity input identify positivity with being
   an inner quotient.

These steps use no intermediate discrete-series representation, no positive
root expansion of `v₀`, and no choice of regular chamber for `t`. They justify
the stated derived scope, subject to formal proofs of the listed inputs. The
p.100 final equality that removes the coarse twist is unnecessary for this
comparison: both sides here retain the same `τ`. The intermediate support and
tempered-exponent/continuation argument of p.101 are needed for the later
all-regular statement and are not removed from that separate obligation.

For Lemma 5.5, distinct irreducible quotient kernels would give a surjection
onto the direct sum of two irreducible quotients, even if their targets are
isomorphic. Reciprocity embeds `μ` in the opposite coarse Jacquet of each
quotient; exactness and transitivity then force the ambient multiplicity to be
at least twice the positive inner multiplicity, contradicting the comparison.
Finite length and nonvanishing of the actual induced representation supply
existence of an irreducible quotient. This explains the kernel-unique head
conclusion without assuming a canonical quotient or using unrestricted
Corollary 5.4.

## Remaining proof obligations

The statement uses the published actual functors, flattened-Levi equivalence,
real twists, cuspidality and composition-series predicates. A proof must supply
normalized induction in stages and opposite Jacquet transitivity with the
actual modulus identities, exactness and finite length, the cuspidal Weyl
multiplicity formula inside product Levis as well as in GL_n, invariance and
additivity of Jordan–Hölder multiplicities, unitary central-character control
of real twists, and the appropriate opposite reciprocity and
fixed-central-exponent extraction/projectivity arguments. An adjunction for
maps *into* upper induction alone does not establish all the needed maps out
of it. The source's transitive citations are not imported as Lean proofs by
this statement. Neither generic head existence nor any relative recovery,
all-regular continuation, or final exhaustion theorem is proved here.
