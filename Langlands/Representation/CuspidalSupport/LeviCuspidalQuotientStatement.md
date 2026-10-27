# Upper cuspidal quotients of irreducible admissible product-Levi representations

This file contains one proposition definition,
`Langlands.CuspidalSupport.LeviCuspidalQuotientStatement.{uF,uV}`. It states
that every irreducible admissible representation of an actual product Levi of
`GL_n` is the target of an actual surjective intertwiner from the normalized
upper induction, inside that Levi, of an irreducible cuspidal representation
of a refined Levi. It is a statement, not a proof: nothing in this file proves
the quotient theorem.

## Exact scope

The proposition quantifies over

* every prime `p` with `Fact p.Prime`;
* every actual finite extension `F : PadicField.{uF} p` and every supplied
  local-field realization `T : F.TopologicalData`; the statement installs
  `T.topology` on `F.Carrier`, and all smoothness, admissibility and induced
  representations below use that topology;
* every positive rank `n` (`0 < n`) and every ordered block shape
  `D : GeneralLinear.BlockShape n`, so `L = D.Levi F.Carrier` is the actual
  block-diagonal product `GL_{n_1}(F) × … × GL_{n_r}(F)` in the given order;
* every actual bundled complex representation `σ : Rep.{uV} ℂ L`.

The only representation hypotheses are `Representation.IsIrreducible σ.ρ`
(the Mathlib simple-order condition on subrepresentations, so `σ` is nonzero)
and `IsAdmissible σ.ρ` (smoothness and finite-dimensional fixed spaces for
every open subgroup). There is no hypothesis of square-integrability,
temperedness, unitarity or an invariant form, real parameter, selected
critical exponent, Jacquet occurrence, support map, finite-length
presentation, opposite embedding, head theorem or classification.

The conclusion supplies

* an actual refinement `R : Geometric.BlockRefinement D`; write
  `C = D.flatten R` for the flattened fine block shape and
  `M = refinedLevi F.Carrier D R` for the actual refined subgroup of `L`;
* an actual representation `ω : Rep.{max uF uV} ℂ (C.Levi F.Carrier)`;
* `Representation.IsIrreducible ω.ρ` and
  `CuspidalSupport.IsLeviCuspidal C ω.ρ`;
* an actual intertwining map
  `q : I_M^L(τ) → σ.ρ` with `Function.Surjective q`, where
  `τ = RelativeJacquetMultiplicity.fineTwist T D R ω 0 0` and
  `I_M^L(τ)` is `(RelativeJacquetMultiplicity.innerInduced T D R τ).ρ`.

`IsLeviCuspidal C ω.ρ` is the published definition from `LeviDefinitions`:
admissibility of `ω` together with vanishing (subsingleton) of the actual
unipotent coinvariants for every proper standard refinement of `C`. The
refinement `R` may be the unrefined one (each block refined into a single
block). In that case the refined parabolic and the refined Levi `M` are all
of `L` as subgroups, the induction is from the improper parabolic, and the
conclusion amounts to `σ` being a quotient of such an induction from a
cuspidal representation of the (canonically identified) Levi `C.Levi F.Carrier`. The surjection is a genuine quotient map onto the given `σ.ρ`; it is
not replaced by a subquotient relation, an embedding or an equality of
isomorphism classes.

## Normalization

`fineTwist T D R ω v₀ t` multiplies `ω` by the real-power character
`∏ k |det(m_k)|^(-v₀(k) + t(parent(k)))` and pulls the result back along the
inverse of the constructed group isomorphism
`flattenedLeviEquiv F.Carrier D R : C.Levi F.Carrier ≃* M`. Both parameters
here are zero, so the exponent function is `fun k => -0 k + 0 _`, which equals
the zero vector. By `leviRealPowerTwist_zero` the twist is then the identity,
so `τ` is the un-twisted `ω` transported to `M` through
`(flattenedLeviEquiv F.Carrier D R).symm`. This identification is
propositional, not definitional; any proof that builds `ω` from a cuspidal
representation of `M` must perform this rewrite and transport. No arbitrary
equivalence or compatibility certificate appears as data.

`innerInduced T D R τ` bundles `T.normalizedRefinedInduced D R τ.ρ` from
`Geometric.RefinementFunctors`. Its carrier is the space of smooth functions
`f : L → V_τ` (open right stabilizer) relative to the actual upper parabolic
`refinedParabolic F.Carrier D R` (block upper triangular with respect to the
refinement, in each block of `L`), satisfying the
covariance `f(x g) = δ^{1/2}(x) τ(m(x)) f(g)` for `x` in that parabolic, where
`m` is `refinedLeviProjection` and `δ^{1/2}` is the positive half modulus
`T.refinedLeviHalfModulus D R`. The group `L` acts by right translation. This
is the normalized induction `Ind(δ_P^{1/2} ⊗ τ)` of Silberger's p.96
convention, carried out inside the product Levi `L` rather than in `GL_n(F)`.
No substitute induction is introduced.

## Universes

The field universe `uF` and the target carrier universe `uV` are independent.
The target `σ` keeps its original carrier in `uV`. The inducing
representation `ω`, and hence `τ`, lives in the saturated universe
`max uF uV`; `innerInduced` then lands in `max uF (max uF uV) = max uF uV`. The
intertwiner `q` therefore crosses from carrier universe `max uF uV` to `uV`.
The larger inducing universe is deliberate: a natural construction of `ω`
from Jacquet modules, smooth duals or induced spaces of `σ` produces carriers
of size `max uF uV`, so this choice does not force a universe-lowering step.

## Provenance and derived scope

This proposition is a derived foundational interface, not a literal
transcription of a printed result.

* A. J. Silberger, *The Langlands Quotient Theorem for p-adic Groups*,
  Math. Ann. **236** (1978), 95–104; registered as
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
  Printed p.96 fixes `I(P, σ) = Ind_P^G(δ_P^{1/2} σ)` with `σ` lifted
  trivially on the unipotent radical. Printed p.99, in the proof of
  Proposition 5.1, cites [4] Corollary 2.4.2 and Theorem 4.4.4 to assume that
  a discrete-series `σ'` of `M'` occurs as a quotient of
  `I(P ∩ M', σ_{v₀})` with `σ` supercuspidal and `v₀` a positive combination
  of simple roots. That passage motivates the fine cuspidal quotient data
  used downstream.
* A. J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
  Groups* (1979), §2.4 through Corollary 2.4.2, printed pp.90–92 (PDF
  pp.96–98); source `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
  Theorem 2.4.1 and Corollary 2.4.2 give an *embedding* of an irreducible
  admissible `π` into an induced representation from the *opposite*
  parabolic, `π ⊂ Ind_{P̄}^G(δ_{P̄}^{1/2} σ)`, with `σ` supercuspidal. They do
  not literally state the present upper-quotient conclusion.

Worker 276 read these passages in the original (S78 pp.96 and 99 as text;
S79 pp.90–92 as page images). No retained erratum for them was found in the
project or Library notes.

The present statement differs from the sources in three explicitly derived
ways:

1. **Product Levi.** The ambient group is the actual product Levi
   `D.Levi F.Carrier` rather than a connected reductive `G`; the parabolic is
   the refined standard parabolic `refinedParabolic F.Carrier D R` inside it,
   and the cuspidal representation lives on the flattened fine Levi `C`,
   transported to `M` by `flattenedLeviEquiv`.
2. **Upper quotient instead of opposite embedding.** The conclusion is a
   surjection from the *upper* normalized induction, obtained from the
   embedding form by passing to smooth duals (see the expected route below),
   not the opposite-parabolic embedding of S79 Corollary 2.4.2.
3. **Universe specialization.** The inducing carrier is placed in the
   saturated universe `max uF uV` and the target keeps its original
   universe `uV`.

No exponent condition on the cuspidal data is asserted; the p.99 positivity
of `v₀` belongs to the discrete-series argument and is not part of this
generic statement. The unrestricted printed form of S78 Lemma 5.3 is not used
or asserted (see `notes/jacquet/silberger-lemma53-scope.md`).

## Expected proof route and remaining transports

A proof is a separate obligation. One expected route:

1. The smooth contragredient `σ̃` of `σ` is irreducible and admissible
   (admissible duality).
2. Choose a refinement `R` for which the actual refined Jacquet module of
   `σ̃` is nonzero and minimal; it is then cuspidal on `M` and has an
   irreducible cuspidal quotient `ρ`. Frobenius reciprocity for the refined
   upper induction gives an embedding `σ̃ ⊂ I_M^L(ρ)`. This is the product-Levi
   analogue of the published `CuspidalSupport.cuspidalEmbedding` in
   `CuspidalEmbeddingProof`, which treats `GL_n` only.
3. Same-parabolic duality `(I_M^L(ρ))~ ≅ I_M^L(ρ̃)` for normalized refined
   induction (stated in `Parabolic.NaturalInductionDualityStatement` and not
   yet proved) turns the embedding into a surjection
   `I_M^L(ρ̃) → σ̃~`, and admissible reflexivity `σ ≅ σ̃~` gives a surjection
   onto `σ.ρ` itself.
4. Define `ω` from `ρ̃` by transport along `flattenedLeviEquiv`, lift to the
   universe `max uF uV`, prove irreducibility and `IsLeviCuspidal` transfer
   along the equivalence (`isLeviCuspidal_iff_of_equiv`), and identify
   `fineTwist T D R ω 0 0` with the transported `ρ̃` using
   `leviRealPowerTwist_zero`.

An alternative route factors `σ` into actual `GL` factors using
`CuspidalSupport.LeviAdmissibleFactorizationProof`, applies a `GL_n` result
to each factor, and reassembles the induction as a tensor product. That
factorization alone proves no analytic or quotient transport.

Every normalized smooth-dual, bidual, opposite/upper, group-equivalence,
tensor and universe transport used by a route is a proof obligation.
Imported proposition definitions, including the refined duality statement,
are not proofs. The proof must be independent, directly and transitively, of
`GLDiscreteSeriesPositiveRootSupportStatement`, joint support, regular
Langlands head/exhaustion, tempered exhaustion, the square-integrable
Langlands classification and the ordered-segment classification.
