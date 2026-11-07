# Scalar of two independently continued actual intertwiners

This is a derived construction for the beginning of Waldspurger IV.3,
printed p.285 (PDF p.51), in `waldspurger-2003-plancherel`. It constructs a
rational coefficient from two continued operators and proves that it is
their actual ambient composition scalar when induced irreducibility is
known on one nonempty ambient open subset. The source specializes the two
operators to opposite standard intertwiners. This module permits two
arbitrary supplied ambient intertwiner families with the same inducing
representation and Levi; identification with the standard integrals remains
a separate obligation.

## Parameters and explicit hypotheses

The generic continuation lemmas use the imported
`RationalOperatorContinuationData` for families `A : Ω → V →ₗ[ℂ] W` and
`B : Λ → W →ₗ[ℂ] V`. Each datum has its own regular denominator and global
polynomial operator numerator. Its denominator is nonzero on its own
original parameter region. The two original regions need not intersect.
The coefficient vector spaces have no topological or dimension hypotheses.

The actual-character lemmas specialize to rational norm characters of a
connected reductive group scheme `L` over an arbitrary nonarchimedean local
field. A topology on `L.rationalPoints`, continuity `hp` of the rational
valuation-image projection, and connected reductivity `hL` are explicit.
The published regular-function domain and density theorems are used with
these same premises. No characteristic or splitness restriction is added.

The actual induction part has the hypotheses of
`CompactIntertwiningContinuation`: a locally compact nonarchimedean ambient
group `G`; semidirect decompositions `Pᵢ = M Uᵢ` with a common literal Levi;
closed radicals and subgroups; the existing `IsUnimodularModulus`
hypotheses; a common compact open `K` with `G = Pᵢ K`; continuous Levi
projections; a topological group isomorphism `L.rationalPoints ≃ₜ* M`;
continuous rational norm characters; and a canonical complex
`Langlands.SmoothRep` inducing representation. The field, ambient-group and
inducing-carrier universes are independent. This supplies no general
rational-point realization of these subgroup or topology premises.

`J₁₀` and `J₀₁` are actual ambient intertwiners on their independent original
regions `Ω₁₀` and `Ω₀₁`. The data `p` and `q` continue precisely their compact
conjugates. Separate nonempty ambient open sets `D₁₀ ⊆ Ω₁₀` and
`D₀₁ ⊆ Ω₀₁` permit the existing equivariant continuation to construct the
actual extended maps. Supplying these data is a substantive rationality
obligation, not a permitted external structural assertion.

The scalarity part additionally assumes separability of the ambient group
and an explicitly supplied nonempty ambient open set `D` on which the
actual normalized induced representation from `P₀` is irreducible. There
is no containment premise between `D` and either regular region. This local
induced-irreducibility premise is a representation-theoretic obligation;
it has not been proved here. It is not irreducibility of every tempered
induction. A fixed compact vector `v` and linear functional `ℓ` satisfy
`ℓ v = 1`. The imported algebraic dual lemma provides such a functional
for any nonzero vector; the extraction choices disappear from the scalar
through the independence results below.

## Common regular locus and rational fraction

In `RationalOperatorContinuationData`, `regularRegion_isOpen` uses
continuity of regular evaluation to show that a denominator's nonzero locus
is ambient open. `denominator_ne_zero` evaluates at a point of the original
nonempty region to exclude the zero regular function.

Write `R = p.regularRegion ∩ q.regularRegion`. `continuedComposite`
constructs `q.continuedOperator ∘ p.continuedOperator` on `R`.
`continuedComposite_rational` restricts both rational families to `R` and
uses the existing rational composition theorem. Their original convergence
regions never enter this composition. `continuedCompositeRegion_dense`
applies actual regular-function density to the product of the two nonzero
denominators. Pointwise, its nonzero locus is exactly `R`.
`continuedCompositeRegion_nonempty` follows from density in the nonempty
actual character space.

`continuedCompositeScalar v ℓ` is the coefficient
`ℓ (q.continuedOperator (p.continuedOperator v))` on `R`. At this point no
scalarity assertion is made. `continuedCompositeRationalScalar` uses the
existing coefficient-presentation construction to produce an element of
`rationalUnramifiedFunctionField L hp hL`. The construction uses the given
operators; there is no freely selected normalization scalar.

`continuedCompositeRationalScalar_spec` exhibits regular functions `a,b`
with `b ≠ 0` and `b(χ) ≠ 0` at every `χ ∈ R`. The constructed fraction is
`a/b` in the existing function field, and the coefficient equals
`a(χ)/b(χ)` throughout `R`. This is a regular presentation on `R`, not an
evaluation map at poles. Independence of the chosen coefficient numerator
and denominator follows from the imported
`rationalUnramifiedOperatorScalar_eq_presentation`, applied with the
nonempty open region `R`.

## Actual ambient composition and scalarity

`continuedInductionComposite` composes the two actual ambient extensions
from `continuedInductionIntertwiner` on `R`, in the same order as the compact
composite. `continuedInductionComposite_compact` first applies the existing
compact conjugation composition law, then the exact compact identities for
both actual extensions. This identifies its compact conjugate with
`p.continuedComposite q`. All restriction, extension and normalization maps
are the existing ones.

`continuedInductionComposite_generic_scalar` applies published separable
smooth Schur to this actual ambient endomorphism at parameters in `D ∩ R`.
The full ambient-to-compact scalar equivalence transports its scalarity to
the compact composite. This theorem itself only needs irreducibility at
these parameters; openness and nonemptiness of `D` enter the next step.

`continuedInductionComposite_compact_eq_scalar` proves that `D ∩ R` is
nonempty using density of `R` and nonempty openness of `D`. It is open
because both denominator regions are open. The imported
`rationalUnramifiedScalarContinuation` then extends Schur scalarity to all
of `R`, with scalar `continuedCompositeScalar v ℓ`.
`continuedInductionComposite_eq_scalar` uses compact conjugation
injectivity, expressed by `compactIntertwiningOperator_scalar_iff`, to
return the same equation for the actual ambient composition. This holds at
every parameter in `R`, including any reducible ones.

`continuedInductionCompositeRationalScalar_spec` gives a regular fraction
representing the constructed function-field element and the actual ambient
identity simultaneously: for every `χ ∈ R`, the composite is
`(a(χ)/b(χ))` times the identity of the actual normalized induction at `χ`.
The proof uses the selected coefficient presentation directly and the
proved ambient scalar identity.

## Independence and provenance boundaries

`continuedComposite_unique` changes either continuation datum for the same
two original families. It uses the separate original open subsets in the
published continuation uniqueness theorem, then composes the resulting
operator equalities at every common regular parameter.
`continuedCompositeRationalScalar_continuation_independent` proves equality
of the resulting function-field elements. The intersection of the two
composite regular regions is nonempty and open by the same density
argument. Their extracted coefficients agree there by operator uniqueness;
regular cross-multiplication proves equality of fractions. This does not
require scalarity or intersection of the two original regions.

`continuedInductionCompositeScalar_independent` applies another normalized
coefficient to the proved compact scalar identity. It proves independence
of both extraction choices at every parameter of `R`.
`continuedInductionCompositeRationalScalar_independent` uses the published
function-field scalar independence theorem with Schur scalarity on
`D ∩ R`, proving the same independence for the constructed fraction.
Together with continuation independence these allow both sorts of choices
to change.

Waldspurger IV.3 first uses a nonempty Zariski-open induced-irreducibility
locus, Schur's lemma, and rational continuation to define the opposite
composition scalar. Its route to generic irreducibility in the
discrete-series case refers to IV.2.2. The current construction isolates
the scalar extraction and continuation step at the actual character and
fixed-representative level. A nonempty Zariski-open regular locus yields
the ambient-open input once its source comparison is supplied. It does not
prove existence of that irreducibility locus, convergence or rationality
of standard integrals, or equivariance under changing inducing
representatives. It does not descend to the representation twist orbit,
prove independence of parabolic, contragredient or Weyl compatibility,
rank-one factorization, nonvanishing or positivity, or define the global
`j` and `mu` normalizations. These remain separate obligations. The supplied
families need not be opposite standard intertwiners, and the result cannot
be used as a source-normalized `j` until that comparison is proved.

The supporting results are derived from the existing actual compact
induction equivalences, rational operator composition and continuation,
actual regular-function density and function field, and smooth Schur.
They are not new assumptions about representation theory or analysis.
