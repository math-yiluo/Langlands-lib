# Equality of scalars in the two standard composition orders

Authors: Worker 200 and Worker 192.

## Provenance and scope

This is an internal algebraic extension of
`StandardInductionCanonicalScalar`. It combines the existing scalarity
theorem `continuedInductionComposite_compact_eq_scalar`, applied in
each order, with an elementary identity for two linear maps. It does
not translate an additional assertion from the original literature.
The existing standard integral, rational continuation, scalar
extraction and rational uniqueness constructions are used unchanged.

The main result is equality of the two canonical rational scalars with
all subgroup, inducing, compact-model and measure data fixed and the
two intertwining directions exchanged. Generic actual induced
irreducibility is supplied on a separate nonempty open locus for each
parabolic. The result is conditional on these and the other displayed
premises. It does not establish independence from other parabolic
pairs, a nonzero scalar, or the source-normalized `j`.

## Linear algebra

For complex vector spaces `V,W`, maps `f : V → W`, `g : W → V`,
and scalars `a,b`, suppose

\[
gf=a\,\mathrm{id}_V,\qquad fg=b\,\mathrm{id}_W.
\]

`linearMap_compositeScalar_eq_reverse` proves `a=b` when each space
has a normalized algebraic coefficient: vectors `v,w` and linear
functionals `ℓ,m` with `ℓ(v)=m(w)=1`. The carrier universes of `V`
and `W` are independent. No topology or representation is used here.

The implemented proof splits on `f=0`. In that case, applying the two
normalized coefficients to the scalar equations gives `a=b=0`.
Otherwise it chooses `x` with `f(x)≠0`. Applying `f` to the first
equation at `x` and the second equation at `f(x)` gives
`a • f(x) = b • f(x)`; scalar cancellation proves equality.
Thus a nonvanishing hypothesis on either intertwiner is unnecessary.
The normalization premises also ensure that neither carrier is zero.

## Rational continuations

Let `F : Type u` be a nonarchimedean local field of arbitrary
characteristic, and let `L` be a group scheme over `F`. Use its actual
rational norm characters and unramified character space. Let `p,q`
be `RationalOperatorContinuationData` for opposite-direction operator
families on sets `Ω,Λ`. Write

\[
R=p.\mathrm{regularRegion}\cap q.\mathrm{regularRegion}.
\]

`continuedCompositeScalar_eq_reverse_of_scalar` assumes the two
continued compact composites equal their extracted scalars times
identity throughout their respective common regular regions.
Applying the linear algebra theorem pointwise proves

\[
p.\mathrm{continuedCompositeScalar}(q,v,\ell,\chi)
 =
q.\mathrm{continuedCompositeScalar}(p,w,m,\chi),
\quad \chi\in R.
\]

The second parameter is explicitly transported to the reversed
intersection. This pointwise theorem needs neither connected
reductivity of `L` nor continuity of the valuation projection.
Its two scalarity assumptions are hypotheses of this generic helper,
not structural assumptions for the standard-family result below.

`continuedCompositeRationalScalar_eq_reverse_of_scalar` additionally
uses a topology on `L(F)`, continuity `hp` of
`rationalValuationImageProjection L`, connected reductivity `hL`,
and nonemptiness of `Ω` and `Λ`. The existing density theorem gives
nonemptiness of `R`. The proof applies
`ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen` on the ambient
open set `R`, using its identity inclusion into the first regular
region and the swapped inclusion into the second. The pointwise
identity therefore gives equality of the concrete fractions in
`rationalUnramifiedFunctionField L hp hL`. No intersection of the
original domains is assumed.

## Actual standard families and retained hypotheses

The specialization uses the actual standard families of
`StandardInductionCanonicalScalar`. The field universe `u`, ambient
group universe `uG` and inducing-carrier universe `uV` are independent.
There is no split, quasisplit or characteristic-zero restriction.

The ambient group `G` is locally compact, Hausdorff, nonarchimedean
and separable. There are actual semidirect decompositions
`P₀=M U₀`, `P₁=M U₁`, with closed parabolics, closed radicals, both
`IsUnimodularModulus` premises and continuous semidirect projections.
A common compact open subgroup `K` satisfies `G=P₀ K=P₁ K`.
An explicit topological group isomorphism `e : L(F) ≃ₜ* M`
transports the full rational norm-character family to `M`;
continuity of every norm character remains a premise. The inducing
representation `A` is the canonical `SmoothRep.{0,uG,uV} ℂ M`.
No realization of these data for every reductive rational-point group
is asserted.

Both radicals, both subgroup intersections and both quotient spaces
have their displayed Borel structures. The radical and intersection
measures are regular right-invariant Haar measures. The two quotient
measures have their displayed `QuotientIntegration.IsCompatible`
proofs. Closedness of `M` and the two
`SquaredModulusCompatibility` identities remain explicit.

The original domains `Ω₁₀,Ω₀₁` are exactly
`standardIntertwiningFullDomainRegion`: absolute scalar convergence
against every smooth-dual functional and representability in the
original inducing carrier, at every vector and group element.
The original families `J₁₀,J₀₁` are exactly
`standardInductionIntertwinerFamily` for the supplied measures.
The independent data `p,q` continue their compact restrictions.
Each denominator is nonzero on its entire original full domain.

Separate nonempty ambient open subsets
`D₁₀ ⊆ Ω₁₀` and `D₀₁ ⊆ Ω₀₁` remain premises. The original domains
need not be open, and no intersection of them or of these two
convergence subsets is assumed.

There are also two independent nonempty ambient open loci `D₀,D₁`.
For every `χ∈Dᵢ`, the actual
`UnramifiedLeviInduction` from `Pᵢ`, twisted by the transported
character, is irreducible. No containment in a convergence set is
required. Irreducibility is not assumed at every evaluation parameter,
and no irreducibility of all tempered inductions is asserted.

## The three standard-family equalities

`standardInductionCompositeScalar_eq_reverse` applies
`continuedInductionComposite_compact_eq_scalar` in the first order
using `D₀`, and in the reverse order using `D₁`. These prove the
scalarity hypotheses of the generic helper; scalarity is not a
separate premise of this specialization. For arbitrary normalized
coefficients on the two compact carriers, the extracted scalar
values agree throughout `R`, including any reducible parameters in
that region.

`standardInductionCompositeRationalScalar_eq_reverse` applies the
rational helper to those same two proved scalar equations. The
nonemptiness of each original domain comes from its supplied
convergence subset. It proves equality of the two fractions, allowing
different normalized coefficients on the two compact carriers.

`standardInductionCompositeCanonicalRationalScalar_eq_reverse`
uses the internally selected normalized pair on the first compact
carrier from `D₀` and the internally selected normalized pair on
the second carrier from `D₁`. It specializes the preceding rational
equality. Unfolding the existing canonical scalar definitions
identifies the two sides with precisely the fractions in that
equality. The chosen points, vectors and functionals need not agree.
No normalized coefficient is supplied to this final theorem.

`conditionalStandardInductionScalarSymmetry` has exact type
`ConditionalStandardInductionScalarSymmetryStatement`. It introduces
every universally quantified datum and premise of that proposition
and applies the canonical rational-scalar equality just proved.
The statement and its imported definitions are used unchanged.

## Remaining obligations

Initial nonempty-open full convergence, whole-operator rational
continuation and both generic actual induced irreducibility premises
remain obligations for applications and for the standing program.
The representation and analysis premises are not permitted external
structural inputs for completion.

The result does not prove independence from compact models, measures,
inducing representatives or different parabolic pairs. It assumes no
opposite relation between `P₀,P₁` and does not construct such a
relation. Full-stabilizer finiteness, nonvanishing, positivity,
source-normalized `j` and `mu`, structural realization, and the main
Schwartz and Plancherel conclusions remain separate obligations.
There is no value at a pole or assertion about unitary-locus density.
