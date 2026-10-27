# Conditional comparison of continued unequal-rank bilinear forms

This module defines `UnequalRankBilinearUniquenessConclusion`, a fixed-data
specialization of the conclusion of the published
`UnequalRankBilinearUniquenessStatement`, and proves the conditional algebra
connecting continued covariant forms to the exact block-zero gamma equation.
It does not prove analytic continuation, the construction of covariant forms,
full Whittaker-type uniqueness, or the universal block-zero gamma existence
statement. Every such input remains an explicit hypothesis of these lemmas.

## Data and the fixed uniqueness predicate

Let F be a field with a topology, let n,r be natural numbers with hnr : n < r,
and let V and W be independent complex modules. Fix a unitary additive
character psi, an absolute value abv, representations pi of GL_(r+1) on V and
sigma of GL_(n+1) on W, and actual functionals ell : glFunctionals psi r pi and
ell' : glInverseFunctionals psi n sigma. Put
M = (coefficientModel pi ell).toSubmodule and
M' = (coefficientModel sigma ell').toSubmodule.

For a natural number q, `UnequalRankBilinearUniquenessConclusion` is the
Prop-valued definition

```text
exists E : Finset C, forall s : C, spectralPoint q s not in E ->
  forall B B' : M ->_C M' ->_C C,
    IsUnequalRankBilinearCovariant hnr psi abv pi sigma ell ell' s B ->
    IsUnequalRankBilinearCovariant hnr psi abv pi sigma ell ell' s B' ->
    B != 0 -> exists c : C, B' = c * B.
```

Here the last multiplication is scalar multiplication of curried linear maps.
The finite set consists of spectral values and precedes the parameter and
forms. The covariance predicate is imported unchanged, including its actual
embedding, determinant weight and unipotent subgroup. This definition adds no
uniqueness assertion: when q and abv are the residue cardinality and normalized
absolute value, respectively, it is exactly the fixed-data conclusion appearing
in the published full uniqueness target. The universal hypotheses needed to
prove that conclusion remain the separate uniqueness proof's responsibility.

## The elementary comparison lemma

`bilinear_cross_of_scalar_comparison` applies to any two curried complex-linear
forms L,L' on independent complex modules A and B. Assume that L != 0 implies
L' = c * L for some complex scalar. For arbitrary a,c in A and b,d in B it proves

```text
L'(a,b) * L(c,d) = L'(c,d) * L(a,b).
```

The implemented proof splits on L = 0. In that case the original factors on
both sides vanish, regardless of L'. Otherwise it substitutes the comparison
scalar, expands scalar multiplication at each argument, and uses commutativity
of complex multiplication. There is no pointwise nonzero anchor requirement
and no assertion that the comparison scalar is nonzero.

## Actual continuations and rational cross identities

For the remaining lemmas F also has a topological ring structure and a
measurable space, and the actual left-unipotent quotient has its supplied
measurable space. Fix a quotient measure mu and a supplied additive Haar
measure nu. Set k = r-n-1, with the dimension equality
hr : r = n + (0+k+1) derived from hnr. The two integral families are precisely

```text
I(f,f') = unequalRankIntegralAt 0 k hr psi abv mu
  (rectangularMeasure nu 0 (n+1)) f.val f'.val

D(f,f') = dualUnequalRankModelIntegralAt hnr 0 k hr
  psi abv mu nu pi sigma ell ell' f f'.
```

The dual family is the published inverse-transpose complementary-block family,
with inverse character and blockWeylAt right translation. Neither integral nor
its measure is changed here. The continuations of D use its unreflected
parameter; reflection occurs only in their evaluations and rational substitution.

`UnequalRankBlockZeroContinuedFormsConclusion.rational_cross` takes:

- the published fixed-data continued-forms conclusion for these actual families;
- the fixed uniqueness conclusion defined above;
- q > 1 and a complex unit delta with value q^(-1);
- arbitrary functions R,Rd from M x M' to rational functions, each supplied
  with its actual HasRationalContinuation proof for I and D, respectively.

For every two vector pairs (f,f') and (g,g') it proves

```text
subst delta (Rd(f,f')) * R(g,g') =
  subst delta (Rd(g,g')) * R(f,f').
```

The proof takes the union of the continued-forms and uniqueness exceptional
sets. Outside this union, it obtains the two covariant forms at the same s.
Their separate unnormalized evaluation clauses identify all four rational
values with evaluations of those forms at the two vector pairs. The elementary
comparison lemma gives the required pointwise cross identity. The published
`RationalGammaComparison.rational_cross_of_spectral_cross` then converts this
to the rational identity. That result uses infinitely many regular spectral
points and carries its four denominator antecedents. The new proof supplies
its identity on that domain through the stronger continued-forms clauses;
it never infers linearity from totalized evaluation at a pole. The union is
chosen before all parameters and vectors.

## Conditional block-zero gamma assembly

`UnequalRankBlockZeroContinuedFormsConclusion.exists_gammaEquation` takes the
same inputs and additionally a complex unit zeta satisfying the actual
`HasModelMinusOneScalar sigma ell' zeta`, together with one nonzero value of R
and one nonzero value of Rd. These two witnesses may come from different
vector pairs. It proves

```text
exists G : RationalFunctions, G != 0 and
  UnequalRankBlockZeroGammaEquation hnr q psi abv mu nu pi sigma ell ell' G.
```

The implemented proof indexes the two rational families by M x M', applies the
cross-identity theorem above, and uses the published
`RationalGammaComparison.exists_gammaFunctionalEquation_of_cross` with exponent
r. That theorem derives a nonzero common comparison from the two separate
witnesses. The larger representation has rank r+1, so the exponent is the
required r. The original nonzero witness belongs to the exact original value
set by `unequalRankValuesAt_eq_set`. Finally the proof packages zeta, that
witness, both supplied continuations at every vector pair, and the common gamma
equation. Its evaluation domain retains exactly the three reduced-denominator
conditions for R at s, Rd at 1-s and G at s. No pole is discarded from that
published domain.

This is a conditional reduction. In particular, its explicit uniqueness and
continued-forms hypotheses have not been discharged by the helper. Obtaining
the continuations and separate nonzero witnesses from the analytic conclusions,
and obtaining the shared minus-one scalar, are separate integration steps.
The full p-adic Whittaker-type existence target is not proved here.

## Provenance, authorship and validation

The definition is an internal specialization of the published uniqueness
interface. The lemmas are derived algebra using that interface, the published
continued-forms conclusion, `DualModels.unequalRankValuesAt_eq_set`, and
`RationalGammaComparison`. This contribution makes no new original-literature
claim and does not assert that an irreducible-generic result proves full
Whittaker-type uniqueness. No imported Lean/Markdown pair is edited.

Worker 364 suggested the zero/nonzero split for bilinear comparison. Worker 112
implemented and checked its adaptation to the exact unequal-rank interfaces
and the conditional gamma assembly. All three universes uF,uV,uW are retained
independently in the field and representation-carrier data.

The module compiles with zero errors and zero warnings in the approved Lean
service environment 3b864ddf-f0af-4c18-8903-c6f813a0ce0f (development check
e8876bd1-08eb-49d0-a681-5335c4121676). Compilation is development evidence;
independent semantic review and Library publication are separate requirements.
