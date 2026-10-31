# Section covariance for a split kernel

Authors: Worker 76 (shared draft, all constructions and the main proofs) and
Worker 835 (the pointwise lemma `splitKernelCompactEquiv_section_eval`, checks
and this description).

This pair builds the conjugation automorphisms and the coefficient action of
`L`. It then proves the section covariance of the split-kernel relative integral
`splitKernelCompactIntegral` and of its descent
`splitKernelCompactCoinvariantDesc` (the entry theorem
`Langlands.Induction.splitKernelCompactCoinvariantDesc_section`). It is an internal
prerequisite for Worker 76's parabolic-orbit Jacquet comparison.

## Provenance

The pair is derived and internal. Every result is a composition of published
Library constructions with Mathlib's `Representation.Coinvariants` API. It uses
the following published constructions:

- `HaarModulus.normalizerConj` (Langlands/Group/HaarModulus);
- `QuotientIntegration.subgroupAutomorphism`;
- `automorphismInducing`, `precomposeCompactInducedEquiv` and
  `automorphismCoinvariantsEquiv` (CompactAutomorphism and
  CompactAutomorphismIntegralProof);
- `compactCoinvariantIntegral_natural` (CompactCoinvariantIntegral);
- `compactCoinvariantIntegral_automorphism` (CompactAutomorphismIntegralProof),
  which supplies the Haar ratio;
- `splitKernelSection` and `splitKernelCompactEquiv` (SplitKernelCompact);
- `splitKernelCompactIntegral`, `splitKernelCompactCoinvariantDesc` and
  `isClosed_splitKernelIntersection` (SplitKernelIntegral).

No external theorem is stated or transcribed, and no measure-scaling or
comparison premise is added.

## Setting

`G` is a topological group, `L` a group, and `r : G →* L` and `s : L →* G` are
homomorphisms. `H` is a subgroup of `G` with `hsH : ∀ l, s l ∈ H`. Write
`N = r.ker` and `I = H.comap N.subtype`, with its subgroup topology inside `N`.
Write `j = N.subtype.subgroupComap H : I →* H` for the actual inclusion and
`σI = σ.comp j` for a complex representation `σ` of `H` on a module `V`. The
universes of `G`, `L`, `V`, and in naturality `W`, are independent. The
coefficient modules have no topology or dimension restriction.

## The conjugation automorphisms

`splitKernelConjugation r s l : N ≃ₜ* N` is the published normalizer conjugation
`HaarModulus.normalizerConj` of the normal subgroup `N` by `(s l)⁻¹`. It is a
continuous automorphism, and `splitKernelConjugation_apply` gives its value:

```text
(α_l n : G) = s(l)⁻¹ * n * s(l),        α_l = splitKernelConjugation r s l.
```

`splitKernelConjugation_mem` proves `α_l n ∈ I ↔ n ∈ I` for every `n : N`, from
`s l ∈ H` and closure of `H` under products and inverses. This is the
preservation hypothesis `hα` used by `subgroupAutomorphism`,
`automorphismInducing` and the published integral law.

## The coefficient action `D`

Let `a = splitKernelSection s H hsH`, so `a l = ⟨s l, hsH l⟩ : H` is the section
value lifted into `H`.

- `splitKernelCoefficientMap r s H hsH σ l` is the actual intertwiner from the
  `α_l`-pulled-back representation `automorphismInducing I α_l hα σI` to `σI`,
  with linear map `σ(a l)`. Its intertwining law is the group identity
  `s(l) * (s(l)⁻¹ * i * s(l)) = i * s(l)` in `H`, for `i ∈ I`.
- `splitKernelCoefficientLinearMap r s H hsH σ l` is the composite on
  `Representation.Coinvariants σI`:
  `Coinvariants.map (splitKernelCoefficientMap …)` after the inverse of the
  published identity-on-vectors transport `automorphismCoinvariantsEquiv`.
  `splitKernelCoefficientLinearMap_mk` gives `[v] ↦ [σ(a l) v]` by `rfl`.
- `splitKernelCoefficientAction r s H hsH σ : Representation ℂ L
  (Representation.Coinvariants σI)` bundles these maps. The identity and
  multiplication laws are proved on representatives, using surjectivity of
  `Coinvariants.mk` and the fact that `σ ∘ a` is a homomorphism. The construction
  assumes neither well-definedness nor any equivariance law.
  `splitKernelCoefficientAction_mk` states `D(l)[v] = [σ(a l) v]`.
- `splitKernelCoefficientAction_natural` holds for every intertwiner
  `T : σ.IntertwiningMap τ`, where `τ` is a representation of `H` on an arbitrary
  module `W` in an independent universe. It says that
  `Coinvariants.map (splitKernelInducingMap r H T)` commutes with the two actions
  `D`. It follows from the intertwining law `T (σ(a l) v) = τ(a l) (T v)`. No
  smoothness of `σ` or `τ` is needed.

## The compact-function identity

From now on `L` has a topology, `G` is locally compact, `r` and `s` are
continuous with `r (s l) = l`, `H` is closed and `σ` is smooth. No topological
group structure on `L` is needed. Let `E = splitKernelCompactEquiv r s hrs hr hs
H hH hsH σ hσ` be the published kernel restriction of compact functions.

`splitKernelCompactEquiv_section` states, as an equality of actual compact
functions on `N` with coefficients `σI`, that

```text
E (compactInduced H σ (s l) f)
  = compactInducedMap I (splitKernelCoefficientMap … l)
      (precomposeCompactInducedEquiv I α_l hα σI (E f)).
```

The precomposition lies in compact induction from the pulled-back
representation. The coefficient intertwiner maps it back into
`CompactFunctions I σI`, so both sides are actual compact functions. The proof
compares values at `n : N`, which are `f(n * s(l))` and `σ(a l) (f(s(l)⁻¹ * n *
s(l)))`. It then uses the left covariance of `f` under `a l ∈ H` and cancels
`s(l) * s(l)⁻¹`.

`splitKernelCompactEquiv_section_eval` is the pointwise form:

```text
eval I σI (E (compactInduced H σ (s l) f)).1 n = σ(a l) (eval I σI (E f).1 (α_l n)).
```

The restriction of the section translate at `n` is `σ(s(l))` applied to the
restriction of `f` at `α_l(n)`.

## The integral identity

For the integral, assume in addition:

- `G` is Hausdorff and `N` is locally compact;
- Borel measurable structures on `N`, `I` and `LeftQuotient I = I \ N`;
- a regular Haar measure `μN` on `N`;
- a regular, left and right invariant Haar measure `μI` on `I`;
- a measure `ν` on `I \ N`, finite on compact sets, with
  `QuotientIntegration.IsCompatible I μN μI ν`.

`IsCompatible` consists of the fields nonzero, regular, right translation
invariance under every `n : N`, integrability of averages and the Weil integral
formula. These are exactly the analytic inputs of the published
`compactCoinvariantIntegral_automorphism`, applied to the group `N` and the
subgroup `I`. Closedness of `I` in `N` comes from `isClosed_splitKernelIntersection`,
and local compactness of `I` is derived from it within each statement. No
compact-open subgroup basis on `N` is needed.

Let `αI_l = QuotientIntegration.subgroupAutomorphism I α_l hα` be the actual
restriction of `α_l` to `I`. In Lean the scalar is

```text
c_l = ((((mulEquivHaarChar αI_l / mulEquivHaarChar α_l : ℝ≥0) : ℝ) : ℂ)),
```

with Mathlib's `MeasureTheory.mulEquivHaarChar`. This is the subgroup modulus
divided by the kernel modulus.

`splitKernelCompactIntegral_section` proves, for every `l : L` and every actual
compact function `f : CompactFunctions H σ`,

```text
I_ν (compactInduced H σ (s l) f) = c_l • D(l) (I_ν f),
```

where `I_ν = splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν` is the
published finite-fiber algebraic integral over `I \ N` of the quotient simple
function `[n] ↦ [f(n)]` after actual kernel restriction, and
`D = splitKernelCoefficientAction r s H hsH σ`. The proof:

1. unfold `I_ν` as `compactCoinvariantIntegral I σI ν ∘ E` and rewrite with
   `splitKernelCompactEquiv_section`;
2. apply `compactCoinvariantIntegral_natural` to the coefficient intertwiner, so
   the left side is `Coinvariants.map T z`, where `z` is the integral, for the
   pulled-back representation, of the forward precomposition by `α_l` of `E f`;
3. write `Coinvariants.map T z = D(l) (A z)` with
   `A = automorphismCoinvariantsEquiv I α_l hα σI`, using `A.symm (A z) = z`;
4. by `compactCoinvariantIntegral_automorphism`,
   `A z = c_l • compactCoinvariantIntegral I σI ν (E f)`, and linearity of
   `D(l)` gives the result.

The orientation is the published one: forward precomposition by `α_l` on `N`,
with the exact ratio `mulEquivHaarChar αI_l / mulEquivHaarChar α_l`.

## Descent to the kernel coinvariants

`splitKernelCompactCoinvariantDesc_section` proves the same formula for every
`z` in `Representation.Coinvariants ((compactInduced H σ).comp N.subtype)`:

```text
Desc ((compactInduced H σ).toCoinvariants N (s l) z) = c_l • D(l) (Desc z),
```

where `Desc = splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
hCompatible.right_invariant`. The source action is Mathlib's
`Representation.toCoinvariants` for the normal subgroup `N`, evaluated at `s l`.
Choosing a representative `f` of `z` by surjectivity of `Coinvariants.mk`, both
sides reduce definitionally to the integral identity above.

## Scope

This pair does not bundle the scalars `c_l` into a character. It does not prove
induction in stages, a normalized functor isomorphism, or the parent
`PadicParabolicOrbitJacquetComparison`. It imports `SplitKernelIntegral` and
`CompactAutomorphismIntegralProof` by their published module names.
