# Domain prime localizations of smooth algebras over arbitrary fields

This module proves the published Library proposition
`Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizations`:

```lean
theorem Langlands.CommutativeAlgebra.smoothAlgebraDomainLocalizations.{u, v} :
    Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizations.{u, v}
```

For every field `K : Type u`, smooth commutative `K`-algebra `A : Type v`,
and prime ideal `p` of `A`, the localization `Localization.AtPrime p` is a
domain, including nontriviality. The universes `u` and `v` are arbitrary and
independent. The closing theorem has no additional outer hypotheses.

The argument is internally derived from Mathlib's smooth integral-closure
base-change theorem, standard-etale polynomial charts, and the published
theorem
`Langlands.CommutativeAlgebra.integrallyClosedInReducedArtinianDomainLocalizations`.
It uses the existing Mathlib notions throughout.

## Integral closure under smooth base change

The helper `integrallyClosedIn_tensor_of_smooth`, in namespace
`Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof`, proves that
if `R` is integrally closed in an `R`-algebra `B` and `S` is smooth over `R`,
then `S` is integrally closed in `S ⊗[R] B`.

The injectivity component follows from the old algebra map's injectivity and
flatness of the smooth algebra. For an element integral over `S`, the
surjectivity of `TensorProduct.toIntegralClosure_bijective_of_smooth` gives
a preimage in `S ⊗[R] integralClosure R B`. Tensor induction shows that this
preimage maps to an element of `S`: each old integral element comes from `R`,
and a scalar in the right tensor factor can be moved to the left factor.
Addition preserves this description. Thus every integral element of the new
ambient algebra is in the image of `S`.

## Etale algebras over integrally closed domains

The helper `domain_localizations_of_etale_of_integrallyClosed` treats an etale
algebra `S` over an integrally closed domain `R`. Let `F` be `FractionRing R`.
Mathlib's formally unramified field results make `F ⊗[R] S` reduced and finite
dimensional over `F`, hence Artinian. Tensor commutativity transfers these
properties to `S ⊗[R] F`. Since an etale algebra is smooth, the first helper
shows that `S` is integrally closed in this reduced Artinian ring.

The helper takes the generic Artinian localization assertion as an explicit
argument `H` and applies it to `S` and `S ⊗[R] F`. In the closing theorem this
argument is supplied by the imported published theorem, so it is not an
assumption of the result.

## Smooth polynomial charts and prime localization

The adapter `smoothAlgebraDomainLocalizations_of_artinian_lemma` starts with a
smooth `K`-algebra `A` and a prime `p`. The Mathlib theorem
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` provides an element
`f ∉ p`, a natural number `n`, and a standard-etale structure on
`Localization.Away f` over `MvPolynomial (Fin n) K`.

The polynomial ring over the field is a unique factorization domain and
therefore integrally closed. The etale helper shows that every prime
localization of the chart is a domain. In particular this holds at the
extension `q` of `p`. The powers of `f` are disjoint from `p`, so `q` is prime
and its comap is `p`.

The equivalence
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization` identifies
the localization of the chart at `q` with the localization of `A` at the
comap of `q`. The proof transfers the domain instance through this ring
equivalence, then substitutes the equality of that comap with `p`.

The final theorem supplies
`integrallyClosedInReducedArtinianDomainLocalizations.{v, max u v}` to the
adapter. The chart ring lies in `Type v`, while its tensor product with the
fraction field of the polynomial ring lies in `Type (max u v)`. This accounts
for independent field and algebra universes without a size restriction.

## Source provenance

The statement's paired Markdown records its derivation from smooth regularity
and normality in the Stacks Project. The implemented proof takes the algebraic
route above. Stacks Project Tag 03GE, Lemma 10.147.2, gives integral-closure
base change for etale maps; the Lean proof invokes Mathlib's stronger smooth
base-change theorem. The idempotent argument of Tag 030C, Lemma 10.37.16,
motivates the imported generic Artinian localization theorem, whose own
Markdown explains the derived generalization.

These originals and their comments are retained in registered source
`stacks-integral-closure-idempotent-generic-fiber-2026-10-28`, content SHA256
`66c72671cd84205183edcebc4e569179a3188b2b02898e669a1e172a56ac6abc`.
The corrected wording discussed in the comments is present in the retained
pages. The proof uses the published algebra theorem and Mathlib directly;
it does not use a scheme-level domain-stalk or rigidity result.
