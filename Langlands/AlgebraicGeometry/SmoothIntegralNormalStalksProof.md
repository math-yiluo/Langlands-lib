# Proof of normal stalks for integral smooth schemes over arbitrary fields

Author: Worker 57.

The exact theorem
`Langlands.AlgebraicGeometry.smoothIntegralNormalStalks` has type
`Langlands.AlgebraicGeometry.SmoothIntegralNormalStalksStatement.{u}`.
For every field `K`, integral Mathlib scheme `X`, smooth structural morphism
`X ⟶ Spec K` and actual point `x`, it proves
`IsIntegrallyClosed (X.presheaf.stalk x)`. The field and scheme share the
arbitrary universe `u`. There is no perfectness, algebraic-closedness or
characteristic hypothesis. The auxiliary algebraic lemmas allow independent
ring universes.

## Reduced Artinian ambient algebras

`isDomain_of_integrallyClosedIn` starts with a domain `R` integrally closed
in a reduced Artinian `R`-algebra `B`. Integral closedness gives injectivity
of the algebra map and hence nontriviality of `B`. Each idempotent of `B` is
integral, so it is the image of an element of `R`. Injectivity makes that
element idempotent in the domain `R`, where it is zero or one. Thus every
idempotent in `B` is zero or one. The existing separating-idempotent lemma
for zero products in reduced Artinian rings then gives no zero divisors in
`B`, proving that it is a domain.

## Etale domains and prime localizations

`integrallyClosed_of_etale` considers an etale domain `S` over an integrally
closed domain `R`. Put `F = FractionRing R`. The generic fibre `F ⊗[R] S`
is reduced and finite-dimensional over `F`, hence Artinian. Tensor symmetry
transfers these properties to `S ⊗[R] F`. The published
`SmoothAlgebraDomainLocalizationsProof.integrallyClosedIn_tensor_of_smooth`
uses smoothness of the etale algebra to prove integral closedness of `S`
in this latter generic fibre. The first helper makes the fibre a domain.
An Artinian domain is a field. Integral closedness in this field, with the
faithful scalar action supplied by the integral-closure structure, gives
`IsIntegrallyClosed S`.

`integrallyClosed_localization_of_smooth_domain` starts with a smooth domain
`A` over an arbitrary field `K` and a prime `p`. Mathlib supplies an element
`f ∉ p` such that `A[f⁻¹]` is etale over a finite-variable polynomial ring
over `K`. This polynomial ring is integrally closed. The element `f` is
nonzero because `p` contains zero. Its powers are non-zero-divisors in the
domain `A`, so `A[f⁻¹]` remains a domain. The etale helper therefore proves
integral closedness of `A[f⁻¹]`.

The powers of `f` are disjoint from `p`. Consequently the extended ideal
`q` in `A[f⁻¹]` is prime and contracts to `p`. Integral closedness localizes
at `q`. The canonical iterated-localization equivalence transfers this to
the prime localization at the contracted ideal, and its equality with `p`
gives `IsIntegrallyClosed (Localization.AtPrime p)`.

## Actual scheme stalks

For an original point of `X`, choose its preimage `y` in the actual affine
open cover. This chart is nonempty because it contains `y`. Its open
immersion into the integral scheme makes it integral, so its global section
ring is a domain. The composite chart map to `Spec K` is smooth. The
canonical global-sections isomorphism for `Spec K` gives the corresponding
smooth `K`-algebra structure on that section ring.

Apply the localization helper at the prime associated to `y`. The affine
stalk's canonical localization equivalence transfers integral closedness
to the chart stalk. The stalk isomorphism of the actual open immersion
then transfers it to the original stalk of `X`.

## Provenance and scope

This is an internal algebraic proof of the exact normal-stalk statement.
Its original-source provenance is recorded with that statement. The
implemented route uses standard-etale polynomial neighborhoods and integral
closure, rather than the source's regularity argument. It imports the
published smooth integral-closure base-change proof by Lean name. It uses
neither a normal-stalk premise nor the missing dominant-unramified-etale
criterion. Every scheme, ring, localization and stalk is the actual Mathlib
object. This theorem does not supply Harris representability, geometric
rigidity or a proof of the separate generic criterion.
