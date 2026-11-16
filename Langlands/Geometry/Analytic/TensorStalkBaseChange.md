# Localization of a tensor factor and pointwise base change

This internal algebraic prerequisite uses arbitrary commutative rings `R`, `S`
and `T`, with `R`-algebra structures on `S` and `T`, in three independent
universes. It has no norm, finite type, or field assumptions.

For a prime ideal `q` of `S`, `tensorLocalizationEquiv` is the canonical
`T`-algebra equivalence from `T ⊗[R] Localization.AtPrime q` to the
localization of `T ⊗[R] S` at the image of `q.primeCompl` under the right
factor inclusion. Its implementation is Mathlib's
`IsLocalization.tensorProductEquivOfMapIncludeRight`.

For a prime `P` of `T ⊗[R] S`, let `q` be its inverse image under that
inclusion. The two supporting theorems say:

- `flat_atPrime`: if `Localization.AtPrime q` is flat over `R`, then
  `Localization.AtPrime P` is flat over `T`.
- `formallyUnramified_atPrime`: if `Localization.AtPrime q` is formally
  unramified over `R`, then `Localization.AtPrime P` is formally unramified
  over `T`.

Both proofs use the same intermediate ring `D`: localize the tensor product
at the images of the elements outside `q`. These denominators lie outside
`P`. The canonical localization algebra and its scalar towers therefore make
`Localization.AtPrime P` a localization of `D`. Base change from `R` to `T`
gives the relevant property for the tensor product with the localized right
factor; `tensorLocalizationEquiv` transports it to `D`. Localizations are
flat and formally unramified, respectively. Composition gives the claimed
property for the final prime localization.

The provenance is internal: the construction combines Mathlib's tensor
localization equivalence, successive localization interface, and stability
of flatness and formal unramifiedness under base change and composition.
It is intended for transport of pointwise conditions through a finite
analytic tensor comparison. It does not identify analytic pointwise
predicates with these algebraic conditions, construct an analytic base
change, or prove unrestricted analytic étale pointwise lifting.
