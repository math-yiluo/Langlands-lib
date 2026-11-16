# Pointwise étaleness through the ordinary tensor comparison

This internal construction connects the existing analytic pointwise predicates
to localization of ordinary tensor products. It uses the original bounded
maps and the actual closed-quotient affinoid pushout.

## Localization wrappers

For any bounded algebra map `f : R → S` over a normed field and spectrum
point `y`, `isFlatAtPoint_iff_flat_atPrime` equates the existing
`f.IsFlatAtPoint y` with flatness of `Localization.AtPrime y.kernel`
over `R`, where the `R`-algebra structure on `S` is induced by `f`.
The proof equips this localization with the local-ring homomorphism from
the localization of `R` at the image point. The local homomorphism's
compatibility with the original map gives the scalar tower. Mathlib's
`Module.flat_iff_of_isLocalization` then removes localization of the source.

For a finite type `f`,
`isUnramifiedAtPoint_iff_isUnramifiedAt` is reused from
`AffinoidPointwiseEtale`. Unfolding its unramified-locus predicate gives
formal unramifiedness of the target prime localization over `R`. Finite
type is required for this equivalence; no global formal unramifiedness
is assumed.

## Transport and canonical equivalence

For arbitrary commutative rings in independent universes,
`flat_atPrime_of_equiv` and `formallyUnramified_atPrime_of_equiv` transport
the tensor primewise base-change results through any `T`-algebra equivalence
from `T ⊗[R] S` to an algebra `D`. They pull a prime of `D` back through
the equivalence and then use `Localization.localAlgEquiv` to identify its
localization with the localization of that pullback prime.

For presented positive-radius affinoids `A`, `B`, `C` and original bounded
maps `f : A → B`, `g : A → C`, `tensorComparisonEquiv` is the canonical
ring equivalence from their ordinary relative tensor product to the actual
`AffinoidPushout.algebra f g`, supplied a proof that the original
`tensorComparison f g` is bijective. Its forward map is exactly that
comparison; it introduces no alternative pushout or maps.

## Étaleness at the actual pushout points

`rightMap_isEtaleAtPoint_of_tensorComparison` assumes bijectivity of that
comparison and finite type of `f`. At every spectrum point `x` of the
actual pushout, étaleness of `f` at the image under `leftMap f g` implies
étaleness of `rightMap f g` at `x`. Neither completeness of the coefficient
field nor a global étale hypothesis is needed for this conditional result.

The proof regards the tensor comparison equivalence as a `C`-algebra
equivalence, using its original left-factor equation. Finite type base
change and surjectivity of the equivalence give finite type of `rightMap`.
The original right-factor equation identifies the prime pulled back from
`x` to `B` with the kernel of its image point. The flatness wrapper, the existing unramified-locus equivalence,
the primewise tensor theorems, and the localized algebra equivalence now
transfer flatness and unramifiedness. Equality of the prime ideals is
transported through `PrimeSpectrum` so that their prime-proof arguments
are carried along as well.

The provenance is internal: the proof composes the Library's analytic
pointwise definitions and actual affinoid tensor comparison with the tensor
localization lemmas and Mathlib's localization and finite type interfaces.
No external-source correspondence is claimed. Bijectivity is an explicit
premise here; this unit does not prove the general finite tensor comparison,
construct a small analytic base-change witness, or prove unrestricted
analytic étale pointwise lifting.
