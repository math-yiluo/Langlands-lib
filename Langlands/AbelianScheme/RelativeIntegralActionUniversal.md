# The actual universal integral action on the action locus

This is an internal consequence of the published finite integral-action locus,
its classification equivalence, and the actual relative endomorphism presheaf.
Let `B` be an abelian scheme over `S`, and let a ring `O` have a supplied finite
integer basis `b`. A supplied scheme `E` over `S` represents the underlying
actual relative endomorphism presheaf on the full category of locally
noetherian schemes over `S`. Every morphism of that full category is retained.

`relativeIntegralActionLocusHomEquiv_comp` first proves naturality of the
existing classification equivalence, assuming explicitly that the finite
endomorphism power is locally noetherian. Precomposition of a map into the
action locus corresponds to composition of its classified action with
`relativeEndRestrict B`. This restriction is the actual Cartier relative-Hom
restriction, with the canonical comparisons for iterated base change, endowed
with its endomorphism-ring laws.

The proof compares the two integral actions on the supplied integer basis.
On each basis vector, the locus classification is decoding the corresponding
coordinate through the inverse of the supplied representation. Naturality
of that inverse gives the required restriction formula.

For the remaining declarations, `S` is locally noetherian, and `E` is separated
and locally of finite type over `S`. The published finite-product and
equalizer geometry then makes the action locus itself a locally noetherian
test, without a separate assumption about its finite tuple power.

`relativeIntegralActionUniversal` is the actual unital ring homomorphism
from `O` to the endomorphism ring of the pullback of `B` to this locus. It is
obtained by applying the classification equivalence to the identity map of
the locus. `relativeIntegralActionUniversal_restrict` applies the naturality
formula to that identity: the action classified by any actual test map is the
canonical relative restriction of this universal action.

`relativeIntegralActionUniversalHomEquiv` packages the existing equivalence
with this explicit universal-family interpretation. Its application formula
is `relativeIntegralActionUniversalHomEquiv_apply`.
`relativeIntegralActionUniversal_existsUnique` states that every actual
integral action on the test pullback has a unique actual classifying map.
Existence uses the inverse equivalence; uniqueness uses its injectivity.

The relative endomorphism representative and its displayed geometry remain
inputs. This module constructs neither that representative nor a Rosati,
determinant, polarization, or rational-isogeny moduli comparison. It is a
prerequisite for imposing further equations on the universal action.
