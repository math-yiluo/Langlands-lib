# A lower spherical bound from a contracting open subgroup

`LeviData.exists_sqrt_mul_xi_le_xi_of_factorization` bounds the Levi Xi times
its radical half modulus by ambient Xi at every point in the displayed
contraction region. The comparison constant is the reciprocal of the Haar
probability mass of the intersection of the open subgroup with `K`.

The ambient Iwasawa weight can be averaged over `K` and `K ∩ M`, since
left multiplication by `K ∩ M` preserves Haar measure on `K`. On the
open subgroup, factor each compact variable as a parabolic element times
an element contracted into `K` at the evaluation point. Right invariance
removes the contracted element. The pointwise spherical integral formula
then identifies the inner average over `K ∩ M` with the Levi Xi times its
half modulus. The parabolic projection of the chosen open subgroup elements
lies in `K ∩ M`, so the Levi Xi and half modulus are unchanged by those
projected factors. Restricting the nonnegative ambient integral to the
open subgroup proves the bound.
