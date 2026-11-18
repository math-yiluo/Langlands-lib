# Reduction of Nagata's identity-component conclusion by Frobenius images

`NagataConnectedFrobeniusReductionStatement` concerns affine group schemes of
finite type over an algebraically closed field of positive characteristic. It
reduces multiplicative type of the identity component of a linearly reductive
group to two premises. The first is the reduced ambient group case of the same
conclusion. The second says that each ambient group under consideration admits
a closed matrix embedding whose first Frobenius power has multiplicative-type
scheme kernel.

The proof uses Noetherianity of the coordinate algebra to bound all nilpotents
by one exponent of the form `p ^ r`. At `r = 0`, the actual coordinate algebra
and hence the ambient group scheme are reduced. In the successor case, the
first Frobenius image is a schematically dominant fppf quotient by the specified
kernel. Linear reductivity descends on the entire ambient group by the
all-test coefficient criterion. Every image coordinate pulls back to a `p`th
power. A nilpotent coordinate has a nilpotent pulled-back root, so injectivity
of pullback reduces the bound from `p ^ (r + 1)` to `p ^ r` on the image.

The induction gives multiplicative type of the image's identity component.
The homomorphism of identity components is flat by cancellation of the target
open immersion and is surjective by the flat image theorem for connected affine
groups. Its full kernel is the restriction of the ambient kernel to a closed
subgroup, so it retains multiplicative type. The field extension theorem for
groups of multiplicative type then lifts the conclusion from the connected
quotient and this kernel to the source identity component.

This is a derived induction for the nonsmooth part of Nagata's theorem. The
exact published finite-coordinate linear reductivity condition is used on the
ambient groups, which may be disconnected at every stage.
