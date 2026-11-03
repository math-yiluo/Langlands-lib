# Geometric centre transport for actual adjoint quotients

Author: Worker 1490.

This internal unit derives transport results from the Library's full centre
functor, its compatibility with arbitrary base change, and its canonical
comparison between the pullback of an actual kernel and the actual kernel of
the pulled-back homomorphism. All bases are arbitrary schemes in the same
universe. No smoothness, reducedness, or characteristic assumption is needed.

`IsSchemeTheoreticCenter.iso_comp` changes only the source presentation of a
centre inclusion by an isomorphism. The composite remains a closed immersion,
and its range on every test scheme is unchanged: witnesses are transported by
the isomorphism and its inverse.

`kernelCenter_baseChange` pulls back the original actual kernel inclusion and
uses base change of closed immersions, ranges, and the full all-test centre
functor to identify its range. It then transports its source along
`kernelBaseChangeIso`.
The comparison's inverse-inclusion identity identifies the resulting morphism
with the actual kernel inclusion after base change.

`kernelCenterBaseChangePointsEquiv` constructs the multiplicative equivalence
between points of this actual kernel and points of the full centre, using the
proved representative property. Its value is composition with the actual
kernel inclusion. The value and naturality lemmas record this formula and its
compatibility with every morphism of test schemes.

`center_eq_bot_baseChange` combines compatibility of the full centre with
compatibility of the bottom subgroup functor. It retains all test schemes and
all refinements, including those detecting nonreduced centres.

These are derived formal consequences of the imported interfaces; they do not
assert preservation of connected reductivity or the full adjoint-quotient
universal properties.
