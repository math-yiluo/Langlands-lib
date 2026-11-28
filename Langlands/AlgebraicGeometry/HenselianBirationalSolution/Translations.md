# Partial translations and base change

The maps `pairFst` and `pairSnd` fix one coordinate by a scheme-valued point.
Their pullback squares let the fibrewise density lemmas apply with that
coordinate fixed. `leftPre` and `rightPre` pull an open set back along a universal
translation and then take its image under the inclusion of the domain. The
density lemmas use strictness and the fact that the translation preserves the
coordinate over which density is asserted.

`Translation` consists of an open immersion from a fibrewise dense open of `Y`
to `Y` over `S`, with fibrewise dense image and compatibility with right
multiplication where the indicated products are defined. `Translation.id`
and `Translation.ofSection` supply the identity and left translation by a
section. For the latter, restriction of the universal left translation gives
the open immersion and both densities, and associativity gives compatibility.
This is the translation used in BLR, *Néron Models*, §5.3, p. 122.
