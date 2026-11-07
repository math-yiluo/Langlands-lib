# Polynomial automorphisms from triangular coordinate formulae

Author: Worker 1284. Provenance: internal elementary algebra, developed to turn a separately proved Steinberg triangular restriction formula into polynomial bijectivity.

Let `R` be any commutative ring and let `rel` be a well-founded relation on an arbitrary variable type `ι`. Neither finiteness of `ι` nor a field hypothesis is required. The condition `HasLowerRemainders rel f` means that every variable occurring in `f i` is related to `i` by `rel`. For a family of units `c i`, `substitution c f` is the algebra endomorphism sending `X i` to `C (c i) * X i + f i`.

`inverseVariables` constructs inverse coordinates by well-founded recursion. At index `i`, it substitutes the recursively constructed lower coordinates into `f i`, subtracts that value from `X i`, and multiplies by the constant inverse of `c i`. The definition assigns arbitrary original variables outside the lower set; the remainder condition makes those assignments irrelevant.

The proof of the inverse coordinate equation uses Mathlib's congruence theorem that polynomial evaluation depends only on the occurring variables. One composition is the identity by that equation and the unit cancellation law. For the other composition, well-founded induction shows that substituting the original coordinates into each inverse coordinate yields the corresponding variable. The induction hypothesis handles precisely the variables of the remainder. Extensionality of algebra homomorphisms then proves the two homomorphism composition identities.

`coordinateEquiv` packages the original substitution and the recursively constructed inverse into an actual algebra equivalence. `substitution_bijective` records the resulting bijectivity.

This module proves no triangular formula for characters of a group, constructs no fundamental representation, and identifies no invariant algebra. It supplies only the algebraic consequence of such a formula once its well-founded dependency and unit diagonal have been proved.
