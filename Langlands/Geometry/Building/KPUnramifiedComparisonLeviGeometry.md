# Generic descended vectors and constant Levi-root valuations

Author: Worker 617.

This is a derived helper for the Levi field of the concrete unramified
comparison. It keeps the special torus and apartment lift of
`KPUnramifiedApartmentLift` unchanged.

Let `K = UnramifiedClosure F`, let `fK : S_K → T_K` be the base change of
the lift's factor `t.f`, and let `ξ` be an integral cocharacter generic for
the downstairs relative roots. The vector upstairs is
`descentCocharacterMap F K t.f hS (1 ⊗ ξ)`.

`eval_descent_eq_zero_iff_of_generic` proves that an actual upstairs root
has zero pairing with this vector if and only if `fK ≫ b = 0`. A nonzero
restriction is an actual root downstairs after base change:
`weightSpace_le_comp` puts its nonzero weight space inside the restricted
weight space. The bijectivity of character-lattice base change for a split
torus supplies its unique downstairs character, and
`mem_roots_baseChange_iff` identifies it as a downstairs relative root.
`eval_descentCocharacterMap`, `eval_splitCocharacterBaseChange` and
`eval_tmul` identify the pairing with the real cast of the integral
downstairs pairing. Genericity makes this nonzero. In the other direction,
the zero character has zero evaluation.

`val_eq_of_restriction_zero` applies the published theorem
`unramified_exists_descent_vadd_of_galoisFixed` to the two lifted points,
which are fixed by `L.fixed`. Their difference is the image of some vector
in `V(S)`. Evaluation on a character trivial on `S_K` vanishes, so the
translation formula `RootFunctionFamily.vadd_apply` proves equality of the
whole valuation functions for that character.

`val_eq_on_zeroPairingRoots_of_generic` combines these facts.
`exists_generic_levi_geometry` chooses `ξ` using the published
`IsSplitTorus.exists_genericCocharacter`; it asserts the existence of that
generic integral cocharacter and valuation constancy for its pairing Levi.
It does not assert centralizer containment or prove the full Levi field.

The geometric provenance is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), opening of §9.6 (printed p. 364, PDF p. 395) and §9.8.2
(printed pp. 375–376, PDF pp. 406–407): the fixed apartment is affine over
`V(S)`, and the roots of its centralizer Levi are the roots restricting
trivially to `S`. The proof uses the published infinite-Galois apartment
torsor theorem rather than introducing an affine-map premise.
