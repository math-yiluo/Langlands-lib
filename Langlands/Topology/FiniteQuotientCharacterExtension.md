# Complex characters through open finite quotients

Author: Worker 1232.

This helper implements the finite-group character extension used in the proof of
Artin and Tate, *Class Field Theory* (AMS Chelsea, 2009), Chapter X, Section 2,
Theorem 5, printed p.80 (one-based PDF p.89). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The generic topological formulation is derived from that proof, rather than a
separately stated arithmetic theorem in the source.

Let `A` and `C` be commutative topological groups in independent, unrestricted
universes. Given continuous homomorphisms `f : A → C` and `η : A → ℂˣ`, an open
finite-index subgroup `N` of `C`, and a natural number `m`, suppose every
`m`th power in `C` belongs to `N`, and `η` is trivial on the preimage of `N`
under `f`. The theorem constructs a continuous complex character `χ` of `C`
such that `χ ^ m = 1` and `χ.comp f = η`.

The proof first factors `η` through the image of `A` in the finite group `C/N`.
It uses `MonoidHom.liftOfSurjective` and the explicit kernel inclusion.
Mathlib's proved `MonoidHom.domRestrict_surjective` extends the resulting
character from this image subgroup to all of `C/N`, since the complex field has
enough roots of unity. The quotient is discrete because `N` is open, so this
finite-group character is continuous. Its pullback along the continuous quotient
map is the required `χ`. The power condition implies that the quotient, hence
every character of it, is killed by `m`. The restriction identity follows from
the two factorization identities.

No injectivity of `f` is assumed, and `m` need not be positive. This result does
not construct the arithmetic subgroup `N`. In the Grunwald–Wang application its
existence, openness, finite index, power bound `m = 2 * n`, and exact preimage
are separate obligations on the actual idele-class group. This helper alone
does not prove the number-field prescription theorem.
