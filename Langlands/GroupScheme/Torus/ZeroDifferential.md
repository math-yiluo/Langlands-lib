# Zero differentials of homomorphisms of split tori

This is an internal consequence of the published actual split-torus point model,
character lattice, and realization of additive character maps. It supports the
character arithmetic needed in the isogeny reduction; it does not prove that
reduction or the no-torus unipotence theorem.

For arbitrary `k : Type u` with `Field k` and split commutative group schemes
`T` and `T'` over `Spec k`, let `f : T ⟶ T'`. The hypothesis is that actual
postcomposition sends every vector in the dual-number identity kernel of `T`
over `k` to the identity in that of `T'`. If `CharP k p` and `p ≠ 0`, there is
an actual homomorphism `g : T ⟶ T'` such that

`f = ((p : ℤ) • 𝟙 T) ≫ g`.

If `CharZero k`, then `f = 0`. The proposition
`SplitTorusZeroDifferentialStatement` packages both conclusions, and
`splitTorusZeroDifferential` proves it in arbitrary universe `u`. No
perfectness, infinitude, or algebraic closedness is assumed.

The proof starts with the actual dual-number unit `(1, a)`, whose product law
adds the second coefficients. The additive homomorphism
`splitTorus.infinitesimalUnitAddHom` gives its integral power law. For a standard
split torus with finite index set `I`,
`splitTorus.characterValue_infinitesimalPoint` evaluates a character with
exponent coordinates `m i` at the tangent coordinates `v i` as the unit
`(1, ∑ i, (m i : A) * v i)`, over every commutative `k`-algebra `A : Type u`.
Applying the zero-differential hypothesis to each coordinate vector over `k`
shows `(m i : k) = 0`. `CharP.intCast_eq_zero_iff` therefore makes `p` divide
each exponent. In characteristic zero, each exponent itself is zero.

For positive characteristic, choose a character with these divided coordinates
for every pullback `f ≫ χ`. Multiplication by the nonzero integer `p` is
injective on the source lattice, as follows from its identification with
`I → ℤ`. This injectivity proves that the choices form an additive map of
character lattices. The published `IsSplitTorus.homOfCharacterMap` realizes it
as an actual morphism. Character separation gives the factorization of `f`.
For characteristic zero, character separation instead gives `f = 0` directly.
Both results are transported from a standard split torus to any split source
using its actual group-scheme isomorphism.

The auxiliary theorem `characteristic_dvd_character_coordinates` also allows
`p = 0`: its conclusion then states that all exponent coordinates are zero.
The factorization results require `p ≠ 0` because their construction uses
injectivity of multiplication by `p` on the integral lattice. These results
concern split tori and a differential over the base field; they do not assert
lifting of tori, a decrease of weights, or termination of successive quotients.
