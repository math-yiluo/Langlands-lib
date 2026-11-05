# Power maps and diagonalizable character restrictions

Author: Worker 1341. This is an internal construction derived from the published
commutative group-object and diagonalizable character-point interfaces.

For an actual commutative group scheme `G` over any scheme, `powerHom G n` is the
pointwise natural-number power of its identity homomorphism. Its evaluation at
every test scheme is the corresponding power of the test point. The construction
commutes with base change and is natural under homomorphisms between commutative
group schemes. The proofs use the monoid structures on morphisms into a
commutative group object and the monoidal pullback functor.

For a commutative ring `R` and arbitrary abelian character groups,
the published `pointsEquiv_restrictMap` records evaluation after character restriction,
and `restrictMap_comp` proves contravariant composition by evaluating every
character on every test scheme. `restrictMap_nsmul_id` identifies multiplication
by `n` on the character group with `powerHom`. These claims impose no finite
generation or torsion restrictions.

The imported `isClosedImmersion_restrictMap` proves that a surjective character map
induces an actual closed subgroup. Its coordinate group-algebra map is surjective:
the published `incl_surjective` supplies surjectivity. The proof applies the closed-immersion criterion for affine spectra.
This retains the full scheme structure, including characteristic torsion.
