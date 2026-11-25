# Actual full-centre characters and the D4 leaf relation

This internal module constructs the centre used by the character relation,
using the imported full-centre, maximal-torus, and base-change results. It does
not assume a supplied centre or its torus factorization.

For an actual `TitsIndexData G`, the definition `toralCenter` applies
`centerInMaximalTorus` to the ground-field maximal torus. It contains an actual
commutative representative of the entire scheme-theoretic centre over the
ground field and its map to that torus. The theorem
`toralCenter_baseChange_isCenter` proves that the same inclusion after base
change represents the full centre over the separable closure. This retains
the nonreduced centre in positive characteristic.

The theorem `toralCenter_root_comp_eq_zero` restricts every actual absolute
root to zero on that centre. With simple connectedness,
`centerFundamentalCharacter` restricts the actual integral fundamental weight
at a simple vertex to the full centre after base change.

The theorem `centerFundamentalCharacter_galois` compares the ordinary Galois
action of the ground-field centre with the full absolute Galois star action
on vertices. It holds for each automorphism and each vertex, with no trivial
action or fixed-vertex assumption. The proof uses the based permutation of
fundamental weights and the Weyl-correction congruence modulo the integral
root lattice. Restriction kills that lattice, and ordinary Galois transport
commutes with restriction along the ground-field torus map.

Under a numbering preserving every Cartan entry with `CartanMatrix.D 4`,
`centerFundamentalCharacter_D4_leaf_sum_eq_zero` proves that the actual centre
characters at leaves `0`, `2`, and `3` have sum zero. Its proof applies the
imported central-subgroup character relation to the constructed centre. The
vertex numbered `1` is the central vertex. No rank-one, local-field, or
characteristic assumption is needed.

These constructions and relations are internal consequences of the imported
actual interfaces. They do not identify the entire centre character group with
the weight-lattice quotient, construct Tits algebras or a Brauer obstruction
map, compare it with the anisotropic kernel, prove a corestriction formula, or
exclude a local D4 index.
