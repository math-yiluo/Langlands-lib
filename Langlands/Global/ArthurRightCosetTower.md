# Decomposing right cosets over an intermediate subgroup

For subgroups `H ≤ K` of a group `Γ`, `rightCosetTower` sends a pair of
right cosets `(Kc, Hd)` to `Hdc`, using the chosen representatives `c ∈ Γ`
and `d ∈ K`. Projecting to `K \ Γ` recovers the outer coset. For a fixed
representative `c`, cancelling the factor `c` detects equality of the
relative cosets. Conversely, for a representative `g` of a coset in
`H \ Γ`, take `c` to be the chosen representative of `Kg`. Then `gc⁻¹`
belongs to `K` and gives the relative coset. These are the injectivity and
surjectivity arguments for the equivalence.

`finiteSupport_tsum_rightCosetTower` applies the equivalence to a sum and
then separates the two factors. Finite support follows from a finite set
of outer indices and finite support in each inner fibre.

`RightCosetPartitionRegroupingStatement` uses a subgroup `P(S)` for each
subset `S` of a finite set `Δ`, with `P(R) ≤ P(S)` when `R ⊆ S`. The outer
summand `a(S, g)` is left `P(S)`-invariant and has finite support on the
right cosets. The coefficients `b(R, S, g)` are left `P(R)`-invariant and
give a finite partition of unity when summed over `R ⊆ S` and over
`P(R) \ P(S)`, at the chosen representative of each outer coset. The
statement gives finite support of `a(S) b(R,S)` on `P(R) \ Γ` and equality
of the original sum with the sum over `R ⊆ S ⊆ Δ` and `P(R) \ Γ`.

`rightCosetPartitionRegrouping` multiplies the outer summand by the
partition of unity. The support of the outer summand permits exchanging
the finite parabolic sum with the coset sum. The tower equivalence then
reindexes each inner and outer pair on `P(R) \ Γ`. Invariance under
`P(R)` allows evaluation at the chosen representative of the new coset.
The outer term is unchanged by the relative representative in `P(S)`.

This is the right-coset reindexing used when inserting the relative
partition (8.1) into the truncation sum in Arthur 2005, §13, printed p. 71.
The proposition isolates the reindexing for abstract groups.
