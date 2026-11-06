# Statement: rank-one reductivity from an actual Weyl inversion

`RankOneWeylReductivityStatement.{u}` isolates a field-theoretic input for
the openness proof. Let `G` be a smooth connected affine group over any
algebraically closed field `k` in universe `u`. Let `i : T → G` be an
actual closed split torus whose existing all-test centralizer is its
own range. Suppose the actual nonzero adjoint weights are exactly
`α` and `-α`, with `α ≠ 0`, and both existing weight spaces have
dimension one.

The final input is an actual group-scheme automorphism `c` of `T`
and an actual `k`-valued point `n` of `G`. The composite character
`α ∘ c` must equal `-α`. The existing all-refinement transporter
relation says, on every test scheme over the point and for every
torus point `t`, that `i(c(t)) n = n i(t)`. Thus `n` is an actual
normalizer element acting by inversion on the specified root
character. The conclusion is the existing `IsConnectedReductive G`.
No reductivity premise is made.

This formulation is derived from the rank-one field argument in
Brian Conrad, *Reductive group schemes* (2014), proof of
Proposition 3.1.9, pp.87–88. It expresses the nontrivial Weyl action
by a specified automorphism and a transporter, avoiding an added
choice of a relative Weyl quotient. The intended source argument
takes the reduced identity component `(ker α)^0_red` in `T`,
equivalently the codimension-one subtorus defined by saturating
`ℤ α` in the character lattice. The scheme-theoretic connected
kernel itself can be nonreduced and need not be a torus.
The two nonzero weights and the self-centralizer condition make
this reduced subtorus central and of codimension three in `G`.
The inversion element rules out
solvability, since the normalizer of a maximal torus in a smooth
connected solvable group centralizes that torus. The quotient by
the central torus is therefore a nonsolvable smooth connected
affine group of dimension three, which has trivial unipotent
radical.

These steps remain proof obligations. This contribution only
defines the full quantified proposition. Its hypotheses must be
constructed in the relative openness argument; the statement
neither proves openness nor adds any torus, weight or transporter
premise to the unchanged openness target. The source provenance
is derived, and the use of actual character weight spaces and
all-test transporters is the explicit Library formulation of
the source's field argument.
