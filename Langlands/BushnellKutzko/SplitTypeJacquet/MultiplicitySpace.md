# Multiplicity spaces for quotient representations

Let `q : G →* D` be a group homomorphism and let `κ` and `π` be representations of `G`
on modules `W` and `V` over a commutative ring `R`. The group acts on `Hom_R(W, V)` by
`g · f = π(g) ∘ f ∘ κ(g⁻¹)`. `MultiplicitySpace κ π q` is the submodule fixed by `ker q`.
`multiplicitySpaceEquiv` identifies it with the space of intertwiners for the restrictions of
`κ` and `π` to `ker q`. When `q` is surjective, this action on the fixed submodule descends
to `D`. `multiplicityRep_apply` computes the descended action at `q g` by conjugation by `g`.

For a commuting square of homomorphisms `i : P →* G`, `s : P →* Q` and `j : Q →* D`
with `j ∘ s = q ∘ i`, suppose `s` is surjective, `j` is injective and the image of `i`
contains `ker q`. Given a representation `ξ` of `Q`, `multiplicityCurry` identifies the
`P`-intertwiners from `(κ ∘ i) ⊗ (ξ ∘ s)` to `π ∘ i` with the `Q`-intertwiners from `ξ`
to the pullback along `j` of the descended representation. The equivalence swaps the tensor
factors and curries a map `f` to `a ↦ (w ↦ f(w ⊗ a))`. Each element of `ker q` lifts to an
element of `ker s`, so the curried map takes values in the fixed submodule. The commutative
square and surjectivity of `s` give equivariance under `Q`. The inverse includes the fixed
submodule in `Hom_R(W, V)` and evaluates on the tensor factors.

This is an algebraic construction for the containment comparison in Bushnell and Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993), (8.3.4)–(8.3.5), printed
pp. 291–292 and 296–297. In the maximal-order comparison, `G` can be the maximal-order
`J`-group, `D` its finite reductive quotient, and `Q` the parabolic image of the intermediate
subgroup `P`. Currying then expresses containment over `P` as a finite parabolic Hom space
when the multiplicity space is finite-dimensional. The construction uses the ordinary
algebraic tensor–Hom equivalence of `RenardTensorHomAdjunctionProof` and the quotient action
on invariants in Mathlib.
