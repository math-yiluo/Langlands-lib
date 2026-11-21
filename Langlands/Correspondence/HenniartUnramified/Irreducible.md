# Irreducibility and the twist stabilizer of the coinduction

Let `S` be a stage of degree `m + 1` and `τ` a representation of `H` on a complex
vector space `V`. Both main results, `coind_isIrreducible` and
`pow_eq_one_of_twist_equiv`, assume that `V` is nonzero and finite-dimensional over `ℂ`
(`[Nontrivial V]`, `[FiniteDimensional ℂ V]`). They also assume that the blocks
`S.block τ k`, for `k < m + 1`, are irreducible, and that there is no nonzero
intertwiner between distinct blocks. The auxiliary lemma `single_mem_of_cycUnit` needs
no finiteness.

The twist criterion uses finite dimensionality essentially. It enters through Schur's
lemma in the form `end_scalar`. Without it, an irreducible block could have non-scalar
endomorphisms.

`coind_isIrreducible` proves that `S.coind τ` is irreducible. Take a nonzero
subrepresentation `M`, and inside it an inertia-stable nonzero subspace `U₀` of minimal
dimension.

- For each coordinate `k`, either all vectors of `U₀` vanish at `k`, or the projection
  to `k` is injective on `U₀`. Otherwise the intersection with the kernel would be
  smaller.
- Some coordinate projection is injective. Then `U₀` maps onto a nonzero
  inertia-stable subspace of the irreducible block `k`, so this projection is onto.
- Any other coordinate `j` on which `U₀` is nonzero would give a nonzero intertwiner
  between distinct blocks. Hence `U₀` is the full coordinate subspace of `k`.
- The operator of the lift, `cycUnit`, moves single-coordinate vectors to the
  neighboring coordinate (`cycUnit_single`, `single_mem_of_cycUnit`). Its iterates
  reach every coordinate (`exists_finRotate_iterate`), so `M` contains every
  coordinate subspace and is everything.

`pow_eq_one_of_twist_equiv` is the converse of `twist_equiv_of_pow_eq_one`, under the
same hypotheses: `V` nonzero and finite-dimensional over `ℂ`, irreducible blocks, and
no nonzero intertwiners between distinct blocks. If the
twist by `u^deg` is equivalent to the coinduction, the equivalence commutes with the
inertia action. Because `V` is finite-dimensional, `blockRep_endo_diag` (which relies
on Schur's lemma `end_scalar`) shows that it is diagonal with scalars `c k`.
Comparing with the lift gives `c(k+1) = u · c(k)` around the cycle of length `m + 1`.
Since `c 0 ≠ 0`, this forces `u^{m+1} = 1`.

Together with `CoindProps`, for a nonzero finite-dimensional complex carrier `V` with
irreducible, pairwise unrelated blocks, the twist stabilizer of the coinduction is
exactly the group of `(m + 1)`st roots of unity. This is the internal form of the
torsion statement in Henniart (1988), Proposition 2.2, which concerns
finite-dimensional representations.
