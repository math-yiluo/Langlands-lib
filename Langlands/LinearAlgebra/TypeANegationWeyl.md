# An additive weight residue in simply connected type A

Let `P` be an integral root datum on arbitrary additive commutative groups
`X` and `Y`, let `b` be a base, and let `e : b.support ≃ Fin n` number its
simple roots. The construction `residue P b e : X →+ ZMod (n+1)` is

`x ↦ Σ i, (i.val+1) * ⟨x, coroot (e.symm i)⟩ mod (n+1)`.

The construction itself needs neither a Cartan hypothesis nor spanning
coroots. With every numbered Cartan entry equal to `CartanMatrix.A n`,
`residue_simple` and `residue_root` prove that the residue vanishes on every
simple root and every root. `residue_weyl` then proves that every element of
the full integral Weyl group preserves the residue of every weight.

If the coroots span the entire coweight lattice, `firstWeight` constructs
the first fundamental weight in the full weight lattice: its pairings with
the simple coroots are one at the vertex numbered zero and zero elsewhere.
This requires `0 < n`. Its residue is exactly one.
`negAut_not_mem_weylGroup` concludes that, when `2 ≤ n`, simultaneous
negation on the two full lattices is not in the integral Weyl group.
All these statements allow independent universes for the indices and the
two lattices. They require no group realization or field assumptions.

The proof is an internal calculation from the imported integral root-datum,
base, Weyl-group and Cartan definitions. `cartan_entry` separates a row into
the diagonal and two neighboring entries. The two finite-sum lemmas then
give

`Σ i, (i.val+1) * A_n(a,i) = if a.val+1=n then n+1 else 0`.

Reduction modulo `n+1` kills this value. The integral simple-root expansion
provided by a base extends the vanishing to every root. The reflection
formula `x ↦ x - ⟨x,α∨⟩ α` and induction over Weyl products establish
invariance. The perfect pairing and `IntegralWeylVector.corootBasis`
construct the first fundamental weight by specifying its integral values
on that coroot basis. If negation were Weyl, invariance at this weight would
give `-1 = 1` in `ZMod (n+1)`. The elementary characterization of that
equality forces `n+1` to be one or two, contradicting `2 ≤ n`.

This focused prerequisite does not identify the actual Tits-index
opposition with reversal, locate its distinguished vertices, or prove the
local rank-one enumeration. It uses no downstream classification theorem.
