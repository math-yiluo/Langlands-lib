# Extension of inertia types to the stage

General lemmas:

- `isIrreducible_of_comp`: if `ρ ∘ c` is irreducible, then so is `ρ`.
- `isIrreducible_twist`: character twists preserve irreducibility.
- `equivComp`: an equivalence remains an equivalence after precomposition.

For a stage `S` of degree `m + 1`, `κ` maps base inertia into stage inertia
(`κ_mem`), because `ι(κ n) = n` has degree `0 = (m+1) · deg(κ n)`. In the other
direction `ι` maps stage inertia into base inertia (`ι_mem`). The restrictions `κJ`
and `ιJ` are mutually inverse group isomorphisms between the two inertia groups.
`ιJ` is continuous, and it transports conjugation by `E.lift` to conjugation by
`lift^{m+1}` (`ιJ_conj`).

`exists_extension` takes an inertia representation `x` together with an equivalence
`x ∘ conj(lift^{m+1}) ≅ x`. It produces a representation `τ` of `H` with:

- first block `S.block τ 0 = x`;
- restriction to stage inertia `x ∘ ιJ`;
- continuity whenever `x` is continuous, provided `H` is a topological group and `V`
  is finite-dimensional over `ℂ`.

The first two properties need no finiteness of `V`.

The proof transports the equivalence along `ιJ`, obtains an operator from
`exists_compatibleOperator`, and uses `SplitDegree.extend` for `E`.

`unramifiedCharacter_ι` records that the unramified character of `D` with parameter
`u`, pulled back along `ι`, is the unramified character of `E` with parameter
`u^{m+1}`.

The extension step is the classical extension of a Frobenius-stable inertia type to
the corresponding unramified extension, as in the proof of Henniart (1988),
Proposition 2.2.
