# Complex-place induction in stages for the identity Mackey constituent

`Langlands.Global.Harris.proposition48PrimeInducedParameterStages` proves
[`Proposition48PrimeInducedParameterStagesStatement`](HarrisProposition48MackeyTransportStatement.md)
with its original hypotheses and arbitrary universe `uF`. In particular, the
containment `D ≤ Q.conjugateField 1` suffices; no prime degree, weak induction,
regularity or archimedean bridge is assumed.

## Source and scope

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210
(`harris-1998-local-langlands`), gives the Mackey character on printed p. 202
and uses the identity constituent in the prime branch on p. 203. The
complex-place statement is an internal consequence of the parameter
formalization required by operator ruling R2
(`a79e2e832569567a8582b3c994f2fc1b`); see
`operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`
lines 908–912. It is not a separate assertion in Harris, whose Remark on
p. 202 (`math_9611226v1.tex` lines 1615–1628) notes that the proof omits the
infinity-type computation. This module does not prove the finite-place
weak-induction analogue.

## Implemented proof

1. Set `M := Q.mackeyField D 1` with the given inclusion from `D`. The
   [identity Mackey identification](HarrisProposition48IdentityMackey.md)
   gives an `E`-algebra equivalence `e : Q.E' ≃ₐ[Q.E] M` and proves that
   `HeckeCharacter.comap e.toRingEquiv (Q.mackeyCharacter D 1) = Q.ξ`.
2. `infinitePlacesTower` identifies the dependent sum of places of `M`
   over places of `D` above `v` with the places of `M` directly above `v`:
   restriction to `D` is unique. `infinitePlacesComap` restricts pullback
   along `e` to this fibre over `v`, since `e` commutes with the base
   maps. Composing with the supplied enumerations gives an equivalence
   `φ` from pairs of indices to places of `Q.E'` above `v`.
3. `readBlock` leaves a block unchanged if the upper selected embedding
   restricts to the lower selected embedding, and conjugates it otherwise.
   `hasComplexPlaceParameter_comap` computes the actual infinite component
   of the pulled-back character using `HeckeCharacter.comap_infiniteComponent`.
   The required coordinate equality, either with the lower selected
   embedding or its conjugate, extends from the field to its completion
   by continuity and density. Thus reading the supplied block of the
   Mackey character at index `φ.symm z` in the coordinates at `z` gives
   an actual parameter `dξ z` of `Q.ξ`.
4. `readBlock_comp` checks the four choices of matching or conjugate
   embeddings in a tower over a complex place. Conjugation commutes with
   restriction, and conjugating a block twice restores it. The two
   routes, through `D` or through `Q.E'`, therefore give the same block
   at `v`, because the two composed embeddings from `Q.E` into `M` use
   the same algebra map. There is no additional twist of the blocks.
5. `transport_eq_map` identifies the published transport of lists with
   mapping `readBlock`. Mapping each supplied permutation and then
   concatenating gives a permutation of the staged sum to the flattened
   list of blocks indexed by the pairs. `ofFn_sigma_perm` compares the
   complete, duplicate-free lists of **indices** before mapping to blocks,
   so repeated blocks retain their multiplicities. Enumerating the pairs
   and composing with `φ`, the block comparison gives exactly the direct
   `complexPlaceLanglandsSum` of the singleton lists `[dξ z]`. The
   resulting `List.Perm` and the actual parameters from step 3 furnish
   the witnesses in `Q.IsInducedComplexPlaceParameter`.
