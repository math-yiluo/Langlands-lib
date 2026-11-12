# Rational-character tensors identify the actual complex image dual

Author: Worker 4636.

Module: `Langlands.Representation.Plancherel.RationalCharacterTensorParameterProof`.

`Langlands.Plancherel.rationalCharacterTensorParameterBijective` proves exactly
the published proposition
`Langlands.Plancherel.RationalCharacterTensorParameterStatement.{u}` (module
[`RationalCharacterTensorParameterStatement`](RationalCharacterTensorParameterStatement.md))
at every universe `u`, with no hypotheses. It belongs to task
`a34dad15-286e-41e2-95c7-2ef8c2110901`.

So for every nonarchimedean local field `F : Type u` (instances `Field`,
`ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField`, any
characteristic) and every connected reductive group scheme `G` over `Spec F`,
the existing canonical complex-linear map

\[
\mathbb C\otimes_{\mathbb Z}X^*(G)
  \longrightarrow \operatorname{Hom}_{\mathbb Z}(\Lambda(G),\mathbb C),
\qquad
s\otimes\chi\longmapsto\bigl(a\longmapsto s\,a(\chi)\bigr),
\]

that is, `rationalCharacterTensorParameter G`, is bijective. Here `X^*(G)` is
`GroupScheme.rationalCharacters G` and `Λ(G)` is the actual
`rationalDiscreteValuationImage G`. The theorem adds no rank, splitting,
characteristic-zero, character-restriction or bijectivity premise. It
introduces no new map, lattice or pairing.

## Implemented proof

The proof is a short assembly of three published Library results.

1. `rationalCharacterTensorParameterStatement_of_detects` (module
   `Langlands.Representation.Plancherel.RationalCharacterTensorParameterReduction`)
   reduces the target to *valuation detection*,
   `RationalValuationDetects G`, for every connected reductive `G` over every
   nonarchimedean local field in universe `u`. That predicate says that every
   nonzero rational character `χ` has a rational point `g` with
   `(rationalCharacterValuation G g).toAdd χ ≠ 0`. The reduction proves
   surjectivity of the map unconditionally: it extends functionals from the
   image `Λ(G)` to the integer dual of `X^*(G)`, using that `ℂ` is divisible.
   It proves injectivity from detection, by flatness of `ℂ` over `ℤ` and
   finite freeness of `Λ(G)`. The proof applies this reduction with
   `refine` and then introduces `F`, its four instances, `G`,
   `hG : IsConnectedReductive G`, a character `χ` and `hχ : χ ≠ 0`.
   Unfolding `RationalValuationDetects` is definitional, so the remaining
   goal is the existence of a rational point with nonzero valuation on `χ`.
2. `RationalValuationDetection.exists_rationalCharacterValuation_ne_zero_of_centralTorusCharacter`
   (module `Langlands.Representation.Plancherel.RationalValuationDetection`)
   closes exactly this goal from `CentralTorusCharacterStatement.{u}`, `hG`
   and `hχ`. Its proof takes a torus `i : Z ⟶ G` on which `χ` restricts
   nontrivially. It then finds a cocharacter `φ : 𝔾_m ⟶ Z` on which the
   restriction is still nonzero. The image under `φ ≫ i` of a uniformizer
   point of the split torus `𝔾_m` is a rational point of `G` whose valuation
   on `χ` is that nonzero integer pairing.
3. The hypothesis `CentralTorusCharacterStatement.{u}` is supplied by the
   unconditional Library theorem `Langlands.GroupScheme.centralTorusCharacter`
   (module `Langlands.GroupScheme.Rational.CentralTorusCharacterProof`). It
   holds for connected reductive groups over every field, and the proof uses
   it at the local field `F`.

So no step of the proof takes an unproved structural statement as a
hypothesis. The proof does not use `CentralSplitTorusCharacterStatement`,
`CharacterRestrictionStatement` or the split-component valuation-image
comparison. Those remain separate obligations with their own owners.

## Relation to the literature

This is the linear identification of David Renard, *Représentations des
groupes réductifs p-adiques* (French version dated 9 July 2026), V.3.19–V.3.20,
printed pages 115–116 / PDF pages 121–122, as recorded in the statement's
Markdown. Renard gets the identification from the fact that the split
component, the image `Λ(M)` and the cocharacter lattice have the same rank.
The Lean proof uses only the part of that fact the complex identification
needs. The integer pairing between `X^*(G)` and `Λ(G)` must be nondegenerate
on the character side. The proof gets this from central tori and cocharacters
of `𝔾_m`, not from the split component.

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
