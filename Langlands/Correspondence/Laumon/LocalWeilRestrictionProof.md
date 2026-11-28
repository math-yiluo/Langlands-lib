# Restriction to the local Weil group of `k((t))`: proof

Module `Langlands.Correspondence.Laumon.LocalWeilRestrictionProof`. The theorem
`Langlands.Henniart.Laumon.localWeilRestriction` proves
`Langlands.Henniart.Laumon.LocalWeilRestrictionStatement` (module
`Langlands.Correspondence.Laumon.UnramifiedLines`) at its universe parameters `u`, `uW`.

## The statement

Let `k` be a finite field, `ℓ` a prime, `X = LaurentSeries k` (with the Library's
`Langlands.LocalField.Laurent.valuativeRel` as a local instance) and `Ω_X = SeparableClosure X`.
Let `A`, `B` be in `FiniteRepresentation.{0, u, uW} E Gal(Ω_X/X)`, `E = PadicAlgCl ℓ`, and
satisfy `IsLadicContinuous`. Restriction along
`Langlands.Weil.Local.SepClosed.localProjection X Ω_X` from the Library's local Weil group:

1. preserves and reflects the intertwining property of a linear map `A → B`;
2. preserves and reflects `FiniteRepresentation.IsIsomorphic`;
3. preserves and reflects `Representation.IsIrreducible`;
4. preserves and reflects `IsLadicDefinedOverFiniteExtension`.

## The proof

After introducing `k`, `ℓ`, `A`, `B` and the two continuity hypotheses, the proof applies
`Langlands.Henniart.LocalNumerical.ladicRestriction_of_denseRange` (module
`Langlands.Correspondence.HenniartLadicDenseRestriction`) with:

- `φ = (localProjection X Ω_X).toMonoidHom`, the homomorphism along which the statement
  restricts;
- the density `Langlands.Weil.Local.SepClosed.localProjection_denseRange X Ω_X` (module
  `Langlands.Weil.Local.SepClosedTopology`): the image of `localProjection` is dense in the
  Krull topology of `Gal(Ω_X/X)`.

`ladicRestriction_of_denseRange` gives the four clauses for any group with a topology and any
homomorphism with dense image. Its proof is as follows. For a continuous action, the set of
group elements at which a linear map intertwines, at which a subspace is stable, or at which a
matrix entry lies in a closed set is closed. A closed set containing a dense image is
everything. A finite extension of `ℚ_ℓ` in `E` is closed in `E`. The closedness lemmas are in
`Langlands.Weil.Representation.DenseRestriction`.

The comparison is not taken from a source. Henniart (1988), §1.1, p. 497, distinguishes the
Weil group `W_K` from the Galois group `G_K`, and §4.1, pp. 509–510, defines ℓ-adic
representations of `G_K` as continuous representations defined over a finite extension of
`ℚ_ℓ`. The page `UnramifiedLines.md` describes the density argument.

## Axioms

`#print axioms Langlands.Henniart.Laumon.localWeilRestriction` lists only `propext`,
`Classical.choice` and `Quot.sound`.

## Imports

The module imports `Langlands.Correspondence.Laumon.UnramifiedLines` (the statement),
`Langlands.Correspondence.HenniartLadicDenseRestriction` and
`Langlands.Weil.Local.SepClosedTopology`. It imports no Mathlib module directly.
