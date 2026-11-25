# Exact functors preserve the connecting morphism of the homology sequence

Module `Nyll.SchemeTheory.HomologicalAlgebra.HomologySequenceExactFunctor`, copied from the Lean library NYLL with one theorem renamed (see "Renamed declarations"). The origin of the file is given at the end of this page.

Let `F : C ⥤ D` be an additive functor between abelian categories that preserves finite limits and finite colimits. The file shows that Mathlib's comparison isomorphisms `H(F K) ≅ F(H K)` are compatible with the structure maps of homology and, as a consequence, that `F` carries the connecting morphism of the homology long exact sequence of a short exact sequence of complexes to the connecting morphism of the image sequence.

## Main results

- `ShortComplex.pOpcycles_mapOpcyclesIso_hom`, `ShortComplex.homologyπ_mapHomologyIso_hom_of_exact`, `ShortComplex.mapHomologyIso_hom_homologyι`: for a short complex `S`, the isomorphisms `mapOpcyclesIso`, `mapCyclesIso` and `mapHomologyIso` commute with the projection to opcycles, the projection from cycles to homology, and the inclusion of homology into opcycles.
- `HomologicalComplex.map_opcyclesToCycles`: for a complex `K`, the map from opcycles in degree `i` to cycles in degree `j` commutes with these comparison isomorphisms.
- `ShortComplex.ShortExact.map_δ_eq`: for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of complexes and `c.Rel i j`, the connecting morphism `δ : H_i(F X₃) → H_j(F X₁)` of the image sequence, composed with `H_j(F X₁) ≅ F(H_j X₁)`, equals `H_i(F X₃) ≅ F(H_i X₃)` followed by `F(δ)`.

## Proofs

The connecting morphism is characterised through the pullback in Mathlib's snake-lemma input: given the pullback projections and a lift to cycles satisfying the two compatibilities, `δ` is determined (`δ_eq'`). The file applies `F` to the original pullback projections, transports them with the comparison isomorphisms, checks the compatibilities with the first four results, and cancels the epimorphism given by the second pullback projection.

## Points to watch

- `F` must be exact on both sides (preserving finite limits and colimits) as well as additive.
- The result is a compatibility square up to Mathlib's existing comparison isomorphisms, for the connecting map Mathlib already defines; no new connecting map is chosen.

## Renamed declarations

| In the source | In this file | Why |
|---|---|---|
| `CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom` | `CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom_of_exact` | the library weil-conjectures declares a theorem of the same name, with other hypotheses (`[F.PreservesHomology]`), in `WeilConjectures/Mathlib/Algebra/Homology/SingleHomology.lean`; Lean refuses to import both declarations together |

The statement and proof are unchanged; the one use of the theorem, in the proof of `ShortComplex.ShortExact.map_δ_eq`, calls it by the new name. The rename is also listed in `NYLL-RENAMES.tsv`.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/SchemeTheory/HomologicalAlgebra/HomologySequenceExactFunctor.lean`. The Lean file is the source byte for byte except for the rename above (SHA-256 of the source, as recorded in `NYLL-MANIFEST.tsv`: `a1e42358c7f9b0ecd0be482afd2a869cebe28590864de05a2a06de05581d7166`; of this file: `caeac501d13d204e0fefeffb5462bcd2db9f2a223788f2f7a906c01140d381a6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
