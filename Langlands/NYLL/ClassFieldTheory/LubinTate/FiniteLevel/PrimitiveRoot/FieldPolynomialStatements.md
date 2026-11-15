# Field primitive polynomial: monicity, degree and irreducibility targets (M341.005–.007)

Three Prop-valued definitions state the source theorems about
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField`,
the image in `Polynomial K` of the level-`n + 1` primitive division
polynomial. Write `q = Nat.card F.residueField`. All three have independent
universes `u v` and implicit `{K : Type u} [Field K]`, with the shared
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`.
With prefix `Langlands.NYLL.LubinTate`:

| Source unit | Declaration | Parameters | Proposition |
| --- | --- | --- | --- |
| M341.005 | `standardLubinTatePrimitivePolynomialOverField_monicStatement` | explicit `F`, `π : F.valuationSubring`, `n : ℕ` | `(standardLubinTatePrimitivePolynomialOverField F π n).Monic` |
| M341.006 | `standardLubinTatePrimitivePolynomialOverField_natDegreeStatement` | explicit `F`, `π`, `n` | `(standardLubinTatePrimitivePolynomialOverField F π n).natDegree = (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n` |
| M341.007 | `standardLubinTatePrimitivePolynomialOverField_irreducibleStatement` | implicit `{F}`, `{π}`, explicit `_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`, explicit `n` | `Irreducible (standardLubinTatePrimitivePolynomialOverField F π n)` |

The first two targets have no uniformizer hypothesis, as in the source; they
assert monicity and degree `(q - 1) q ^ n` for every `π` in the valuation
ring. The third requires that the image of `π` in `K` be a uniformizer for
the chosen valuation `F.toCompleteDVF.valuation`, in Mathlib's
`Valuation.IsUniformizer` sense: its valuation equals the generator `< 1`
of the value group supplied by the `Valuation.IsRankOneDiscrete` instance,
which comes from the package's stored complete-discreteness
(`Valuation.IsCompleteDiscrete.isRankOneDiscrete`). The proof argument `_hπ` is retained although the proposition
does not mention it, so that a proof has the source's outer telescope.
Irreducibility is `Irreducible` in the commutative monoid `Polynomial K`.

These are Prop-valued definitions only. This pair supplies no proof, simp
attribute or instance, and the targets do not by themselves establish
monicity, the degree or irreducibility.

## Original source and modifications

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`:
M341.005 lines 90–94 (statement 91–93, proof 94);
M341.006 lines 96–105 (statement 98–102, proof 103–105);
M341.007 lines 107–120 (statement 109–112, proof 113–120);
universe and variable context at lines 32–42. Source file SHA-256:
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
Registered sources `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 421 made these changes:

- replaced each theorem by a definition returning `Prop`, with `Statement`
  appended to the source name, and omitted the source proofs;
- renamed the unused proof binder `hπ` of M341.007 to `_hπ`, keeping its
  type, position and explicitness;
- prefixed the namespace `LubinTate` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` with `Langlands.NYLL`;
- extracted only these three units into this focused module, with new
  docstrings and a header modification note;
- imported only the published definition module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomial`
  and `Mathlib.Algebra.Group.Irreducible.Defs` for `Irreducible`.

Source universes, binder order and explicitness, types and conclusions are
otherwise unchanged. The original copyright, Apache-2.0 release line and
author line remain in the Lean header; `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` retain licensing and attribution and are not modified.
