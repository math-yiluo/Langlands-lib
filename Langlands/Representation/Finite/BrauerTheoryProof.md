# Proof of the finite complex Brauer theory statement

Author: Worker 84, who wrote the proof and this explanation.

This file proves the Library proposition `Langlands.FiniteRep.FiniteBrauerTheoryStatement`
(module `Langlands.Representation.Finite.BrauerStatement`). The target is unchanged and keeps its
hypotheses: `G` is a group in universe `uG` with a `Fintype` instance.

| Theorem in `Langlands.FiniteRep.BrauerTheory` | Proves |
| --- | --- |
| `virtualCharacter_brauerExpansion` (implicit `G`) | the character of `brauerExpansion G c` is `Finsupp.linearCombination ℤ inducedCharacter c` |
| `spanning` (implicit `G`) | `IntegralBrauerSpanningStatement G` |
| `finiteBrauerTheory` (explicit `G`) | `FiniteBrauerTheoryStatement G` |

`FiniteBrauerTheoryStatement G` is the conjunction of seven statements: `FiniteRankOneOrderStatement G`,
`FiniteInducedCharacterFormulaStatement G`, `FiniteInducedDegreeStatement G`,
`FiniteVirtualCharacterFaithfulnessStatement G`, `FiniteIrreducibleBasisStatement G`,
`IntegralBrauerSpanningStatement G` and `IntegralBrauerCharacterLatticeStatement G`. This module proves the
spanning conjunct and assembles the other six from their proofs in the imported modules. The proof adds no
hypotheses or axioms; the declaration check of `finiteBrauerTheory` reports only `propext`, `Classical.choice`
and `Quot.sound`.

The spanning conjunct is Brauer's induction theorem stated in the representation group: every virtual complex
representation of a finite group is a signed integer sum of classes of representations induced from
one-dimensional representations of subgroups. Henniart uses it in this form (*Une preuve simple des conjectures
de Langlands pour GL(n) sur un corps p-adique*, 2000, §3.7, p.451). In Jean-Pierre Serre, *Linear Representations
of Finite Groups*, GTM 42, Springer, 1977, §10.5 (literature ID `serre-1977-linear-representations`), Theorem 20
is the character form; the representation-group form follows because characters determine virtual
representations.

## Imports

- `Langlands.Representation.Finite.BrauerLatticeProof` (Worker 84), for
  `Langlands.FiniteRep.BrauerLattice.characterLattice : IntegralBrauerCharacterLatticeStatement G`: the `ℤ`-span
  `inducedCharacterLattice` of the induced characters `inducedCharacter d` equals the image `virtualCharacters`
  of the character map. Through it come `Langlands.Representation.Finite.InducedCharacterProof` (Worker 84), with
  `InducedCharacter.rankOneOrder`, `InducedCharacter.inducedCharacterFormula` and `InducedCharacter.inducedDegree`,
  and the target module `Langlands.Representation.Finite.BrauerStatement`.
- `Langlands.Representation.Finite.VirtualCharacterProof` (Worker 84), for
  `Langlands.FiniteRep.VirtualCharacter.faithfulness : FiniteVirtualCharacterFaithfulnessStatement G` (the map
  `virtualCharacter` is injective) and `VirtualCharacter.irreducibleBasis : FiniteIrreducibleBasisStatement G`.

From the public module `Langlands.Representation.Finite.Virtual` the proof uses `virtualCharacter`,
`virtualCharacter_ofClass`, `inducedCharacter` and `inducedCharacterLattice`. From Mathlib it uses
`Finsupp.apply_linearCombination`, `Finsupp.mem_span_range_iff_exists_finsupp` and
`Finsupp.linearCombination_apply`.

## Proof

- `virtualCharacter_brauerExpansion c`. By definition, `brauerExpansion G` is
  `Finsupp.linearCombination ℤ` of the family `d ↦ ofClass (induce d.1 (classOf (oneDimensional d.2)))`. A linear
  map applied to a linear combination is the linear combination of the composite family
  (`Finsupp.apply_linearCombination`). Composing with `virtualCharacter` gives the family
  `d ↦ character (induce d.1 (classOf (oneDimensional d.2)))` by `virtualCharacter_ofClass`. That is
  `inducedCharacter d` by definition.
- `spanning`. Let `x` be a virtual representation. Its character `virtualCharacter x` lies in `virtualCharacters`,
  the range of `virtualCharacter`. By `characterLattice` it therefore lies in `inducedCharacterLattice`, the span
  of the range of `inducedCharacter`. By `Finsupp.mem_span_range_iff_exists_finsupp` there is
  `c : MonomialDatum ℂ G →₀ ℤ` with `c.sum (fun d n => n • inducedCharacter d) = virtualCharacter x`. By
  `virtualCharacter_brauerExpansion` and `Finsupp.linearCombination_apply`, the left side is the character of
  `brauerExpansion G c`. Faithfulness then gives `brauerExpansion G c = x`.
- `finiteBrauerTheory G` is the tuple of `InducedCharacter.rankOneOrder G`,
  `InducedCharacter.inducedCharacterFormula`, `InducedCharacter.inducedDegree G`, `VirtualCharacter.faithfulness`,
  `VirtualCharacter.irreducibleBasis`, `spanning` and `BrauerLattice.characterLattice`, in the order of the
  conjuncts.
