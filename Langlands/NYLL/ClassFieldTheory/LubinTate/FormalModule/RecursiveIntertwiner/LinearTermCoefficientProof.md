# NYLL M353.043: proof of the low-degree coefficient comparison

This module proves the published proposition
`Langlands.NYLL.PortInternal.M353.d043Statement` as
`Langlands.NYLL.PortInternal.M353.d043`. It imports the exact
`RecursiveIntertwiner.LinearTermCoefficientStatement` module and reuses its
shared `LocalField`, `linearForm` and `HasLinearTerm` definitions.

## Statement and parameters

For independent universes `u`, `v` and `w`, let `K : Type u` be a field,
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
and `sigma : Type w` have a `Fintype` instance. Given
`H : MvPowerSeries sigma F.valuationSubring` and
`L : sigma → F.valuationSubring`, assume `HasLinearTerm H L`.
For every exponent `d : sigma →₀ ℕ` with `d.degree < 2`, the theorem states
that `MvPowerSeries.coeff d H = MvPowerSeries.coeff d (linearForm L)`.
Thus the two series agree in total degrees zero and one.

The field, local field, variable type, series and coefficient function remain
implicit; the field and `Fintype` instances remain instance binders. The
hypothesis `hH`, exponent `d` and degree bound `hd` are explicit, in source
order. The unused source section parameter `pi` is absent from the effective
telescope. No uniformizer or Lubin–Tate-series hypothesis occurs here.
The final Lean example assigns the entire unapplied theorem, with all three
universe arguments, to the exact published proposition.

## Implemented proof

By the imported definition, `hH` is the bound
`(2 : ℕ∞) ≤ (H - linearForm L).order`. The proof casts `d.degree < 2` from
natural numbers to `ℕ∞` with `exact_mod_cast`, obtaining `hd'`.
Transitivity gives
`(d.degree : ℕ∞) < (H - linearForm L).order`.
Mathlib's `MvPowerSeries.coeff_of_lt_order` then says that the coefficient
of `H - linearForm L` at `d` is zero. Rewriting this equality with `map_sub`
and `sub_eq_zero` gives the required equality of coefficients.
This is the original six-line proof. It requires no predecessor theorem
from the recursive-intertwiner construction.

## Source and modification record

The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
private theorem
`LubinTate.SameUniformizer.coeff_eq_linearForm_of_hasLinearTerm`,
unit M353.043. Its signature is at lines 893–899, its proof at 900–905,
and its effective section parameters at 29 and 34–38. The file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.

The readable source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the current `notes/errata/`.

Worker 344 extracted this proof on 14 November 2026, replaced the private
source name by the assigned public `PortInternal.M353.d043` name, placed
the section parameters directly in its declaration, and replaced the
source's two broad recursive imports by the exact published target module.
The new module documentation, theorem docstring and complete-type example
describe and check this focused result. The original proof body, source
universes, binder kinds, hypotheses and conclusion are retained. There are
no patch10 changes, new definitions or new instances.

The original copyright, Apache-2.0 release and author header are retained
verbatim. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are preserved unchanged.
