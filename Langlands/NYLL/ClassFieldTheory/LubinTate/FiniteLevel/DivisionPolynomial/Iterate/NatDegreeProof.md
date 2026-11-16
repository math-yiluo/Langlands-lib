# Exact degree proof for standard Lubin–Tate polynomial iterates (M339.011)

This module proves
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_natDegreeStatement`
under the theorem name
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_natDegree`.
Its type is the fully applied imported target:

```lean
{K : Type u} [Field K]
(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K)
(π : F.valuationSubring) (n : ℕ) :
  Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_natDegreeStatement F π n
```

The universes `u` and `v` are independent. Write
`q = Nat.card F.residueField` and
`f = standardLubinTatePolynomial F π = X ^ q + C π * X`.
The assertion is that the `n`-fold compositional iterate of `f`, starting
from `X`, has natural degree `q ^ n`. The element `π` is arbitrary:
no uniformizer, nonzero or additional finiteness hypothesis is present.

## Implemented proof

The proof first establishes a local equality `hdegree : f.natDegree = q`.
The natural degree of `C π * X` is at most `1`, by
`Polynomial.natDegree_C_mul_X_pow_le π 1` and `pow_one`.
The residue field is a finite nontrivial field: finiteness comes from
the published `LocalField.residueFinite` instance, and nontriviality
comes from its field structure. Consequently `Finite.one_lt_card`
gives `1 < q`. This proves that the second summand has strictly smaller
natural degree than `X ^ q`. The proof uses
`Polynomial.natDegree_add_eq_left_of_natDegree_lt` and
`Polynomial.natDegree_X_pow` to obtain `hdegree`.

It then unfolds the imported proposition target and the published iterate
definition, which is `f.comp^[n] Polynomial.X`. Mathlib's
`Polynomial.natDegree_iterate_comp` gives
`f.natDegree ^ n * Polynomial.X.natDegree`. Rewriting with `hdegree`,
`Polynomial.natDegree_X` and `mul_one` proves `q ^ n`.
This also covers `n = 0`, where the starting polynomial `X` has degree `1`.
The valuation subring inherits the domain structure needed by the
Mathlib composition-degree formula.

The only imports are the unchanged published iterate `Statements`
module and `Mathlib.Algebra.Polynomial.Degree.Lemmas`. No new data,
statement definitions or auxiliary public theorem is introduced.
The base-degree calculation is local to this proof.

## Source and modifications

The proof is adapted from Naganori Yamaguchi's NYLL ClassFieldTheory,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`.
M339.011 is declared at line 156, with its type at lines 157–159 and
proof at lines 160–163. The local base-degree argument comes from
M339.006, declaration line 101 and proof lines 105–114.
The source file SHA-256 is
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
The readable original is in the registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Changes from upstream are the `Langlands.NYLL` namespace prefix, the
fully applied published proposition as the theorem's type, the initial
unfolding of that target, the inline local copy of the base-degree
calculation, the focused imports, and this module's documentation.
The original copyright, Apache-2.0 notice and authorship are preserved
in the Lean header. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged. The published target and all
its imported Lean/Markdown pairs remain unchanged.
