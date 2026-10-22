# Proof of the all-degree Tate cup laws

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

`Langlands.Tate.cupLaws` proves exactly `CupLaws` in arbitrary universe `u`.
It assembles the normalization and naturality theorems of `CupProof`, the
boundary theorems of `CupBoundary` and `CupBoundarySecond`, and the subgroup
compatibility theorems of `CupTransfer`.

The normalization unfolds the construction at bidegree `(0,0)`. Naturality
is propagated through the canonical shifts of both coefficient modules.
The first boundary formula follows by shifting the second degree from zero;
the second follows by shifting the first degree, with anticommutation of
the connecting maps producing the factor `(-1)^p`. These formulas retain
exactly the short exactness of the original and tensor sequences.
Restriction and projection follow from invariant representatives at second
degree zero and dimension-shift induction for the second coefficient.

The imported paired Markdown explains these arguments in detail.
`CupStatement.md` records the original source and the scope of the exact
proposition. This theorem does not assert associativity, graded commutativity,
or comparison with ordinary cochain cup products. Those statements are outside
`CupLaws`.

The target and all its construction dependencies are imported unchanged.
The proof keeps the arbitrary common carrier universe `u` and introduces
no additional hypotheses on the coefficients. Its general commutative-ring
form extends the integral tensor setting of Serre VIII §3, Proposition 5;
the Lean proof supplies this extension directly.

Source: Jean-Pierre Serre, *Local Fields* (1979), VII §7 and VIII §§1–3,
especially VIII §3, Proposition 5(i)–(iv), printed pp. 131–132
(PDF pp. 137–138). Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
