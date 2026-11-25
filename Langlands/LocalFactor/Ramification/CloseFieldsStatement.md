# Close-fields comparison of ramification quotients

Let \(p\) be prime and \(F : \texttt{PadicField}\ p\). Write \(K\) for its carrier
with the canonical local-field data, \(k\) for its residue field, and
\(X = k((t))\) for the Laurent-series field with its \(t\)-adic topology.
The absolute ramification index \(e\) is the normalized order of \(p\) in \(K\),
given by `F.canonicalTopologicalData.ramificationIndex` and cast to `ℝ`.

## Galois form

`Langlands.Ramification.Local.CloseFieldsGaloisQuotientStatement` asserts that
there is an isomorphism of topological groups
\(\phi : G_K/G_K^e \simeq G_X/G_X^e\) carrying the image of \(G_K^v\) onto the
image of \(G_X^v\) for every real \(v\) with \(0 \le v \le e\). The superscripts
use Serre's upper numbering. The action of \(\phi\) on Frobenius is left
unspecified.

This is interface E1a in §4.3 of `external-inputs-plan.tex`
(`operator-external-inputs-plan-2026-11-16`, lines 572–575). Deligne's *Les corps
locaux de caractéristique p, limites de corps locaux de caractéristique 0*,
§3.5 (printed p. 144 in `bdkv-1984-representations-local-field`), gives the
Galois quotient comparison. The filtered form appears in Theorem `thm:Deligne`
in `numerical-LLC-route.tex` (`operator-numerical-llc-route-2026-11-16`,
lines 861–870). The plan note's Remark 4.1 (lines 586–609) gives a field-of-norms
route using Corollaire 3.3.6 (printed p. 77 in `wintenberger-1983-field-of-norms`).

## Weil form

`Langlands.Ramification.Local.CloseFieldsWeilQuotientStatement` asserts that
there is an isomorphism of topological groups
\(\psi : W_K/W_K^e \simeq W_X/W_X^e\) carrying the image of \(W_K^v\) onto the
image of \(W_X^v\) for every real \(v\) with \(0 \le v \le e\). Each \(W^v\)
is the preimage of \(G^v\) under the Weil group projection. Whenever \(w \in W_K\)
and \(w' \in W_X\) satisfy \(\psi([w]) = [w']\), their degrees are equal.
The degrees take values in `Langlands.Weil.Degree` (`Multiplicative ℤ`), with
geometric Frobenius of degree \(1\) in the underlying additive integers on
both sides. Unramified characters factor through these degrees.

The Weil form is the consequence of Theorem `thm:Deligne` stated at line 868
of `operator-numerical-llc-route-2026-11-16` and used in the proof of
`prop:LD` at line 827. Deligne's reciprocity compatibility for finite residue
fields (Proposition 3.6.1, printed p. 145 of his article) gives degree compatibility
when the truncated multiplicative groups are identified by matching units and
uniformizer classes.

## Lean objects

The \(K\) side uses `Field.absoluteGaloisGroup F.Carrier`, the automorphisms of
`AlgebraicClosure F.Carrier` over `F.Carrier`, and
`Langlands.Ramification.Padic.absoluteUpperRamificationGroup`. It uses
`Langlands.Weil.Local.localWeilGroup` and `localDegree` together with
`Langlands.VirtualRepresentation.LocalWeil.Ramification.upperGroup`.
These are the published p-adic objects of the Library.

The \(X\) side uses `LaurentSeries (Langlands.Weil.Local.localResidueField F)`
with `Langlands.LocalField.Laurent.valuativeRel`, `Laurent.localField`, and
the `localResidueField_finite` instance for its coefficient field. The absolute
Galois group is the group of \(X\)-automorphisms of `SeparableClosure X`.
The upper groups are `Langlands.Ramification.Local.localAbsoluteUpperRamificationGroup`.
The Weil group and degree come from `Langlands.Weil.Local.SepClosed`, and the
Weil upper groups from `Langlands.VirtualRepresentation.LocalWeil.SepClosed.Ramification`.

Each quotient has Mathlib's quotient topology from the Krull or Weil topology
on the corresponding group. The isomorphisms are `ContinuousMulEquiv`s and the
filtration images use `Subgroup.map` under `QuotientGroup.mk'`. The absolute
upper groups use the Library's normality instances. The two local Weil normality
instances use `Subgroup.Normal.comap` along the respective projections.
