# Pole-to-pairing comparison for actual witnessed relative pairs

This module proves
`Langlands.Global.PoleComparison.RelativePolePairingStatement`
as the theorem `Langlands.Global.PoleComparison.relativePolePairing`.
The theorem keeps the statement's three independent universe parameters:
`uF` for the number fields, `uW` for the Weil-representation carriers and
`uP` for the presentation factors. The proof specializes the published
generic results of `Langlands.Global.Factors.PolePairingDescentProof` to
the existing generator index
`Langlands.VirtualRepresentation.RelativeGlobal.WitnessedGenerator F E c v`.

## Two degree identities

The private theorems `localWeil_unitaryDegree_eq` and
`padicSupercuspidal_unitaryDegree_eq` show that the existing degree maps
`LocalWeil.unitaryDegree` and `PadicSupercuspidal.unitaryDegree` equal the
generic `degree` with weight `b ↦ (b.val.1 : ℕ)`. Each unitary basis element
lies in a ranked basis, and `b.val.1` is its positive rank. Both sides are
`ℤ`-linear maps on a free integral lattice, so `integral_hom_ext` reduces
each identity to basis vectors. On a basis vector both sides unfold by
`simp` to the same rank.

## Main proof

Fix the fields `F` and `E`, the class family `c`, the place `v`, the
additive character `ψ`, and the hypothesis
`RelativeCertifiedPoleComparisons F E c v ψ`. The proof takes the
self-dual measure `ν` given by its first component. The second component,
applied to `ν`, gives certified data `d : RelativePairFactorData` together
with `RegularPairComparisonsAt d.comparison 0` and the two
`RealizesPairingAtZero` formulas. These formulas are for the generator
families `left j = j.weilElement` and `right j = j.automorphicElement`.
The distinguished functions of `d.comparison` are, by definition, the actual
arithmetic pair L-factor with dualized second input and the certified
automorphic pair L-factor, both evaluated at `X = q^(-s)`. The proof only
passes these data to the generic theorems and does not unfold them.

1. **Gram equality.** The published `poleGramComparison` applied to
   `left`, `right`, `d.comparison` and the three hypotheses gives
   `pairing (left j) (left k) = pairing (right j) (right k)` for all
   generators `j` and `k`. This is the first conclusion, since
   `LocalWeil.unitaryPairing` and `PadicSupercuspidal.unitaryPairing` are
   the generic `pairing`.
2. **Generator degrees.** Let `sourceWeight` and `targetWeight` be the
   rank weights on the Weil and supercuspidal unitary bases. For each
   generator `j`, the two degree identities rewrite the published
   `WitnessedGenerator.degrees_eq` into
   `degree targetWeight (right j) = degree sourceWeight (left j)`.
3. **Generic descent.** The published `generatedPositiveIsometry_of_gram`
   applied to the Gram and degree equalities gives
   `relations left = relations right`, which is the second conclusion. It
   also gives an equivalence `T` from `generated left` to `generated right`
   that satisfies `GeneratedPositiveIsometry` and is the unique such
   equivalence. These spans are by definition `weilImage F E c v` and
   `automorphicImage F E c v`.
4. **Concrete existence.** `T` satisfies
   `RelativeGeneratedPositiveIsometry`. Rewriting the generator-image clause
   by `evaluateGenerators_generator` gives the concrete clause
   `T ⟨j.weilElement, _⟩ = ⟨j.automorphicElement, _⟩`. The pairing clause
   transfers unchanged. The degree identities turn the generic degree clause
   into the clause for the existing degree maps. They also rewrite the
   positive-degree hypothesis of the norm-one clause before the generic
   clause is applied.
5. **Uniqueness.** Let `S` satisfy `RelativeGeneratedPositiveIsometry`. The
   same rewrites in the reverse direction show that `S` satisfies
   `GeneratedPositiveIsometry`. The uniqueness part from step 3 then gives
   `S = T`.

## Hypotheses that are used and unused

The proof uses the self-dual measure given by the existence premise. It then
uses the certified data, regularity conditions and pole formulas for that
one measure. The hypothesis that certified data exist for every self-dual
measure stays in the statement unchanged. The arithmetic class-family
premise `RelativeWeilGroup.IsArithmeticClassFamily c` is introduced but not
used. The relative Weil representations, characterized local maps,
cuspidal realizations, presentations, effective expansions and support
certificates enter only through the structure fields of `WitnessedGenerator`.
In particular, they enter through the published `degrees_eq`.
Because the degree hypothesis is used only as an equality, the positivity
of `rankIndex + 1` plays no further role.

## Provenance and scope

The Lean proof was written by Worker 64 in the shared H1 draft of task
`205503d3-82c7-4b1a-a4f0-90d02bbe9a2e` and is reused here unchanged. It is
the derived actual-interface adapter of the pole-order and integral-descent
argument of Henniart (2000), §§2.5–2.8, printed pp.445–448. The concrete
formulation is internal, as explained in the statement's Markdown.

The statement's analytic inputs remain hypotheses. These are meromorphy of
both distinguished factors at zero, the omitted local units, the separate
boundary units, equality of the completed punctured germs, and both signed
pole formulas. The proof does not construct global functional equations,
highly ramified stability, boundary nonvanishing or local pole formulas. It
does not show that the generated spans exhaust either ambient lattice, and
it gives no surjectivity on basis indices. It is not a proof of
`AssociatedFactorStatement`.
