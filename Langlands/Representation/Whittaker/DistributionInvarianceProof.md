# Shalika invariance of Whittaker bi-equivariant distributions: proof

Author: Worker 634.

`Langlands.Whittaker.shalikaDistributionInvariance.{uF}` proves exactly the
published proposition
`Langlands.Whittaker.ShalikaDistributionInvarianceStatement.{uF}` from
`Langlands.Representation.Whittaker.DistributionInvarianceStatement`.
The target and its imported Lean/Markdown pairs are unchanged.

The theorem retains every prime `p`, every `F : PadicField.{uF} p` in the
arbitrary universe `uF`, its canonical normed field and topology, every
`n : ℕ` and thus every positive rank `n + 1`, every bundled unitary additive
character `ψ`, and every full complex algebraic distribution `D` on the
actual matrix group `G = GeneralLinear (n + 1) F.Carrier`. The sole premise
is the published `IsBiEquivariantDistribution ψ n D`; the conclusion is
`IsWeylTransposeInvariant n F.Carrier D`. No continuity of the distribution,
representation, auxiliary support or cell-stability hypothesis is added.

Write `U` for the actual upper unipotent subgroup, `χ = standardCharacter ψ n`
and `τ = weylTransposeHomeomorph n F.Carrier`. The conventions are exactly
those of the target:

\[
D\bigl(g\mapsto f(u_1 g u_2)\bigr)=\chi(u_1)\chi(u_2)D(f),
\qquad \tau(g)=Jg^tJ,
\qquad (\tau_*D)(f)=D(f\circ\tau).
\]

Here `J` is the long-Weyl matrix. Both character factors are positive, and
the conclusion is `τ_*D = D`.

## Published prerequisites

Besides the target, this module imports four public proof modules:

- `BruhatCellVanishingProof`, for `bruhatCellVanishing`: when the actual
  `compatibleTorus ψ n w` is empty, every bi-equivariant algebraic
  distribution on `UpperBruhatCell (n + 1) F.Carrier w` is zero.
- `BruhatCellInvarianceProof`, for `bruhatCellInvariance`: when that torus
  is nonempty, the cell is stable under `τ` and every bi-equivariant
  distribution on it is invariant under the restricted transpose.
- `BruhatCellRestrictionVanishingProof`, for
  `bruhatCellRestrictionVanishing`: a globally bi-equivariant,
  anti-invariant distribution supported on the inversion layer of a cell
  has zero open restriction to that cell's neighborhood, provided the cell
  satisfies either of the preceding two alternatives. This theorem uses
  actual supported descent and the public covariance theorem.
- `Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof`,
  for `bruhatFiltrationVanishing`: a distribution is zero if support on the
  inversion layer of each permutation forces its actual restriction to
  that cell's open neighborhood to vanish. Its proof uses the published
  open-restriction locality theorem.

The first three module names above have prefix
`Langlands.Representation.Whittaker`; their theorem names have prefix
`Langlands.Whittaker`. The filtration theorem has prefix
`Langlands.HarmonicAnalysis.Distribution`. Each is used by its public Lean
name, with its full statement. No private preparation is imported.

## Algebraic reduction

Six small private helpers in `DistributionInvarianceProof` establish the
anti-invariant reduction over a commutative topological ring. They use the
actual test-function pullbacks and distribution pushforwards.

`pullback_transpose_biTranslate` identifies the test function
`g ↦ f(u₁ * τ(g) * u₂)` with the bi-translate of `f ∘ τ` by `τ(u₂)` and
`τ(u₁)`. Extensionality, multiplication reversal and involutivity prove the
identity. Consequently `biEquivariant_pushforward` applies the original
bi-equivariance to these two unipotents. The published
`standardCharacter_weylTranspose` preserves each character value;
commutativity of complex multiplication restores their order. Thus `τ_*D`
has the same two positive character factors as `D`.

`biEquivariant_sub` follows by linearity and `mul_sub`. Hence
`biEquivariant_difference` shows that

\[
E=D-\tau_*D
\]

is bi-equivariant. `antiInvariant_difference` uses linearity of pushforward
and its published involutivity to obtain `τ_*E = -E`. Finally,
`invariance_of_difference_zero` converts `D - τ_*D = 0` into the required
`τ_*D = D` by `sub_eq_zero` and symmetry.

## Canonical topology and the global proof

The main proof introduces precisely the parameters and premise of the
published target and installs `F.canonicalNormedField`.
`F.canonicalTopologicalData.generalLinearLocallyCompactSpace` supplies local
compactness of the actual group. The canonical spectral norm is
nonarchimedean, so `isUltrametricDist_of_isNonarchimedean_norm` supplies an
ultrametric distance on the field. The finite matrix space is consequently
totally disconnected. The continuous injective map `Units.val` from the
matrix general linear group to the matrix space transfers total
disconnectedness to the group. These are derived instances, not extra
premises of the theorem.

For the difference `E`, the helpers supply bi-equivariance and
anti-invariance. Apply the public `bruhatFiltrationVanishing` to this fixed
`E`. For each permutation `w`, its remaining premise assumes

```text
E ∈ supportedOn
  (upperBruhatLayerLE (n + 1) F.Carrier
    (permutationInversionCount (n + 1) w)).
```

Use this membership to regard `E` as the supported-distribution subtype
required by `bruhatCellRestrictionVanishing`, and pass the already proved
bi-equivariance and anti-invariance. Its cellwise alternative is discharged
by classical case distinction on `(compatibleTorus ψ n w).Nonempty`.

When the locus is nonempty, `bruhatCellInvariance` supplies exactly the
existential stability proof and invariance of every bi-equivariant cell
distribution required by the second branch. When it is empty,
`bruhatCellVanishing` supplies the universal vanishing assertion required
by the first branch. Thus the actual open restriction is zero in every
case. Stability of an arbitrary cell is never assumed; it is supplied only
in the compatible branch.

The finite-filtration theorem now gives `E = 0`. Internally that public
theorem removes inversion layers using open-restriction locality and
starts with the bound `(n + 1) * (n + 1)` on every inversion count and
actual Bruhat covering. The final module needs no comparison between an
inversion count and a geometric dimension. The last algebraic helper
concludes `IsWeylTransposeInvariant n F.Carrier D`.

Rank one (`n = 0`) is retained throughout and needs no separate argument.
The canonical topology instances and all four public theorems apply in
that rank as well. The proof uses the full algebraic dual throughout and
never commutes a distribution with an infinite integral.

## Provenance and scope

The local helpers and final assembly were written by Worker 634 in
`GlobalAntiInvariantCore` and `DistributionInvarianceAssemblyCore`, shared
parent draft revision 8 of task `f79ca82c-d050-4ffa-821b-c347b60e36e0`.
This production module ports those small parts and replaces every private
prerequisite application with its published theorem. The imported
prerequisite implementations are reused by import; their respective
companion Markdown files record their authorship and proofs.

The source is J. A. Shalika, *The multiplicity one theorem for GLn*,
Ann. of Math. (2) **100** (1974), 171–193, registered as
`shalika-1974-multiplicity-one`, SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Theorem 1.6 is on printed p.174. The standard all-ones adjacent-entry
character makes the auxiliary diagonal element the identity, giving
exactly the Weyl-conjugated transpose in the target. Proposition 1.8
(printed p.175) gives the positive-character test-function convention.

The implemented route follows the anti-invariant difference and support
removal in the proof of Theorem 1.6 on printed p.179. The original uses
cell dimensions, Lemma 1.16 and Proposition 1.17; this proof uses the
published inversion-layer topology, explicit one-cell supported descent
and finite-filtration theorem. The cellwise results come from the
published realization of the factorization and compatible-support
argument on printed pp.176–178. These are explicit internal deductions
and adaptations, rather than a claim that every helper is separately
stated in the source. Worker 634 read printed pp.173–179 and re-read
pp.178–179 when preparing this assembly; no source-specific errata note
was found.

This proves the distribution-invariance target. The representation bridge
and Whittaker multiplicity-one conclusion remain separate theorems.
Declaration inspection reports only `propext`, `Classical.choice` and
`Quot.sound` as axioms; no new axiom or proof hole is introduced.
