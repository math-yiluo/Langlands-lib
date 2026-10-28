# Simultaneous normalized p-adic row Fourier cutoffs: proof

The module `Langlands.HarmonicAnalysis.PadicRowFourierCutoffProof` proves
`Langlands.HarmonicAnalysis.padicRowFourierCutoff`. For every prime `p` with
`[Fact p.Prime]`, every `F : PadicField.{u} p` in an arbitrary universe `u`,
every supplied `T : F.TopologicalData` and every `d : ℕ`, the theorem's type
is exactly
[`PadicRowFourierCutoffStatement F T d`](PadicRowFourierCutoffStatement.md).
The statement's meaning and every pair it imports are unchanged. Integration
exposes its existing nonarchimedean helper for reuse here and removes the
duplicate private helper from this proof module.

Besides the statement, the module imports the published row Fourier
compatibility proof ([`RowFourierCompatibilityProof`](RowFourierCompatibilityProof.md)),
the published sigma-finiteness proof
([`SelfDualSigmaFiniteProof`](SelfDualSigmaFiniteProof.md)), the published
Hecke test functions ([`Hecke.TestFunction`](../Representation/Hecke/TestFunction.md))
and Mathlib's circle arcs. It adds no hypothesis. In particular it does not
assume Fourier closure, row inversion, the existence of cutoffs, a compact open
lattice, a conductor bound, a nonempty `C` or positive dimension. It uses the
supplied `ν` and chooses no other Haar measure.

The proof is split into two generic theorems over an arbitrary field `F`
and a short final step that installs the statement's structures.

## A compact open product subgroup adapted to `C` and `U`

`exists_rowCutoffSubgroup` assumes that `F` is a field with a topological
ring structure, a nonarchimedean additive group and a locally compact
topology. Let `ψ` be a unitary additive character and `d : ℕ`. Let `C` be a
compact set of rows and `U` a neighbourhood of zero in the rows
`Fin d → F`. The theorem gives an open additive subgroup `S` of `F` with the
following three properties:

- `S` is compact;
- every row `z` with all entries in `S` lies in `U`;
- `ψ.complex (rowPairing z x) = 1` for every such `z` and every `x ∈ C`.

The proof uses the open set `A`, the inverse image under `ψ` of Mathlib's open
right half arc `Circle.centeredArc (π / 2)`. It contains `ψ 0 = 1`. The row
pairing `(z, x) ↦ ∑ i, z i * x i` is continuous, and `rowPairing 0 x = 0`.
So each `x ∈ C` has a neighbourhood of zero of rows `z` with
`rowPairing z x ∈ A`. Compactness of `C`
(`IsCompact.eventually_forall_of_forall_eventually`) makes this uniform in
`x ∈ C`. Intersecting with `U` gives a neighbourhood of zero in the product
topology. By `nhds_pi` and `Filter.mem_pi` it contains a set of rows whose
`i`-th entries lie in a neighbourhood `t i` of zero in `F`, for each `i`.
Local compactness gives a compact neighbourhood `K` of zero. The
nonarchimedean property then gives an open additive subgroup `S` inside
`K ∩ ⋂ i, t i`. Open subgroups are closed, so `S` is compact as a closed
subset of `K`. Every row with entries in `S` lies in `U`, and its pairing with
every `x ∈ C` lies in `A`.

It remains to show that `ψ` is trivial on these pairings, not only close to
one. Let `z` have entries in `S` and let `x ∈ C`. For every `n ≥ 1`, the row
`n • z` also has entries in `S`, and `rowPairing (n • z) x = n • rowPairing z x`.
The character law (`AddChar.map_nsmul_eq_pow`) shows that every positive power
of `ψ (rowPairing z x)` lies in the half arc.
`Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` then gives
`ψ (rowPairing z x) = 1`. This is the same half-arc argument as
`annihilator_mem_nhds_zero` in
[`CompactOpenAnnihilatorProof`](CompactOpenAnnihilatorProof.md). That lemma
concerns the scalar product with a compact subgroup, not rows paired with a
compact set, so the argument is written out again here.

## The cutoff pair

`exists_rowFourierCutoff` adds the hypotheses that `F` is Hausdorff, Borel
and totally disconnected. With local compactness, these are the classes
required by `IsSelfDual`. For a unitary additive character `ψ`, an additive Haar measure
`ν` with `IsSelfDual ψ ν`, a compact row set `C` and an open row set `U`
containing zero, it proves the six clauses of the statement for one pair
`Φ κ : SchwartzBruhat (Fin d → F)`.

The published `selfDualSigmaFinite` makes `ν.measure` sigma-finite. The
published `rowFourierCompatibility` turns `IsSelfDual ψ ν` into row Fourier
closure (`RowFourierClosed`) and row inversion (`IsRowSelfDual`), both for
the supplied `ν`.

Take `S` from the previous section and let `L` be the product set
`Set.univ.pi (fun _ => S)`, the rows with all entries in `S`. It is open (a
finite product of open sets), closed, compact and measurable. `L` is closed
under negation because `S` is a subgroup. By the published `rowMeasure_entries`,
`rowMeasure ν d L = ν.measure S ^ d`. The factor `ν.measure S` is nonzero,
because `S` is open and nonempty, and finite, because `S` is compact. Hence
the real volume `m` of `L` is positive.

Let `κ = m⁻¹ • 1_L`, where `1_L` is the published actual characteristic
function `Hecke.TestFunction.characteristic` of the clopen compact set `L`.
As a function, `κ` is the indicator of `L` with constant value `m⁻¹`. So:

- `κ` is even, since `L` is closed under negation;
- the support of `κ` lies in `L`, hence in `U`;
- `∫ κ ∂rowMeasure ν d = m⁻¹ · m = 1` by `integral_indicator_const`.

Row Fourier closure gives `Φ : SchwartzBruhat (Fin d → F)` with
`Φ x = rowFourierIntegral ψ ν d κ x` for every row `x`, the plus-sign row
transform of `κ`.

- **Fourier pair.** For every row `y`, row inversion applied to `κ` gives
  `rowFourierIntegral ψ ν d Φ y = κ (-y)`. Evenness of `κ` turns this into
  `κ y`, which is `IsRowFourierPair ψ ν Φ κ`.
- **Plateau on `C`.** Let `x ∈ C`. On `L`, the factor
  `ψ.complex (rowPairing z x)` equals one by the choice of `S`. Off `L`, `κ`
  vanishes. Hence the integrand of `rowFourierIntegral ψ ν d κ x` equals `κ`,
  and `Φ x = ∫ κ = 1`.
- **Evenness of `Φ`.** Row inversion applied to `Φ` gives
  `Φ (-x) = rowFourierIntegral ψ ν d (rowFourierIntegral ψ ν d Φ) x`. The
  inner transform is `κ` by the Fourier pair clause, and the transform of `κ`
  is `Φ`. So `Φ (-x) = Φ x`.

Dimension zero needs no separate case. Then `L` is the whole one-point row
space, `m = ν.measure S ^ 0 = 1`, and the same argument applies.

## The p-adic statement

`padicRowFourierCutoff` installs the structures of the statement in the same
order. These are `T.topology`, `T.valuativeRel`, `T.localField`, the right
additive uniformity with its uniform additive group certificate, a
nonarchimedean certificate and the Borel measurable space with its Borel
certificate. The topology, valuative relation, local-field certificate,
uniformity and measurable space are bound with `let`. The uniform additive
group, nonarchimedean and Borel certificates are propositions bound with
`have`; by proof irrelevance they agree with the statement's certificates.
After introducing the quantified data, the theorem applies
`exists_rowFourierCutoff`. Instance search supplies the remaining
Hausdorff, local compactness and total disconnectedness classes from the
installed structures, as described in the statement Markdown.

The nonarchimedean certificate comes from the existing theorem
`rowFourierCutoff_nonarchimedean` in the statement module. It obtains, from Mathlib's basis of
open submodules over the valuation integers
(`IsLinearTopology.hasBasis_open_submodule`), an open additive subgroup inside
each neighbourhood of zero. The helper is exported during integration so
that both modules reuse the same declaration.

## Provenance and credits

This proof is an internal derivation from published Library interfaces and
Mathlib. It asserts no original-source theorem; the source correspondence of
the proposition (Jacquet–Piatetski-Shapiro–Shalika 1979, Theorem (4.5), and
1983, §§2.7–2.8) is documented in the statement Markdown. The route is the
one suggested in the statement Markdown. One choice differs from that
suggestion: the subgroup of rows is a product `Sᵈ` of a scalar subgroup, so
measurability and the exact volume come from the finite product measure
without countability assumptions. The proof does not need the compact-open
annihilator theorem or the scalar Fourier closure theorem directly; the
latter enters only through the published row Fourier compatibility proof.

Worker 723 wrote this proof. The nonarchimedean helper is reused from
the statement module by Worker 234. That helper was in turn adapted, through
Worker 467's and Worker 331's published statements, from Worker 11's published
`FunctionalEquationStatement`. The proof reuses, without changes, the published
row Fourier compatibility proof by Worker 110, the published `rowMeasure`
interface of [`RowFourier`](RowFourier.md), the sigma-finiteness theorem and
the Hecke characteristic test function.
