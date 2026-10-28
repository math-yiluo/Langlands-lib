# Simultaneous normalized p-adic row Fourier cutoffs

Worker 234 authored this derived statement and its documentation. The
interface was specified by Worker 623 for the paired complementary-block
transfer proof (task `60e55e09-11c3-4f2f-bd81-5011f07445f7`). Worker 110
proposed the normalized-pair design: one Fourier pair whose small member has
mass one, rather than two cutoffs normalized independently. The instance
setup and the valuative-topology helper are adapted from the
published `Langlands.RankinSelberg.UnequalRankComplementaryTransferStatement`.

`Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement.{u} F T d` is a
Prop-valued definition. This module states the proposition; it does not
prove it. The implicit parameters are a prime `p` and `[Fact p.Prime]`. The
explicit parameters are `F : PadicField.{u} p`, a supplied
`T : F.TopologicalData`, and `d : ℕ`. The field universe `u` is arbitrary.

## Installed structures

The definition installs exactly `T.topology`, `T.valuativeRel` and
`T.localField`. It then installs the right additive uniformity of that
topology, its uniform additive group certificate, and a nonarchimedean
additive group certificate. The helper `rowFourierCutoff_nonarchimedean`
derives the last from Mathlib's basis of open submodules for the valuative
topology. Integration exposes this existing helper for reuse by the proof
module, without changing its type, proof or the statement's meaning.
Finally it installs the
Borel measurable space of the supplied topology and its Borel certificate.

`IsSelfDual` requires the field to be Hausdorff, locally compact and totally
disconnected. Instance search derives these from the installed structures.
Total disconnectedness comes from Mathlib's total-separatedness instance
for Hausdorff nonarchimedean groups, imported from
`Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`. These classes
are propositions, so they add no data and no hypothesis.

The row space `Fin d → F.Carrier` has the product topology. The measure on
rows is the unchanged `rowMeasure ν d`, the finite product of the supplied
scalar measure in every coordinate. No topology, field realization or measure
is chosen anywhere in this module.

## The assertion

The proposition quantifies, in this order, over:

- every `ψ : UnitaryAdditiveCharacter F.Carrier` (continuous, nontrivial,
  with values in the unit circle);
- every supplied `ν : AdditiveHaarMeasure F.Carrier` with `IsSelfDual ψ ν`;
- every set `C` of rows with `IsCompact C`;
- every set `U` of rows with `IsOpen U` and `0 ∈ U`.

It then asserts that there exist actual Schwartz–Bruhat row functions
`Φ κ : SchwartzBruhat (Fin d → F.Carrier)` satisfying all six clauses:

1. `IsRowFourierPair ψ ν Φ κ`. Unfolded, for every row `y`,

   ```text
   κ y = ∫ x, ψ.complex (∑ i, x i * y i) * Φ x ∂rowMeasure ν d.
   ```

   This is the published plus-sign `rowPairing` and `rowFourierIntegral`,
   with no conjugation. So `κ` is the row Fourier transform of `Φ` for the
   supplied `ν`.
2. `Φ x = 1` for every `x ∈ C`. This is the large cutoff.
3. `Function.support ⇑κ ⊆ U`: the ordinary support `{x | κ x ≠ 0}` lies in
   `U`. This is the small cutoff.
4. `∫ x, κ x ∂rowMeasure ν d = 1`. This is the actual Bochner integral for the
   product of the supplied `ν`. Since the value is `1`, not `0`, the clause
   also rules out a vacuous non-integrable reading.
5. `Φ (-x) = Φ x` for every row `x`.
6. `κ (-x) = κ x` for every row `x`.

Both functions lie in the existing Schwartz–Bruhat subspace: they are locally
constant and compactly supported. The proposition does not assume Fourier
closure, row inversion or `IsRowSelfDual`. It does not assume the existence of
cutoffs, a compact open subgroup, or any bound on the character or its
conductor. Nothing is normalized by a chosen Haar measure.

## Why one pair

The large cutoff value and the small cutoff mass belong to one Fourier pair.
Clause 1 makes `κ` the transform of the same `Φ` that equals one on `C`. The
measure in clause 1 and in clause 4 is the same supplied `ν`. A consumer can
therefore use `Φ` as the large cutoff in one actual integral and `κ` as the
small cutoff in the other, with one consistent normalization. Two
independently normalized cutoffs would not provide this link.

Here is why the self-duality hypothesis matters (not used in Lean). Suppose
`ν₀` is self-dual for `ψ` and `ν = c • ν₀` with `c > 0`. Then row Fourier
inversion for `ν₀` gives `∫ κ ∂rowMeasure ν d = c^(2d) · Φ 0` for the
transform `κ` of `Φ` with respect to `ν`. When `0 ∈ C` and `d ≥ 1`, clauses
1, 2 and 4 hold together only if `c = 1`. Under self-duality, inversion gives
`∫ κ = Φ 0` whenever `κ` is the transform of `Φ`. Clause 4 states the mass
directly, so a consumer does not need inversion and the clause is not
redundant when `0 ∉ C`.

The evenness clauses remove the sign ambiguity between the plus-sign row
transform here and the reflected arguments of the sources described below.
They also serve the inverse-transpose sign changes in the paired transfer.

## Dimension zero

Dimension zero is included by the unrestricted `d`. Then the row space is a
singleton, `rowMeasure ν 0` is unit point mass (`rowMeasure_zero`), and the
empty pairing is zero. Hence `IsRowFourierPair ψ ν Φ κ` says `κ 0 = Φ 0`, and
the mass clause says `κ 0 = 1`. The constant functions `Φ = κ = 1` satisfy
every clause: `Φ` is one everywhere, and `U` contains `0`, so it is the whole
singleton. This short argument is documentation only; the
module proves nothing.

## Source correspondence

Provenance: **derived/internal**. Neither source states this proposition.
It is a sufficient internal formulation of the Fourier-cutoff step in the
following two arguments.

- Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms on GL(3) I*,
  Ann. of Math. 109 (1979), proof of Theorem (4.5), printed pp.197–198
  (registered `jps-1979-gl3-i`; one-based PDF pages 30–31; checked
  visually). In the induction step from `j` to `j+1`, the function `W′` is
  smeared by `Φ ∈ 𝒮(F)` in one coordinate. The Fourier transform appears with
  the sign `(-1)^(j+r-1)`, and the authors set
  `Φ′(u) = Φ̂((-1)^(j+r-1) u)`. They then take `Φ` to be the characteristic
  function of `𝔓^{-m}`, with `m` large enough that
  `Ψ(s, W; j, Φ) = Ψ(s, W; j+1)`. They note that `Φ′` is the characteristic
  function of `𝔓^m` times `vol 𝔓^{-m}`. For large `m`, `K_m`-invariance gives
  `Ψ(1-s, (π(w′)W)~; k-1, Φ′) = Ψ(1-s, (π(w′)W)~; k-1)`. That equality uses
  the total mass of `Φ′`, which the source does not display. Here `Φ` is the
  large cutoff (clause 2) and `Φ′` is the small normalized Fourier cutoff
  (clauses 1, 3, 4).
- Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions*,
  Amer. J. Math. 105 (1983), printed pp.394–395 (registered
  `jpss-1983-rankin-selberg`; one-based PDF pages 29–30; scan checked
  visually). The unnumbered Lemma in §2.7 takes `Φ ∈ 𝒮(F^t)` and
  `H¹(g) = ∫_{F^t} H(g u(z)) Φ̂(-ᵗz) dz`, where `u(z)` is the printed
unipotent matrix whose off-diagonal block is the column `z`. It asserts that integrating `H¹`
  against the row variable `x ∈ F^t` equals integrating `H` against `Φ(x)`.
  Its proof is said to be similar to Lemma (4.1.5) of [J-P-S]. §2.8 (p.395)
  states that, for general `t`, the argument of [J-P-S] Theorem (4.5) applies
  with that lemma in place of (4.1.5). This is the row (`F^t`) version of the
  cutoff step above. Our `d` plays the role of `t`.

The internal formulation differs from the sources as follows:

- it works with every supplied self-dual `ν` and every nontrivial `ψ`, rather
  than the source normalization with explicit ideals `𝔓^{±m}`;
- it allows an arbitrary compact `C` and open neighbourhood `U` of zero;
- it exports existence and mass one as clauses;
- it adds evenness and states the plus-sign transform `κ = F Φ`, absorbing
  the source signs `(-1)^(j+r-1)` and `-ᵗz`;
- it includes `d = 0`.

These are deliberate generalizations for the consumer. They are not claims
about the printed text.

The registered files are
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`
(SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`)
and
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`
(SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).

Errata check (bounded): I found no erratum for either article. I checked the
project literature index, the Central Library listing and the Library notes.
The only located Jacquet correction (2012) concerns the 1981 *Conducteur*
article, not these pages. This records the extent of the check; it does not
claim that no errata exist elsewhere.

## Intended proof (not part of this module)

A later proof task owns the construction. Here is the suggested route.
Choose a compact open additive subgroup `L` of rows inside `U` with
`ψ(rowPairing x z) = 1` for all `x ∈ C`, `z ∈ L`. Such an `L` exists because
`ψ` is trivial near zero, the pairing is continuous and `C` is compact. Set
`κ = 1_L / vol(L)` and `Φ = F κ`. Then `Φ = 1` on `C`, and row closure,
inversion and evenness give `IsRowFourierPair ψ ν Φ κ`. No
annihilator-volume product formula and no second Haar measure are needed.
Existing owners cover the ingredients: row closure and inversion from scalar
`IsSelfDual` (task `ba6361ff-1c19-432b-82b1-9d246273d780`), scalar Fourier
closure (task `66e7ba59-db37-4c91-afde-b1f13c86022c`) and compact-open
annihilator compactness (task `969ca422-a29a-4f92-ab24-beeeafb941d2`). This
module proves none of these steps.
