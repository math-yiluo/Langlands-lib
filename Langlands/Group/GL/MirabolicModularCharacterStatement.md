# The modular character of the actual mirabolic group

Author: Worker 799.

This file states a proposition. It does not prove it. The proposition
definition `Langlands.MirabolicModularCharacterStatement.{uF}` in the module
`Langlands.Group.GL.MirabolicModularCharacterStatement` asserts that Mathlib's
Haar-defined modular character `MeasureTheory.Measure.modularCharacter` of the
actual mirabolic subgroup of `GL_(n+1)(F)` is the positive residue-normalized
determinant norm `g ↦ |det g|_F`, for every rank `n`. In the conventions of
Bernstein--Zelevinsky this is their identity `Δ_P = ν⁻¹|_P` (BZ77 §4.2).

## Parameters, topology and instances

The outer parameters are exactly

```lean
{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
```

No other hypothesis occurs. There is no measurable structure, chosen Haar
measure, Haar-scaling premise, modular comparison, unimodularity premise or
other theorem-valued assumption, either as an outer parameter or inside the
body. Every prime `p`, every finite extension `F` of `ℚ_p` packaged as a
`PadicField`, every supplied realization `T` and every rank `n` is covered.
Only the field universe `uF` occurs.

The field `F.Carrier` has no global topology instance. The body installs
`T.topology`, the topology stored in the supplied realization, and its
Hausdorff property `T.fieldT2`. The matrix group `GeneralLinear (n+1) F.Carrier`
then carries the matrix unit topology induced by this field topology (the
Library's `T.generalLinearTopology (n+1)`), and the mirabolic subgroup carries
the subspace topology. For each `n` the body installs, from the same `T`:

- `T.generalLinearTopologicalGroup (n+1)` and
  `T.generalLinearLocallyCompactSpace (n+1)` for `GL_(n+1)(F)`;
- `GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)`,
  local compactness of the mirabolic group, which is closed in `GL_(n+1)(F)`
  (`GeneralLinear.Mirabolic.isClosed`).

The topological-group structure of the mirabolic subgroup is Mathlib's
instance for subgroups of a topological group
(`Mathlib/Topology/Algebra/Group/Subgroup.lean`). All of these are theorems or
instances about the supplied topology, proved in the Library or Mathlib; none
is an assumption. The canonical topology of `F` is not used.

## The group

Write `P_n = GeneralLinear.mirabolic n F.Carrier`. It is the actual Library
subgroup of `GL_(n+1)(F)` of invertible matrices whose last row is
`(0, …, 0, 1)`. **Rank shift:** this is the group `P_(n+1) ⊂ G_(n+1)` of BZ77
§3.1; the Lean index `n` is one less than BZ77's. The case `n = 0` is included:
`P_0` is the trivial subgroup of `GL_1(F)` (`GeneralLinear.Mirabolic.rankOneSubsingleton`),
where both sides of the equation are `1`. The Lean statement uses the Library
subgroup directly and introduces no substitute group.

## The modular character

For a locally compact topological group `G`, Mathlib's
`MeasureTheory.Measure.modularCharacter : G →* ℝ≥0`
(`Mathlib/MeasureTheory/Group/ModularCharacter.lean`) is defined by
`modularCharacterFun g = haarScalarFactor (map (· * g) haar) haar`, computed for
the Borel measurable structure that the definition installs internally. By
`modularCharacterFun_eq_haarScalarFactor` it is independent of the Haar
measure: for every left Haar measure `μ` on `G` with Borel measurable
structure, `haarScalarFactor (map (· * g) μ) μ = modularCharacter g`, so it is
the scalar `Δ(g)` in `map (· * g) μ = Δ(g) • μ` whenever this law holds, that
is `μ(A g⁻¹) = Δ(g) μ(A)`. It needs only `TopologicalSpace`, `Group`,
`IsTopologicalGroup` and `LocallyCompactSpace`, which is why the statement
needs no measurable structure or Haar measure. The statement applies this
actual definition to `G = P_n`; it is not replaced by a determinant character.

## Statement

For every `n : ℕ` and every `g : GeneralLinear.mirabolic n F.Carrier`,

```lean
MeasureTheory.Measure.modularCharacter g =
  ((T.determinantNorm (n + 1) g.val : ℝ≥0ˣ) : ℝ≥0)
```

as an equality in `ℝ≥0`. Here `g.val : GL_(n+1)(F)` is the underlying matrix
and `T.determinantNorm (n+1) : GL_(n+1)(F) →* ℝ≥0ˣ` is the published character
`g ↦ |det g|_F` of `Group/GL/NormalizedCharacter`, where `|·|_F` is the
residue-normalized absolute value supplied by `T` (`|x|_F = q^(-ord x)`, `q`
the residue cardinality). The right side is the underlying nonnegative real of
this unit. For `g` in `P_n` with upper-left block `h ∈ GL_n(F)`, `det g = det h`.

## Orientation and source correspondence

Registered source: `bernstein-zelevinsky-1977-induced-i`, I. N. Bernstein and
A. V. Zelevinsky, *Induced representations of reductive p-adic groups. I*,
Ann. Sci. ÉNS 10 (1977), SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Printed
page 444 is PDF page 5 counted from one, printed page 450 is PDF page 11 and
printed page 454 is PDF page 15. No erratum to these passages was found in the
Library notes.

- §1.7, printed page 444, defines the module of an automorphism `σ` of an
  l-group `U` by `∫_U f(σ⁻¹(u)) dμ(u) = mod_U σ · ∫_U f(u) dμ(u)`, writes
  `mod_U(g)` for the module of `u ↦ g u g⁻¹`, and sets `Δ_G = mod_G⁻¹`, "the
  module of the group `G`".
- §3.1, printed page 450, defines `P = P_n ⊂ G_n` as the matrices with last
  row `(0, 0, …, 0, 1)`, with `G_(n-1)` embedded in the standard way, unipotent
  radical `V`, and `P = G_(n-1) V`.
- §4.2, printed page 454, defines `ν(g) = |det g|` and states: "It is easy to
  prove that `Δ_P = ν⁻¹|_P`."

**Orientation.** For a left Haar measure `μ` on `G`, left invariance under
`u ↦ g u` gives `∫ f(g⁻¹ u g) dμ(u) = ∫ f(u g) dμ(u) = ∫ f d(map (· * g) μ)`.
The left side is `mod_G(g) ∫ f dμ` by BZ77's definition (with `σ = (u ↦ g u
g⁻¹)`, so `σ⁻¹(u) = g⁻¹ u g`); the right side is Mathlib's
`modularCharacter g · ∫ f dμ`. Hence Mathlib's `modularCharacter` is BZ77's
`mod_G`, the **inverse** of BZ77's `Δ_G`. BZ77's `Δ_P = ν⁻¹|_P` therefore reads
`mod_P = ν|_P`, and the formal target is the **positive** `|det g|_F`, not its
inverse. The Library's `T.determinantNorm` uses the standard normalized
absolute value, matching BZ77's "standard norm".

**Provenance.** The formal statement is an internally derived transcription of
BZ77's §4.2 sentence into Mathlib's convention; BZ77 gives no proof. The
following informal check is not part of the formal content. Write `p = v m`
with `v ∈ V ≅ F^n` and `m = diag(h, 1)`, `h ∈ GL_n(F)`, and let
`mod_V(m) = |det h|_F` be the module of `v ↦ m v m⁻¹` (this is the content of
the published radical theorem described below). Then
`∫_M ∫_V f(v m) mod_V(m)⁻¹ dv dm` is a left Haar integral on `P`, and right
translation by `m₁` multiplies it by `mod_V(m₁)`, while `V`, a union of compact
open subgroups, has trivial modular character, and `GL_n(F)` is unimodular. So
`modularCharacter(v m) = |det h|_F = |det(v m)|_F`.

## Distinction from related Library results

- **Radical conjugation theorem.** `Langlands.MirabolicRadicalHaarModulusStatement`
  (`Group/GL/MirabolicModulusStatement`), proved by
  `Langlands.mirabolicRadicalHaarModulus` (`Group/GL/MirabolicModulusProof`),
  computes the Haar character `HaarModulus.closedRestrictCharacter` of
  **conjugation on the last-column radical** `V` by the Levi and successor
  subgroups: BZ77's `mod_V`. It says nothing about Haar measures on the full
  group `P` or about right translation in `P`; its own Markdown places the
  full-group identity `Δ_P = ν⁻¹` outside it. The present statement is that
  full-group identity, for Mathlib's `modularCharacter` of `P_n` itself. The
  radical theorem is a natural proof ingredient, not this statement.
- **Minus-functor normalization adapter.**
  `Langlands.Representation.Derivative.MirabolicMinusNormalization`
  identifies the canonical inverse half `mod_V^(-1/2)` of the radical Haar
  characters with the determinant real-power characters of exponent `-1/2`
  used by the minus functors `Ψ⁻` and `Φ⁻`, and identifies the resulting
  functors. It concerns radical characters, their inverse square roots and
  the minus functors, not the modular character of `P`; this statement
  neither uses nor restates it.

## Imports and independence

The module imports only `Langlands.Group.GL.Mirabolic`,
`Langlands.Group.GL.NormalizedCharacter` and
`Mathlib.MeasureTheory.Group.ModularCharacter`. It imports neither the radical
Haar statement or proof, nor the block-parabolic modular character module
`Langlands.Group.GL.ParabolicModularCharacter`, nor any representation,
derivative, Jacquet, classification or irreducibility development, nor any
module of the tasks excluded by this statement task's independence section.

## Not claimed

This file only states the comparison. It proves no Haar scaling, computes no
Haar measure and supplies no proof of the equation. It does not state the
right Haar measure, the half or inverse-half powers, normalized induction on
`P`, or any consequence for derivatives, minus or plus functors, exactness,
pairings or classification.
