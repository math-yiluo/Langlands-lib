# Existence of a nontrivial unitary additive character

Module: `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement`.
Worker 219 drafted the definition and an earlier version of this note; Worker 1000
revised the note and submitted the pair.

## Statement

`Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement.{u}` has
implicit parameters `{p : ℕ}` and `[Fact p.Prime]`, followed by explicit parameters
`(F : Langlands.PadicField.{u} p)` and `(T : F.TopologicalData)`. It returns `Prop`,
with the single universe parameter `u`. Its body is

```lean
letI := T.topology
Nonempty (UnitaryAdditiveCharacter F.Carrier)
```

so it is definitionally `Nonempty (@UnitaryAdditiveCharacter F.Carrier _ T.topology)`,
where the additive group is the one of the field `F.Carrier`. In words: for the
topology supplied by `T`, there is an additive character `ψ : F → Circle` of the
additive group of `F` that is continuous and is not the trivial character.

The parameters follow the published `PadicSelfDualMeasureExistsStatement`. The
prime `p`, the finite extension `F` of `ℚ_p` (Mathlib's `Padic p`), the realization
`T` and the universe `u` are all arbitrary. The topology is the supplied
`T.topology`, not `F.canonicalTopology`. The other fields of `T` (valuation,
module-topology and local-field certificates) are not used in the body; they only
make `T.topology` the topology of a nonarchimedean local field.

`UnitaryAdditiveCharacter` is the existing structure of
[Basic](Basic.md), used unchanged: an `AddChar F Circle` together with
`continuous_toFun : Continuous toAddChar` and `nontrivial : toAddChar ≠ 1`. Here
`Circle` is Mathlib's unit circle in `ℂ`. The proposition says nothing about the
conductor of the character, self-duality of a measure, a normalization, compatibility
with the trace, or uniqueness. It only asserts existence and does not choose a
character.

## Source

J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in
J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press,
1967, Chapter XV, §2.2, printed pp.308–309, with the conventions of §1.3, printed
p.307. Registered source `tate-1967-thesis`,
file `/home/taskhub/central-library/Cassels-Frohlich--Algebraic Number Theory--1967/Cassels-Frohlich--Algebraic Number Theory--1967.pdf`,
SHA256 `01259375a6275b726e836ce209cee40ed6f98a5cefe1aa5ad40f2ad07a63169e`. The scan
has two printed pages per PDF page and no text layer. Printed p.308 (left half) and
p.309 (right half) are on PDF page 163 (zero-based index 162); printed p.307 is the
right half of PDF page 162 (zero-based index 161).

- Printed p.307, §1.3. Tate assumes the basic facts of abstract Fourier analysis on
  a locally compact abelian group `G` and its character group `Ĝ`. He does not
  restate the definition there; in that standard theory `Ĝ` consists of the
  continuous homomorphisms of `G` into the complex numbers of absolute value 1.
- Printed p.308, §2.1 and the start of §2.2. There `k` is the completion of an
  algebraic number field at a prime `𝔭`, it is locally compact, and `k⁺` is its
  additive group, "as a locally compact commutative group". Lemma 2.2.1 concerns the
  character group of `k⁺`. Step (1) of its proof uses the continuity of `ξ ↦ ηξ` to
  show that `ξ ↦ χ(ηξ)` is again a character.
- Printed p.309, Case 2 (`𝔭` discrete, `R = ℚ_p`). `λ(x)` is determined modulo 1 by
  (a) `λ(x)` is a rational number with only a `p`-power in the denominator, and
  (b) `λ(x) − x` is a `p`-adic integer. Lemma 2.2.2 states that `x ↦ λ(x)` is a
  nontrivial continuous additive map of `R` into the reals mod 1. Its proof notes
  `λ(x) = 0 ⇔ x` is a `p`-adic integer.
- Printed p.309, the paragraph before Theorem 2.2.1. With `Λ(ξ) = λ(S_{k/R} ξ)`,
  where `S_{k/R}` is the trace, "an additive continuous map of `k` onto `R`", the map
  `ξ ↦ e^{2πiΛ(ξ)}` is a nontrivial character of `k⁺`.

That character is a continuous nontrivial homomorphism from the additive group of
`k` to the unit circle, which is exactly an element of `UnitaryAdditiveCharacter`.
So the proposition is the existence part of this passage.

Tate's `k` is a completion of a number field. Case 2 of his argument uses only that
`k` is a finite extension of `ℚ_p` with its locally compact topology and that the
trace to `ℚ_p` is continuous and onto. These hold for every finite extension of
`ℚ_p`, since the characteristic is zero. The statement is therefore made for every
`F : PadicField.{u} p`. Theorem 2.2.1, which identifies `k⁺` with its character
group, and Lemma 2.2.3, on the conductor of the standard character, are not part of
this statement. Since only existence is asserted, Tate's sign convention
(`λ(x) = −x mod 1` in the archimedean case, and the choice of `+` in `e^{2πiΛ}`)
plays no role.

## Provenance and use

This is an internal prerequisite, stated in Lean packaging rather than verbatim
source notation. The Bernstein–Zelevinsky derivatives of representations of
`GL_n(F)` are defined with a fixed nontrivial additive character, and the Library's
derivative statements quantify over every `ψ : UnitaryAdditiveCharacter F.Carrier`.
Results such as Zelevinsky 1980, Proposition 4.6, have no character in their
statements, so their proofs must choose one. This proposition provides the choice.

The module imports only `Langlands.LocalField.Definitions` and
`Langlands.HarmonicAnalysis.Basic`, which import only Mathlib. It uses no
representation-theoretic result.

## Status

This module states the proposition only. It is unproved by this contribution; its
proof is a separate obligation.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
