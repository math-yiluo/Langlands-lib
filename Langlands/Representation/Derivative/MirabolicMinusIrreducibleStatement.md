# Irreducibility of unnormalized `Φ⁻`

Author: Worker 806.

This module states one Prop-valued definition,
`Langlands.Derivative.Mirabolic.PhiMinusIrreducibleStatement F T m`. It proves
nothing.

## Statement

Let `F` be a p-adic field with topological data `T`, let `m : ℕ`, and let `ψ`
be a unitary additive character of `F`. The Library's `UnitaryAdditiveCharacter`
includes nontriviality. Let `ξ` be an irreducible smooth complex
representation of `mirabolic (m + 1) F` (the group `P_(m+2)` inside
`GL_(m+2)(F)`) on a carrier `V` in universe `uV`. Let `Φ⁻ ξ` be
`(phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)`, a smooth
representation of `mirabolic m F`. Its carrier is the quotient of `V` by the
span of the vectors `ξ u v - θ_ψ(u) v` for `u` in the radical `V_(m+2)`, and
`h` acts through `successor h`.

The statement says that every subrepresentation of `Φ⁻ ξ` is `⊥` or `⊤`.
Together with `⊥ ≠ ⊤` this is irreducibility. So the statement says that
`Φ⁻ ξ` is irreducible or zero.

## Source and provenance

Provenance: derived. The statement is a consequence of Bernstein–Zelevinsky
(1976), *Representations of the group GL(n,F) where F is a non-Archimedean
local field*, `bernstein-zelevinsky-1976-representations-gln`:

- Definition 5.11 a), printed p.46: `Φ⁻(π)` is the representation of `P'` on
  `E_(M,θ) = E/E(M,θ)`. This is the unnormalized functor; the Library's
  `phiMinusUnnormalized` is the same construction.
- Proposition 5.12 d) and f), printed pp.46–47: there is an exact sequence
  `0 → Φ⁺Φ⁻(π) → π → Ψ⁺Ψ⁻(π) → 0`, and `Φ⁻Φ⁺(τ) ≅ τ`. Moreover `Φ⁺` and `Φ⁻`
  give a bijection between the subrepresentations of `τ` and those of
  `Φ⁺(τ)`.
- Proof of Corollary 5.13 b), printed p.48: an irreducible `π` is either
  `Φ⁺(τ)` with `τ` irreducible or `Ψ⁺(ρ)`. In the first case
  `Φ⁻(π) ≅ τ` is irreducible. In the second case `Φ⁻(π) = Φ⁻Ψ⁺(ρ) = 0` by
  5.12 c).

The source does not state this consequence as a separate result. It is
recorded here as an intermediate statement for the induction in
`MirabolicTwistedPairingRigidityStatement` (JPSS 1983, §1.5, Corollary 2).
