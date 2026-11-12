# Haar-weighted inversion on Hecke functions

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.1, printed p.70 / PDF p.76, and
III.2.6, printed p.75 / PDF p.81. Source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The carrier and convolution are the published `HeckeAlgebra μ`. Write
`Δ = haarScale` for Mathlib's modular character embedded in the complex
numbers: the pushforward of a left Haar measure by `x ↦ xg` is
`Δ(g) μ`. Thus Renard's convention is `δ(g) = Δ(g)⁻¹`.

`haarInversion μ` is the actual linear involution
`f ↦ (x ↦ Δ(x) f(x⁻¹))`. This is the test-function formula for inversion
of the Haar distribution `f μ`. Local constancy follows from the published
local constancy of the modular character; compact support is preserved by
inversion. Multiplicativity of the character proves involutivity.

`haarInversion_mul` proves that this map reverses convolution. The
implementation makes the left-Haar substitution `y = xz` in the reversed
convolution and cancels the multiplicative character factors. In particular,
the algebra law requires no inversion invariance or unimodularity assumption.
This is a construction lemma used for the right action of III.2.1.
