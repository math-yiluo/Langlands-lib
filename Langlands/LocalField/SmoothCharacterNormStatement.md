# Real norm decomposition of a smooth scalar character

Worker 559.

`Langlands.PadicField.TopologicalData.SmoothCharacterNormDecomposition F T`
is a proposition for any prime `p`, any finite p-adic extension
`F : PadicField.{uF} p`, and any supplied `T : F.TopologicalData`. The field
universe `uF` is arbitrary. The definition installs `T.topology` locally, so
the topology on `F.Carrierˣ` is the usual topology of units induced from
that supplied field topology.

For every multiplicative character `ω : F.Carrierˣ →* ℂˣ` whose kernel is
open in `F.Carrierˣ`, the proposition asserts the existence of a unique
`c : ℝ` satisfying, for every `a : F.Carrierˣ`,

```text
‖(ω a : ℂ)‖ = T.normalizedAbs (a : F.Carrier) ^ c.
```

The norm on the left is the usual complex norm after coercing the
nonzero complex value to `ℂ`. The base on the right is the existing
residue-normalized absolute value of the supplied local field, and the
power is real exponentiation, `Real.rpow`. The existing normalization is
zero at zero and `q ^ (-T.ord x)` at a nonzero field element, where
`q = T.residueCardinality`; in that defining formula the exponent is an
integer. The displayed character statement only evaluates this absolute
value at units of the field, hence at nonzero elements.

The open-kernel hypothesis is the smoothness condition used here. It is
explicit in the proposition; the statement does not quantify over
unrestricted discontinuous characters. It includes all primes, all finite
p-adic extensions in the indicated universe, and all supplied compatible
topological data. There are no representation-theoretic hypotheses or
supplied real-exponent data.

## Internal provenance and source boundary

This is an internal scalar local-field lemma, extracted as a prerequisite
for normalizing the absolute value of a smooth central character by a real
norm twist. It is not a transcription of a theorem from Auel.

Asher N. Auel, *Une démonstration d'un théorème de Bernstein sur les
représentations de quasi-carré-intégrable de GL_n(F) où F est un corps local
non archimédien*, DEA memoir, Université Paris-Sud XI Orsay, July 2004:
Definition 4.7, printed/PDF page 9, defines `Irrᵘ` by a unitary central
character. Lemma 4.15, printed/PDF page 10, asserts a real-valued character
twist into that class. These passages motivate this scalar prerequisite
but do not state or prove its exact existence-and-uniqueness assertion.
Both pages were read, and page 10 was checked visually.

- Registered literature ID:
  `provided-dd2424348af1ddf73426a58cb44a42985d610bade9fb26dd0da2739fbc2494d1`.
- Retained source:
  `literature/Auel (2004), proof of Bernstein's quasi-square-integrable GL_n classification.pdf`.
- Source SHA-256:
  `3a6bcabbd0fa06a16e530cd3e7381c42742e3f1e4545316e2bf047e62afb1e65`.
- The source-boundary note
  [GL_n classification sources](../../notes/henniart/gln-classification-sources.md)
  records the memoir's corrections and distinguishes unitary central
  character from unitarizability.

## Dependencies and proof obligation

The only project import is
`Langlands.LocalField.Normalization.Definitions`. It supplies the algebraic
finite extension, the compatible supplied local-field data, and the
valuation-based absolute-value definition. Mathlib supplies complex norms,
real powers, and the topology of units. No representation, classification,
or square-integrability module is imported.

This module defines a `Prop`; it contains no proof of that proposition and
introduces no axiom. A separate proof must establish existence as well as
uniqueness. The intended elementary route uses compactness of the local
integer units and the valuation/uniformizer decomposition. Those steps are
proof obligations, not inputs supplied by this statement or by its motivating
citation. This statement constructs no invariant positive form and proves
no downstream analytic assertion.
