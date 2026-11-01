# Pullback of compatible two-axis rigidifications

For maps `e : S → X`, `t : S → Y`, `i : X → Z`, `j : Y → Z` with
`e ≫ i = t ≫ j`, a `TwoAxisRigidification` of an actual module sheaf `M`
consists of trivializations along `i` and `j` agreeing after restriction
to `S`. This module constructs their canonical pullback under a map of
such diagrams.

## Input diagram and resulting rigidifications

Take a second diagram with maps `e'`, `t'`, `i'`, `j'` over `S'`, `X'`,
`Y'`, `Z'`. A map to the original diagram consists of
`fz : Z' → Z`, `fx : X' → X`, `fy : Y' → Y`, `fs : S' → S`, with

```text
i' ≫ fz = fx ≫ i             j' ≫ fz = fy ≫ j
e' ≫ fx = fs ≫ e             t' ≫ fy = fs ≫ t.
```

`TwoAxisRigidification.pullback` sends a compatible rigidification `ρ` on
`M` to one on the actual module `(Scheme.Modules.pullback fz).obj M`.
Its first and second fields are exactly the canonical one-axis
`RigidifiedModule.pullback` rigidifications of `ρ.first` and `ρ.second`.
Thus both supplied trivializations are pulled back using the canonical
unit, composition and equality comparisons. Neither is replaced by a
newly chosen ordinary trivialization.

## Implemented comparison proof

`restrictionHom e i c h M α` is the restriction of an axis trivialization
to a named composite `c`, where `h : e ≫ i = c`. It first uses the inverse
structure-module unit comparison, then pullback of `α.hom`, then the
published `RigidifiedModule.compHom`.

The published `Langlands.Scheme.Modules.compHom_isIso` supplies invertibility.
`Langlands.Scheme.Modules.compHom_naturality`, used in the reverse direction,
and `RigidifiedModule.pullbackUnitIso_inv_compHom` supply the naturality and
unit laws. Their existing proofs are reused without duplicate declarations.
`pullback_rigidification_compHom` cancels the inverse comparison in the
definition of canonical one-axis pullback against the forward comparison.

`restrictionHom_pullback` proves that restricting a pulled-back
trivialization and then comparing to the composite `fs ≫ c` equals
pulling back the original restriction along `fs`. Its proof applies
`compHom_assoc` three times: first for `e'`, `i'`, `fz`, then for `e'`,
`fx`, `i`, then for `fs`, `e`, `i`. Naturality moves the trivialization
across the comparisons, and unit coherence identifies the two resulting
maps from `O_S'`.

`compatible_iff_restrictionHom` rewrites the original equality of
restriction isomorphisms as equality of their forward morphisms to the
same named composite `t ≫ j`. The constructor applies
`restrictionHom_pullback` on each axis, using the same composite
`t' ≫ j'` and the same comparison to `fs ≫ (t ≫ j)`. Cancellation of
this invertible comparison reduces the desired equality to pullback of
the original compatibility equation.

## Provenance and scope

This is internal categorical infrastructure derived from
`TwoAxisRigidification`, `RigidifiedModule.pullback`, and the proved
canonical pullback laws in `RigidifiedPullbackProofs`. The module makes
no additional literature assertion. The underlying product
rigidification convention and its source are documented in
`TwoAxisRigidification.md`.

All schemes have arbitrary universe `u`. No smoothness, properness,
connectedness, valuation, rank or fraction-field hypothesis is required.
The construction works on any module sheaf carrying the specified
trivializations. Isomorphism classes, their presheaf, correspondence
comparison, representability, gluing and extension are separate
constructions.
