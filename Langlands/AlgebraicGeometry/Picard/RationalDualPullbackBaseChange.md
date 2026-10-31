# Canonical base change of the actual rational dual-pullback equation

This internal construction proves compatibility of actual rational
dual pullback with canonical base change. It reuses
`rationalDualPullbackHom0`, its rational-linear form
`rationalDualPullbackHom0Linear`, and
`IsRationalDualPullbackMultiple` from the existing
`WeilHom0Pullback` and `WeilHom0PullbackCoherence` modules.
No dual-pullback operation or multiplier predicate is redefined.

For a rational homomorphism `f : Hom0 A B`,
`rationalDualPullbackBaseChangeHom f` transports a rational dual-valued
map on `B` by `rationalDualBaseChangeHom`, then applies the existing
dual pullback by `rationalBaseChangeHom b f`. This is a constructed
rational-linear map from `Hom0 B DB` to `Hom0 (b*A) D(b*A)`.
The symbol `DB` denotes the actual constructed dual with the displayed
endpoint data, and every target comparison is the canonical
`dualAbelianBaseChangeIso`.

`rationalDualPullbackBaseChangeHom_commutes` proves that this equals
first applying actual dual pullback by `f` over the old base and then
transporting the result canonically. It assumes the exact named
`DualAbelianBaseChangeNaturalityStatement`, and pointwise dual-map
additivity at the original and changed endpoints. The proof rewrites
the two actual rational composition pullbacks using
`rationalBaseChangeHom_comp`, reassociates compositions, and applies
the derived rational duality square
`dualHom0_baseChange_of_naturality`. The theorem ending in `_square`
is equality of the corresponding rational-linear maps, proved by
extensionality and that value formula.

`IsRationalDualPullbackMultiple.baseChange_of_naturality` preserves
the actual geometric equation
`f^vee lamB f = q • lamA` with the same `q : ℚ`. It substitutes the
commuting-square theorem into the changed-base equation, applies the
given old equation, and uses rational linearity. The theorem ending
in `integral_baseChange_of_naturality` specializes to integral
`lamA` and `lamB`: the changed maps are precisely
`dualAbelianBaseChangeMap lamA` and
`dualAbelianBaseChangeMap lamB`, included into the actual rational
Hom groups. Its proof uses the previously proved integral recovery
formula for `rationalDualBaseChangeHom`.

These equations hold for every actual rational homomorphism `f` and
every rational number `q`; they require neither invertibility of `f`
nor nonzero `q`. In a polarized rational-isogeny application, an
actual rational isomorphism and a rational unit are supplied by that
application. The map used here is its actual rational pullback, so
the result supplies the geometric multiplier equation needed before
Tate frame or level transport. No pairing-preservation hypothesis
replaces that equation.

The bases are arbitrary schemes in one universe. The seven
dual-construction inputs, universal-family base-change, canonical
comparison group compatibility and existence, geometry,
inverse-bundle/evaluation data for all four dual endpoints remain
explicit. The construction uses the same endpoint choices in every
occurrence. This is internal algebraic compatibility of the imported
constructions, following Worker 144's canonical-dual square analysis
and implemented by Worker 57.

The integral naturality theorem remains a named hypothesis. This
module does not prove preservation of the whole polarization
predicate, preservation of faithful actions, a Tate frame or level
square, a varying-base polarized quotient, successive-base
coherence, representability or scheme levels.
