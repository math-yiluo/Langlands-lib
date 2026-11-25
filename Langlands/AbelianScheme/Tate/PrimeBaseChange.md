# Base change of the actual prime Tate action and trace

This internal construction supplies the prime analogue of the published full rational Tate pullback comparison. For an arbitrary morphism of schemes `b : S' ⟶ S`, a prime `p`, a commutative group scheme `G` over `S`, and any test object `T : Over S'`, `integralBaseChange` identifies the actual integral prime Tate module of the pullback of `G` at `T` with that of `G` at `(Over.map b).obj T`.

The equivalence applies the existing `Tate.levelBaseChange` to every `p ^ n` torsion coordinate. The published transition compatibility makes both directions coherent, and the finite-level equivalences give inverse identities and additivity. The residue-defined `Z_p` action commutes with these additive maps by `ZMod.map_smul`. Extending scalars from `Z_p` to `Q_p` gives `rationalBaseChange`.

`integralBaseChange_map` and `rationalBaseChange_map` prove naturality for actual group-scheme homomorphisms, using finite-level pullback naturality and tensor induction. The abelian-scheme namespace exposes these comparisons for the actual bundled abelian schemes.

`Langlands.AbelianScheme.Tate.PrimeAdic.rationalBaseChange_homMap` extends naturality to the existing rationalized Hom action and the existing `AbelianScheme.rationalBaseChangeHom`. Its proof uses tensor induction in the rational homomorphism, rational scalar compatibility, and naturality for integral homomorphisms.

`trace_rationalHomMap_baseChange` proves equality of the intrinsic prime Tate traces on the two sides. Naturality identifies the operators by conjugation through the constructed equivalence, and Mathlib's trace-of-conjugation theorem proves the equality. The argument needs no finite-dimensionality assumption.

The trace on the original side is evaluated at the mapped test object, which is generally an extension-valued point rather than the identity test object. This module does not identify different geometric-point fibre functors, establish rational trace comparison, or prove field-extension invariance of `geometricEndomorphismTrace`. These remain separate obligations when using it in the Rosati positivity argument.

All schemes and bundled geometric objects retain the existing universe `u`. This is an internal derivation from the actual pullback adjunction, torsion-level comparison and prime Tate constructions already in the Library, with no source-dependent assertion.
