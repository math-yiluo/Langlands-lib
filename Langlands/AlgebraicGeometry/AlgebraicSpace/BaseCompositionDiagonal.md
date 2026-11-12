# Structural diagonals after composition of bases

Author: Worker 109.

This internal module derives structural quasi-separatedness and separatedness
for actual base-composed spaces. The proof uses the published scheme-diagonal
comparison and the base-composition pullback and relative-diagonal
constructions. No external literature theorem is claimed as proved.
Schemes and their test sites retain arbitrary universe `u`.

The base map's diagonal contributes an additional condition in this module.
`relative_diag_presheaf` assumes a scheme-morphism property `P` respecting
isomorphisms and stable under composition and base change, the represented
`P` property for the diagonal of the original presheaf `F`, and
`P (pullback.diagonal g)` for the scheme base map `g : S ⟶ T`. It concludes
the represented `P` property of the diagonal of `presheaf g F`.

`schemeTerminalIso` identifies the relative presheaf represented by `S`
over itself with a terminal presheaf: the identity over `S` is terminal and
the lifted Yoneda functor preserves terminal objects. Mapping this
isomorphism by the composed-presheaf functor, then applying `schemeIso`,
gives `composedTerminalIso`. Thus the composed terminal relative presheaf is
represented by the original base scheme `S`, now over `T`.

`diag_iff_diagonal_terminal` compares an absolute presheaf diagonal with
the relative diagonal of its unique map to a terminal object. The canonical
product/pullback comparison is an isomorphism, so every isomorphism-respecting
morphism property gives the same condition on the two diagonals.

The main proof applies `relative_pullback_diagonal` to the original
terminal map. This supplies the required relative-diagonal property for its
base-composed map to the composed terminal presheaf. The represented scheme
diagonal theorem `relative_diag_schemeYoneda` and the given condition on
`g` supply the structural diagonal property for that composed terminal
presheaf. The relative property is stable under base change and composition,
so its diagonal property is stable under composition as well. Composing the
two maps gives the unique terminal map from the composed original presheaf.
The product/pullback comparison then yields its absolute diagonal property.

`quasiSeparated_space` specializes to quasi-compact scheme morphisms:
a quasi-separated original space remains quasi-separated provided `g`
is quasi-separated. `separated_space` specializes to closed immersions:
a separated original space remains separated provided `g` is separated.
These hypotheses on `g` remain explicit. In particular no structural
separatedness assertion is made for an unrestricted base morphism.

The results supply structural geometric prerequisites. They do not prove a
uniform finite-field estimate, spreading of a generic morphism, or the
unconditional adelic open-map target.
