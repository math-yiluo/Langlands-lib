# Isomorphisms and section formulas for group-scheme translations

This module shares the existing translation helpers from
`AlgebraicallyClosedCommonAffineProof` in the namespace
`Langlands.GroupScheme.CommonAffine`. Their definitions and proof terms are
unchanged; the declarations are public so that `AffineSectionAmple` reuses them.

For every scheme `S : Scheme.{u}`, group object `G : Grp (Over S)` and section `s`,
`translationIso G s` packages translation by `s` as an isomorphism, with inverse
translation by `s⁻¹`. The inverse laws use the group cancellation laws.
`section_comp_translation G s z` identifies `z ≫ translation G s` with `s * z`.
If `G.X` is commutative, `translation_apply_section G s z c` identifies the value
of translation by `s` on `z(c)` with translation by `z` on `s(c)`.

These are internal identities for the existing `GroupScheme.translation`
construction. They require no smoothness, properness or field hypothesis.
