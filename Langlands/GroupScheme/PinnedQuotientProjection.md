# A group projection from unique pinned representatives

This internal group construction isolates the algebraic step in the affine
pinned automorphism theorem. It applies to any groups `Γ` and `Δ`, a normal
subgroup `N` of `Γ`, a subgroup `B` of `Δ`, and a relation `Pinned g θ`.
It assumes the geometric existence and separation properties; it does not
establish them for group schemes.

`SplittingData` packages the following hypotheses. The identity pair is pinned,
and products of pinned pairs are pinned. Every pinned label belongs to `B`.
Each element of `B` has exactly one pinned representative in `Γ`. Every element
of `Γ` factors as an element of `N` times such a representative. Finally, a
pinned representative belonging to `N` has identity label.

The unique representatives form `sectionHom : B →* Γ`: its identity and product
laws follow from uniqueness. Composing with the quotient map gives
`quotientSection : B →* Γ ⧸ N`. Separation proves its injectivity by checking
the kernel, and factorization proves its surjectivity. Its inverse group
isomorphism, followed by the inclusion of `B` into `Δ`, defines
`projection : Γ →* Δ`.

The projection has kernel exactly `N` and image exactly `B`, is the identity on
the labels of the chosen section, and sends any pinned representative to its
label. These are consequences of the quotient isomorphism and uniqueness.

The provenance is an elementary algebraic reduction, intended for
`Γ = Aut G`, `N = inn.range`, and `B` the based root-datum automorphisms in the
Library's affine pinned automorphism group statement. No result about reductive
groups, existence of their pinned automorphisms, or their geometric
factorization is asserted by this module.
