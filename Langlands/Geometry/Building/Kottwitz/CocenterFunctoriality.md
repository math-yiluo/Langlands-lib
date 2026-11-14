# Morphisms between supplied actual cocenters

This helper constructs actual morphisms between the cocenters used in the
simply-connected-derived Kottwitz construction. It is
an internal consequence of the Library's definitions and fpqc homomorphism
descent, motivated by the functoriality argument in Kaletha–Prasad (2023),
Lemma 11.5.1, printed p. 430 / PDF p. 461, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`.

For a morphism `f : H → G` and supplied actual cocenters of both groups,
`Cocenter.kernel_comp` identifies the full kernel of the source quotient
with its actual derived subgroup. The published derived-annihilation
theorem shows that the composite to the target torus kills this kernel.
The target is separated because it is affine.

When `H` is connected reductive, its quotient to the source cocenter is
flat and scheme-surjective by the cocenter definition. Both its source
and target are affine, so it is quasi-compact. The published
`FpqcHomDescent` construction therefore produces a unique morphism of
commutative group schemes between the supplied cocenters.
`Cocenter.map` selects it, `Cocenter.quotient_map` proves its commuting
square, and `Cocenter.map_unique` states uniqueness. These are actual
scheme morphisms; no surjectivity of rational points is assumed.
