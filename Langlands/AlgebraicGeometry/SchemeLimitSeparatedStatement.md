# Separatedness descent along actual affine-scheme limits

This proposition is a derived relative form of the separatedness clause
of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`RelativeSeparatednessDescent` uses an actual small cofiltered diagram
of affine schemes over an affine base, an actual limit cone and its
`IsLimit` witness, and a compatible structure map from that limit.
For a morphism `f : X ⟶ Y` over the base, assume that `f` is
quasi-compact and quasi-separated and that the source structure map
`a : X ⟶ S` is quasi-compact. The actual `baseChangeMap` at the limit
is separated if and only if its actual counterpart at some stage is
separated. All categories and schemes share arbitrary universe `u`.
Neither model is required to be affine or separated; transition maps
need not be injective on coordinate rings.

These are derived weaker relative hypotheses than the source's finitely
presented models. The diagonal of any scheme morphism is an immersion,
hence locally of finite type, and is a monomorphism, hence
quasi-separated. Quasi-separatedness of `f` gives quasi-compactness of
its diagonal. Quasi-compactness of `f` and `a` makes the self-product
`X ×_Y X` quasi-compact over the base. Relative closed-immersion
descent thus applies to the actual diagonal. A constructed pullback
comparison identifies its base change with the diagonal of the actual
base-changed morphism, up to the explicitly constructed isomorphism.
This gives the separatedness equivalence by its definition. The source
finitely presented model hypotheses imply the displayed assumptions;
the original filtered-ring specialization remains a separate obligation.
The paired Lean file defines a proposition only. Other source properties
and the whole-paper obligations remain separate.
