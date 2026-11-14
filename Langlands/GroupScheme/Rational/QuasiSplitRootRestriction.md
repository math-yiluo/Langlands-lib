# Total root restriction for quasi-split groups

This internal supporting unit compares actual adjoint roots of algebraic groups.
All fields and group schemes have the same arbitrary universe level. No
restriction on the characteristic is imposed.

## A torus centralizer prevents vanishing roots

Let `G` be an affine group scheme locally of finite type over a field `k`.
Let `S` and `T` be split tori, with homomorphisms `a : S → G`, `j : T → G`
and `f : S → T` such that `f ≫ j = a`. Assume the whole-group centralizer
`torusCentralizer a` is represented by `j`. Then
`root_restrict_ne_zero_of_sameField_torusCentralizer` proves that every actual root
`β` of `j` has nonzero restricted character `f ≫ β`.

Choose a nonzero vector in the root weight space. If the restricted character
were zero, weight-space functoriality would place this vector in the zero
weight space for `a`. The published Lie comparison puts it in the whole-torus
centralizer on every scheme test. Representability by `j` puts it in the range
of `j`; commutativity of `T` then puts it in the centralizer of `j`, hence in
the zero weight space for `j`. Disjointness of distinct weight spaces for a
split torus contradicts the chosen vector's nonvanishing.

`rootRestrictionOfTorusCentralizer` consequently restricts every root of `j`
to a root of `a`, without excluding any roots from its domain. Its value lemma
identifies the resulting character with ordinary composition by `f`.

## A containing maximal torus over a splitting field

Suppose now `G` is quasi-split, `a` is a maximal split torus, and `j` is a
maximal torus containing it by `f`. Let `L/k` be any field extension over
which `T` splits. The original affine and locally finite type assumptions
are retained explicitly in the section. The published
`quasiSplitMaximalTorusCentralizer` identifies the original whole centralizer
with `j`; representability and the all-test centralizer commute with base
change. The preceding argument therefore proves
`IsQuasiSplit.root_restrict_ne_zero` for every root of `j_L`.

`IsQuasiSplit.rootRestriction` is the resulting total map from the roots of
`j_L` to the roots of `a` over `k`. Restrict the character to `S_L` and apply
the inverse of the split-torus character base-change equivalence. Root
membership follows from the published split-torus root-restriction and
root-support base-change comparisons.
`IsQuasiSplit.rootRestriction_baseChange` states that pulling back its value
recovers the actual restricted character. Finally,
`IsQuasiSplit.rootRestriction_surjective` lifts any original relative root
with `splittingFieldRootLift` and uses this equality and injectivity of
character pullback to prove surjectivity.

## Provenance and scope

This is an internal derivation from published centralizer, Lie weight-space,
root-restriction and base-change results; it is not a transcription of a
literature statement. It does not assert injectivity of root restriction,
splitting of `T` over `k`, or the local anisotropic affine-diagram theorem.
Those remain further obligations of the host task.
