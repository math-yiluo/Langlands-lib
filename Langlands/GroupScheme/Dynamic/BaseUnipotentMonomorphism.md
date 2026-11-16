# Relative unipotent monomorphisms over arbitrary base schemes

This is an internal extension of `Dynamic.AffineUnipotentMonomorphism` from
affine bases to arbitrary schemes. Its provenance is descent along affine open
charts, the existing base-change identities for dynamic subgroup functors,
and the affine closedness theorem; it asserts no separate translation from an
external source.

Let \(S\) be any scheme, \(G,H\) group schemes over \(S\),
\(\chi:\mathbf G_{m,S}\to G\) a cocharacter, and \(f:G\to H\) a homomorphism.
Suppose \(i:U\to G\) and \(j:V\to H\) represent the actual functors
\(U_G(\chi)\) and \(U_H(f\chi)\), on every scheme over \(S\).

`Dynamic.unipotentFactorOverBase` is the induced homomorphism \(U\to V\).
The theorem `unipotentFactorOverBase_comp` proves its defining square
\(g\,j=i\,f\). The construction uses the generic restriction homomorphism
and functoriality of the contraction condition. It requires no affineness or
monicity assumption.

If the structure morphisms of \(G\) and \(H\) are affine and the underlying
morphism \(f\) in schemes over \(S\) is monic, then
`isClosedSubgroup_unipotent_of_represented_overBase` proves that **every**
homomorphism \(g:U\to V\) with that square is a closed immersion.
`isClosedSubgroup_unipotentFactorOverBase` specializes this result to the
constructed homomorphism. Closed immersion has its ordinary scheme meaning:
`IsClosedSubgroup g` is `IsClosedImmersion g.hom.hom.left`. There are no
smoothness, flatness, connectedness, finite type, or finite presentation
hypotheses. The base scheme and universe are arbitrary.

The proof first establishes two general descent helpers in
`BaseClosedImmersion`. The theorem `baseChange_isPullback` identifies the
underlying pullback square of a morphism in `Over S`. This follows from the
two defining pullback squares and pullback pasting, generalizing the same
construction used by the field-based `DominantHomFlat.baseChange_isPullback`.
The theorem `of_affine_baseChange` pulls the affine open cover of \(S\) back
to the target of a morphism. On each piece, the canonical pullback projection
is identified with the map pulled back from \(S\), by the isomorphism furnished
by the preceding square. Closedness is unchanged by this isomorphism and is
local at the target, so closedness on all affine base charts implies global
closedness.

For the group-scheme result, base change preserves the supplied subgroup
representations, and `unipotent_baseChange` and
`baseChangeCocharacter_comp` identify their functors with the correct
base-changed cocharacters. The square for \(g\) is carried by the base-change
functor to the same square over each affine chart. The base-changed ambient
groups are affine schemes and the ambient map remains monic. The imported
affine theorem therefore proves closedness on that chart, and the general
descent helper finishes.

This unit proves closedness of induced unipotent subgroup maps. It does not
prove the reductive monomorphism theorem: the centralizer, cell, and global
steps remain separate obligations.
