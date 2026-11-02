# Conditional double quotient for a smooth Picard presentation

This is an internal construction combining the represented Picard arrow
relation, the smooth-projection atlas bridge and the canonical quotient
comparison. It retains three explicit inputs: the full proposition
`AlgebraicSpace.SmoothRelationQuotientStatement.{u}`, descent of smoothness
along a smooth surjective source map, and etale local surjectivity of the
actual `etaleFamilyMap f L`. This module proves none of those inputs and
does not discharge `SmoothAutomorphismEtaleAtlasStatement`.

The remaining data is an actual family `L` on an arbitrary object scheme
`U : Over S`, a smooth surjective presentation by this family, local finite
type of `U` over `S`, and smooth representations of the full relative
automorphism presheaves. All schemes have the same arbitrary universe `u`.
Every scheme test, slice morphism and sheaf section is retained.

The proof of `smoothDoubleQuotient_picardProperties` first uses
`exists_smoothArrowRelation`. This gives an actual scheme `A` representing
all arrows between members of the family, smooth endpoints `a, b : A → U`,
and an actual scheme `R` representing the full kernel of the endpoint
map. The kernel projections `r, s : R → A` are smooth, form a monomorphic
equivalence relation on every test and admit the required common etale
atlas. The arrow scheme `A` is locally of finite type over `S`.

The first application of the explicit generic quotient hypothesis gives
the geometric properties of the fixed canonical etale arrow-class sheaf
`B`, including its fppf sheaf property, representable diagonal, etale
atlas, and the smooth surjective canonical map `q : A → B`.
`arrowKernelQuotientSpace` packages this precise sheaf as an algebraic
space. The descended endpoint equations identify the composites of `q`
with the two endpoints of `B` with the Yoneda maps of `a` and `b`.

Applying `smoothProjectionAtlasOfSmoothCover` to these equations and the
explicit smooth-source descent input gives an actual etale atlas of `B`
on which both endpoints to `U` are smooth. The complete arrow-class kernel
comparison supplies the equivalence-relation property on all sections of
`B`. Thus the generic quotient hypothesis applies a second time, with
object scheme `U` and relation algebraic space `B`. This second quotient
has the fppf sheaf property, a scheme-representable diagonal and an etale
surjective scheme atlas locally of finite type over `S`.

The explicit local-surjectivity input permits
`arrowClassQuotientPicardIso` to identify this entire second quotient
naturally with `RelativePicard.etaleClassSheafPresheaf f`. Transport along
this natural isomorphism proves the three properties for the actual
ordinary presheaf. This comparison includes sections with no global
line-bundle representative.

`smoothDoubleQuotientPicardSpace` packages those properties as an actual
algebraic space whose underlying presheaf is definitionally the ordinary
etale Picard class sheaf. Its presheaf lemma records that identity.
`smoothDoubleQuotient_picardAtlas` retains the local finite type conclusion
when forgetting the additional fppf sheaf property.

The provenance is this internal composition of the named interfaces.
The construction assumes the generic quotient proposition in full and
does not replace its proof with representability of the desired sheaf.
An exact proof of the host target must separately discharge that input,
smooth-source descent and local surjectivity, using accepted Library
proofs. No descent of line bundles is inferred or needed in this
conditional construction once the stated presentation data is given.
