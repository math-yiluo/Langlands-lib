# Flat nilpotent reflection of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeFlatNilpotentReflection.{u}` proves
`MultiplicativeTypeFlatNilpotentReflectionStatement.{u}`. The hypotheses are
flatness of the group scheme over `Spec A`, nilpotence of `J`, and
multiplicative type after base change to `Spec (A ⧸ J)`.

The proof uses `multiplicativeTypeQuasiIsotrivial` to obtain an étale splitting
cover over `Spec (A ⧸ J)`. The quotient spectrum map is surjective by
nilpotence. For a point of `Spec A`, choose a point above it in the quotient
spectrum and then a point of a splitting cover member above that point.
The proof refines this member by taking an affine open containing its chosen
point and applying `Algebra.IsEtaleAt.exists_isStandardEtale` to obtain a
principal open containing the point. Its ring `C` is standard étale over
`A ⧸ J`, and the reduced group remains diagonalizable over `Spec C`.

`StandardEtaleLift.exists_etale_nilpotent_lift` supplies an étale `A`-algebra
`B` and a compatible surjection `q : B →+* C` with nilpotent kernel. The
compatibility of the ring maps gives a commutative square of spectra and
places the chosen point of `Spec C` above the original point of `Spec A`.
The pullback comparison for this square identifies the base change of the
group along `Spec C → Spec B → Spec A` with the diagonalizable group over
`Spec C`. The isomorphism `B ⧸ RingHom.ker q ≃+* C` identifies this base
change with the scalar reduction of the group over `Spec B`.

Flatness passes to the group over `Spec B`.
`NilpotentReduction.isDiagonalizable_of_baseChange` recovers affineness by
finite-surjective affine descent and applies split reflection with the
finitely generated character group of the reduction. This proves
diagonalizability over `Spec B`. The resulting pointwise étale splitting
neighbourhoods give an étale splitting cover by
`MultiplicativeTypeQuasiIsotrivial.exists_etale_cover_of_pointwise`.
Each member is flat and locally of finite presentation, so the cover
also gives the required fppf splitting.

The étale local reduction is the one used in SGA 3, Exposé X,
Corollary 2.3. The implemented proof uses the algebraic chart lift and the
Library's split deformation theorem. The source locators and the comparison
of multiplicative-type conventions are in the
[statement documentation](MultiplicativeTypeFlatNilpotentReflectionStatement.md).
