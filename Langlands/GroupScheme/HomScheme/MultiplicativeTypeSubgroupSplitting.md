# Hopf coordinates for affine fppf subgroup splitting

Author: Worker 872.

`HomScheme.exists_fppf_diagPoints` takes an actual closed
multiplicative-type subgroup of `G_T`, where `G` is an affine group
scheme over `Spec R` and `T` is affine over that base. It produces
finitely many affine test schemes `Spec C_k → T` with flat maps
locally of finite presentation that jointly cover `T`. For each
member it supplies a finitely generated additive commutative
character group `Λ_k` and a Hopf point
`O(G) → C_k ⊗[R] R[Λ_k]`. The scalar extension of this Hopf point is
surjective, and its actual homomorphism has exactly the evaluated
all-test subgroup range of the original inclusion.

There is no torsion-freeness or smoothness requirement on the
subgroup and no smoothness requirement on `G`. The conclusion is an
fppf splitting cover; it does not assert étale splitting or a
residually trivial point on any cover member. Character groups can
vary between members and are left as arbitrary finitely generated
abelian groups rather than being put in a chosen normal form.

The construction first uses
`RelativeMultiplicativeType.affineSplittingCover` to refine the
fppf cover in the multiplicative-type definition to finitely many
affine members. Choose a character group and actual diagonalizable
isomorphism on each member. The published generic `TorusSplitting`
coordinate-ring and test-morphism constructions give each ring its
`R`-algebra structure through its composite map to `Spec R`.

`DiagonalizableSplitting.chartRelHom` expresses the pulled-back
inclusion as a relative homomorphism from the fixed model of
`D(Λ_k)` over `Spec R`, using the diagonalizable base-change
isomorphism. Its auxiliary lemmas preserve closedness and the actual
all-test range under this source identification. The diagonalizable
Hopf-point equivalence then supplies the desired coordinates.
Its closed-immersion criterion proves scalar-extension surjectivity;
source-isomorphism invariance proves the exact evaluated-range
identity.

This is an internal derived adapter combining the finite affine
splitting construction, generic subgroup-family evaluation and
`DiagonalizablePoint.diagPointEquiv`. It is the fppf analogue of the
published split-torus `exists_etale_splitPoints` argument and
asserts no subgroup-chart representability theorem by itself.
