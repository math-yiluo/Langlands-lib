# Changes of coordinates for group-scheme coefficient representations

This is an internal construction from the published `MatrixRepresentation`,
`InnerAutomorphism`, and `HomConjugacy` APIs. It constructs an actual conjugated
scheme representation and an explicit equivalence of its full affine coefficient
representations. No external-literature identification is asserted.

## Parameters and convention

The base is any commutative ring `R : CommRingCat.{u}`. The source `G` is an
actual group scheme over `Spec R`, and `n : Type` is finite with decidable
equality. No nonemptiness of `n`, nontriviality of `R`, field, smoothness, or
topology hypothesis is needed. Affine test algebras `S : CommAlgCat.{u} R`
have the same universe as the base ring.

A coordinate change is a single actual base point

```lean
g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X
```

of the general linear group scheme. For a test scheme `T` over `Spec R`, write
`g_T` for `constantPoint g T`, the pullback of this point along the structure
map of `T`. The same `g` is used on every test scheme. It is not an independently
chosen family of conjugators.

Our convention is `ρᵍ(x) = g_T ρ(x) g_T⁻¹`. Consequently the map from the
original coefficient representation to the conjugated one is multiplication
by the matrix of `g_T`. This specifies the direction of the coordinate change.

## Actual scheme construction

`conjugate ρ g` is the composite of the actual group-scheme morphism `ρ` with
`(GeneralLinear.groupScheme n R).innerIso g`. Its target remains the same
explicit general linear group scheme. The imported `innerIso` constructs the
scheme automorphism from the natural family of point conjugations by
full faithfulness of group-valued Yoneda. Neither that automorphism nor its
naturality is supplied as an additional hypothesis here.

`comp_conjugate` proves, for every test scheme and every source point `x`,

\[
x\mathbin{\gg}\rho^g=g_T\,(x\mathbin{\gg}\rho)\,g_T^{-1}.
\]

The proof reassociates the actual morphism composite and applies the published
`comp_innerIso_hom`. Applying the multiplicative point-coordinate equivalences
gives `conjugate_pointMatrix`, over the global-section ring of every `T`, and
`conjugate_affineMatrix`, over the affine test algebra `S` itself.

For the latter formula, let `C_S` be the matrix of `g_T` for
`T = (algSpec R).obj (op S)`. Then the formula is

\[
 (\rho^g)_S(x)=C_S\,\rho_S(x)\,C_S^{-1}.
\]

In Lean the conjugating matrix is expressed as the `affineMatrix` of the
standard representation at `g_T`; the published `standard_affineMatrix`
identifies this with `GeneralLinear.affinePointsEquiv` at `g_T`.

`conjugate_affineAction` states the same conjugation identity in the group of
`S`-linear automorphisms of `n → S`. It follows by applying the two published
monoid homomorphisms that turn invertible matrices into linear automorphisms.
The existing naturality results for every `MatrixRepresentation` also apply
to `conjugate ρ g`.

## Full affine representation equivalence

`conjugateAffineEquiv ρ g S` has type

```lean
(ρ.affineRepresentation S).Equiv ((ρ.conjugate g).affineRepresentation S)
```

Both representations are of the same full group of affine `S`-points of `G`
on the whole coordinate module `n → S`. Its underlying linear equivalence
is the standard affine action of `g_T`, and `conjugateAffineEquiv_apply` gives
its value on every vector:

\[
 v\longmapsto C_S v.
\]

The `Representation.Equiv` structure includes the intertwining identity
`C_S ρ_S(x) = (ρᵍ)_S(x) C_S`. The proof uses the established action conjugation
formula and cancellation of the inverse linear equivalence. Thus this is a
bundled equivalence of representations, not only a bijection of carriers or
an unproved existence condition.

For every algebra map `f : S ⟶ T`,
`conjugateAffineEquiv_naturality` proves

\[
 e_T\bigl((f(v_i))_i\bigr)=\bigl(f((e_S(v))_i)\bigr)_i.
\]

The proof combines the published naturality of `constantPoint` with
`affineAction_naturality` for the standard representation. This is a pointwise
scalar-change identity on coordinate vectors; the module does not introduce a
new tensor-extension comparison.

## Laws and scope

`conjugate_restrict` states that conjugation commutes with restriction along
any actual group-scheme morphism `H → G`. It is category associativity.
`conjugate_one`, `conjugate_mul`, and `conjugate_inv` prove

\[
 \rho^1=\rho,\qquad (\rho^g)^h=\rho^{hg},\qquad
 (\rho^g)^{g^{-1}}=\rho.
\]

These are equalities of actual scheme morphisms. The first two proofs use
`hom_ext_points`, the explicit point formula, preservation of identity or
multiplication by `constantPointHom`, and group identities. The inverse law
then follows from the multiplication law.

Finally, `nonempty_affineEquiv_of_homConjugate` extracts a base conjugator from
the published relation `HomConjugate ρ σ` and applies `conjugateAffineEquiv`.
It proves existence of an equivalence for every affine test algebra. It does
not assert a converse from unrelated pointwise equivalences to scheme conjugacy.

The construction handles coordinate changes supplied as actual base points of
GL. It does not construct a representation on an arbitrary finite projective
module, classify basis-independent algebraic representations, differentiate a
representation, or attach it to an automorphic infinity component. Those
constructions remain separate obligations.
