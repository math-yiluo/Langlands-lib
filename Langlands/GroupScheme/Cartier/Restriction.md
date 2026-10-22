# Restriction of relative homomorphisms and the relative Hom functor

Author: Worker 207.

This module makes the relative Hom groups of
`Langlands.GroupScheme.Cartier.Evaluation` into a contravariant functor on the
category `Over S` of `S`-schemes. Throughout, `G`, `G'`, `G''` and `H` are
arbitrary commutative group schemes over a scheme `S`
(`Langlands.CommGroupScheme S`), and `T`, `T'`, `T''` are objects of `Over S`.
`RelativeHom G H T` is the published actual Hom group from the base change of
`G` to `T` to the base change of `H` to `T`; it is written additively, so the
pointwise product of homomorphisms with values in `H` appears as `+`. No
pointwise group homomorphism is supplied as an independent input anywhere in
this module.

## Base change and the canonical comparison isomorphisms

`testBaseChange T G` abbreviates `(CommGroupScheme.baseChange T.hom).obj G`, the
base change `G_T = G ×_S T` as a commutative group scheme over `T.left`.

For `a : T' ⟶ T`, `pullbackCompIso a` is the natural isomorphism, of functors
from `Over S` to `Over T'.left`, between pullback along `T'.hom` and pullback
along `T.hom` followed by pullback along `a.left`. Its component at `X` is the
canonical isomorphism `pullback.congrHom` (using `T'.hom = a.left ≫ T.hom`)
followed by the inverse of Mathlib's pasting isomorphism
`pullbackLeftPullbackSndIso`.
`baseChangeCompIso G a` applies the induced natural isomorphism of group-object
functors (`Functor.mapGrpNatIso`) and the composition isomorphism
`Functor.mapGrpCompIso`. It is the canonical isomorphism
`G_{T'} ≅ (G_T)_{T'}` of group objects over `T'.left`, where the right side is
the base change of `G_T` along `a.left` (`GroupScheme.baseChange`).
The group structures are transported by these functors, so no group law is
chosen by hand.

`baseChangeProj G a : G ×_S T' ⟶ G ×_S T` is the canonical projection over `a`,
the pullback lift of the first projection and of the second projection followed
by `a.left`. The lemmas `baseChangeProj_fst` and `baseChangeProj_snd` record
these two components, and `baseChangeProj_id` and `baseChangeProj_comp` state
`baseChangeProj G (𝟙 T) = 𝟙` and
`baseChangeProj G (b ≫ a) = baseChangeProj G b ≫ baseChangeProj G a`.
`baseChangeCompIso_hom_fst` states that the comparison isomorphism followed by
the first projection of the pullback along `a.left` is `baseChangeProj G a`.
`baseChangeCompIso_inv_fst` states that its inverse followed by the first
projection to `G` is the composite of the two first projections.

For a homomorphism `φ : G' ⟶ G`, `baseChange_map_fst` states that its base
change to `T`, followed by the first projection to `G`, equals the first
projection to `G'` followed by the underlying morphism of `φ`.
`baseChange_map_snd` states that the base change preserves the second
projections to `T.left`.
`relativeHom_ext` states that two elements of `RelativeHom G H T` are equal as
soon as their underlying scheme morphisms agree after the first projection
`H ×_S T ⟶ H`. The second components agree automatically because both are
morphisms over `T`.

## Restriction along a test-scheme map

For `a : T' ⟶ T` and a group-object homomorphism `χ : G_T ⟶ H_T`,
`restrictGrp G H a χ` is the composite of `(baseChangeCompIso G a).hom`, the base
change of `χ` along `a.left`, and `(baseChangeCompIso H a).inv`. This is the
construction prescribed by the task: base change along the test-scheme map,
conjugated by the canonical comparison isomorphisms.
`restrict G H a : RelativeHom G H T →+ RelativeHom G H T'` is this map on the
additively written Hom groups. It preserves zero and addition because base
change along `a.left` preserves finite products, hence the constant unit
morphism and pointwise products of morphisms, and because composing with the
comparison homomorphisms respects both.
`restrict_toMul` records definitionally that restriction is `restrictGrp` on
the underlying multiplicative homomorphisms.

`restrict_fst` is the defining formula on first projections:
the underlying morphism of `restrict G H a χ`, followed by the first projection
to `H`, equals `baseChangeProj G a`, then `χ`, then the first projection to `H`.
By `relativeHom_ext` this formula determines the restriction uniquely.
From it and the laws of `baseChangeProj`, `restrict_id` proves
`restrict G H (𝟙 T) χ = χ` and `restrict_comp` proves
`restrict G H (b ≫ a) χ = restrict G H b (restrict G H a χ)` for
`b : T'' ⟶ T'`.

`relativeHomFunctor G H : (Over S)ᵒᵖ ⥤ AddCommGrpCat` is the relative Hom
functor `T ↦ Hom_T(G_T, H_T)`. Its value at `T` is `RelativeHom G H T` and its
map along `a` is `restrict G H a`. Its identity and composition axioms are
`restrict_id` and `restrict_comp`. The simp lemmas
`relativeHomFunctor_map_apply` and `relativeHomFunctor_obj` unfold its map and
its underlying types.

## Naturality of evaluation in the test scheme

For a `T`-point `x : T ⟶ G.X` (a morphism in `Over S`), write `s(x)` for the
section `(sectionPointsEquiv G T).symm x` of `G_T` over `T`.
`sectionPointsEquiv_symm_fst` states that `s(x)` followed by the first
projection is `x.left`. `sectionPointsEquiv_symm_snd` states that it is a
section of the second projection.
`sectionPointsEquiv_symm_comp_baseChangeProj` states that `s(a ≫ x)` followed by
`baseChangeProj G a` equals `a.left ≫ s(x)`.

`evaluation_restrict` proves naturality of the published evaluation pairing in
the test scheme:
`evaluation (restrict G H a χ) (a ≫ x) = a ≫ evaluation χ x`.
Thus restricting a relative homomorphism and a point along `a` restricts the
evaluated point.
For an integer `n` with `multiplication G.toGrp n = 1`,
`torsionEvaluation_restrict` proves the same identity for the published
evaluation into the torsion scheme of `H`. The proof cancels the monomorphism
`torsionι H.toGrp n`.

## Contravariance in the source group scheme

For `φ : G' ⟶ G`, `precompose H φ T : RelativeHom G H T →+ RelativeHom G' H T`
sends `χ` to the composite of the base change of `φ` to `T` with `χ`
(`precompose_apply`). It is Mathlib's `Preadditive.leftComp`, so additivity
comes from the preadditive structure of commutative group schemes over
`T.left`. `precompose_id` and `precompose_comp` state
`precompose H (𝟙 G) T χ = χ` and
`precompose H (ψ ≫ φ) T χ = precompose H ψ T (precompose H φ T χ)` for
`ψ : G'' ⟶ G'`.

`baseChange_map_baseChangeProj` states that the canonical projections commute
with base changes of `φ`. Using it, `restrict_precompose` proves
`restrict G' H a (precompose H φ T χ) = precompose H φ T' (restrict G H a χ)`.
Hence `precomposeNatTrans H φ : relativeHomFunctor G H ⟶ relativeHomFunctor G' H`
is a natural transformation with components `precompose H φ T`
(`precomposeNatTrans_app_apply`). `precomposeNatTrans_id` and
`precomposeNatTrans_comp` state `precomposeNatTrans H (𝟙 G) = 𝟙` and
`precomposeNatTrans H (ψ ≫ φ) = precomposeNatTrans H φ ≫ precomposeNatTrans H ψ`.
`relativeHomBifunctor H : (CommGroupScheme S)ᵒᵖ ⥤ (Over S)ᵒᵖ ⥤ AddCommGrpCat`
packages these as a functor contravariant in the source group scheme. Its value
at `G` is `relativeHomFunctor G H`.

The imported `evaluation_precompose` applies definitionally in
terms of `precompose`. It says that evaluating `precompose H φ T χ` at
`x : T ⟶ G'.X` equals evaluating `χ` at `x` composed with the underlying morphism
of `φ`. Under `n`-annihilation hypotheses on both `G` and `G'`,
`torsionEvaluation_precompose` proves the same compatibility for the
torsion-valued evaluation.

## Source and provenance

These are derived constructions. Edixhoven–van der Geer–Moonen, *Abelian
Varieties*, preliminary draft, (3.21), printed p.41/PDF45, defines, for any
commutative group scheme `G` over `S`, the contravariant group functor
`Hom(G, Gm,S) : T ↦ Hom_T(G_T, Gm,T)` on `S`-schemes. Theorem (3.22), printed
p.42/PDF46, again names it the contravariant functor `Sch/S → Gr`. The source
leaves restriction along `T' ⟶ T` implicit. Here it is made explicit by base change and the canonical
comparison isomorphisms. The source likewise leaves the identity and
composition laws implicit, and here they are proved. Definition (3.23), printed
p.43/PDF47, introduces the induced dual homomorphism `f^D : G_2^D ⟶ G_1^D` for
finite locally free group schemes. Our `precomposeNatTrans` is the functorial
counterpart, for arbitrary commutative group schemes, of this contravariance:
precomposition with the base change of `f`. The evaluation naturality relates
to the evaluation `e_f(x, y) = β(y)(x)` of (11.11)(i), printed p.162/PDF166, whose
values are points with values in arbitrary test schemes.

The module generalizes the target `Gm,S` to an arbitrary commutative group
scheme `H`. Specialization to the constructed multiplicative group scheme is a
separate later module. It does not use the representability theorem (3.22), the
Hopf-algebra construction of `G^D`, or any finiteness assumption. It asserts no
Cartier representability, finite local freeness, biduality or duality of
isogeny kernels.

The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
PDF45–47 and PDF166 were read.
