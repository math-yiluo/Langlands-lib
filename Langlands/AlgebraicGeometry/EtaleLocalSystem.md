# Actual abelian étale local systems

This module defines actual abelian presheaves and local systems on the big
relative étale site of an arbitrary scheme. All declarations below belong to
`Langlands.AlgebraicGeometry.EtaleLocalSystem`.

## Source and scope

The source is Brian Conrad, *Reductive group schemes* (2014), Proposition B.3.4,
printed pp.290–292, especially its description on p.291 of locally constant
abelian étale sheaves with finitely generated geometric fibres. The opening of
the proof of Corollary B.3.6, pp.293–294, describes local constancy using
trivializations over the constituents of an étale cover. The registered source
is `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

The concrete big-site interface is an implementation of those local models.
It includes elementary sheaf and restriction lemmas. The module does not assert
local constancy of a character functor, an anti-equivalence with groups of
multiplicative type, or finite étale triviality over a normal scheme.

## Site, variance and universes

For `S : Scheme.{u}`, `topology S` is
`Scheme.etaleTopology.over S`, a Grothendieck topology on **all** objects
`V : Over S`. The structure morphism `V.hom : V.left ⟶ S` need not be étale.
A covering family has jointly surjective étale underlying scheme morphisms.
This is the big relative site, rather than the full subcategory of schemes
étale over `S`.

An actual abelian presheaf is a functor
`(Over S)ᵒᵖ ⥤ AddCommGrpCat`. Its contravariant maps are part of the functor.
`IsEtaleSheaf F : Prop` is exactly
`CategoryTheory.Presheaf.IsSheaf (topology S) F`; it imposes étale descent on
that functor.

The scheme universe `u` and coefficient universe `v` are independent.
`restrict`, its coherence isomorphisms and `IsEtaleSheaf` allow a presheaf
valued in `AddCommGrpCat.{v}`. For
`M : AddCommGrpCat.{v}`, the function spaces in the constant model take values
in `AddCommGrpCat.{max u v}`. Accordingly
`IsFinitelyGeneratedLocallyConstant.{u,v}` takes a presheaf with values in
`AddCommGrpCat.{max u v}` and uses coefficient groups in `AddCommGrpCat.{v}`.
The étale cover has index type in `Type u`. There is no specialization to
universe zero, and no condition on the scheme such as connectedness, normality
or a noetherian hypothesis.

## Constant models

`constant S M` is the composite of `(Over.forget S).op` with Mathlib's
`AlgebraicGeometry.continuousMapPresheafAb M`. The topology on the carrier of
`M` is explicitly the discrete topology `⊥`. Thus its sections over
`V : Over S` are continuous maps `V.left → M`, with pointwise addition.

`constantSections S M V` is an additive equivalence from those sections to
`LocallyConstant V.left M`. It uses the equivalence between continuity to a
discrete space and local constancy. For `a : W ⟶ V`,
`constantSections_map` states the pointwise formula

```text
constantSections S M W ((constant S M).map a.op f) x
  = constantSections S M V f (a.left x).
```

These are the usual constant étale sheaf models: sections are locally constant
functions, including on disconnected test schemes, and restriction pulls back
functions. Restricting the interface to test schemes étale over `S` expresses
the usual small-site local trivializations. The formal interface itself uses
natural isomorphisms on all schemes over each covering member.

`isEtaleSheaf_constant S M` proves étale sheafness of every such model, with no
finite generation hypothesis. Its implementation restricts Mathlib's
`isSheaf_fpqcTopology_continuousMapPresheafAb` along
`etaleTopology ≤ proetaleTopology ≤ fpqcTopology` and then along the continuous
forgetful functor `Over.forget S`.

## Restriction and coherence

For any scheme morphism `g : T ⟶ S`,
`restrict g F := (Over.map g).op ⋙ F`.
At `V : Over T`, this evaluates `F` on `V.left` with structure morphism
`V.hom ≫ g`. No étaleness hypothesis is imposed on `g`. The maps use the same
underlying morphisms of test schemes.

The comparison declarations are:

| Declaration | Comparison |
| --- | --- |
| `restrictIso g e` | transports a natural isomorphism `e : F ≅ G` through restriction |
| `restrictIdIso F` | `restrict (𝟙 S) F ≅ F` |
| `restrictCompIso g h F` | `restrict (h ≫ g) F ≅ restrict h (restrict g F)` |
| `restrictCongrIso w F` | compares restrictions for an equality `w : g = h` |
| `restrictConstantIso g M` | `restrict g (constant S M) ≅ constant T M` |

The identity, composition and equality comparisons are whiskered
over-category comparisons from Mathlib. The constant comparison is
definitionally the identity because the construction forgets the structure
morphism to the base.

`isEtaleSheaf_iff_of_iso` proves invariance under natural isomorphism.
`isEtaleSheaf_restrict` proves that restriction along every `g` preserves
étale sheaves, using continuity of `Over.map g` for the relative topologies.

## Finitely generated local systems

`IsFinitelyGeneratedLocallyConstant.{u,v} F : Prop` is the conjunction of:

1. `IsEtaleSheaf F`;
2. existence of a
   `Scheme.Cover.{u} (Scheme.precoverage @Etale) S` such that for every index
   `i`, there is `M : AddCommGrpCat.{v}` with `AddGroup.FG M` and a natural
   isomorphism
   `restrict (𝒰.f i) F ≅ constant (𝒰.X i) M`.

`Scheme.precoverage @Etale` includes joint surjectivity as well as étaleness.
The isomorphism is recorded by `Nonempty`, so all choices remain within the
Prop-valued predicate. Finite generation means finite generation of the
underlying additive group. It does not impose freeness or exclude torsion.
The coefficient group can vary with `i`; neither a single global model nor a
uniform bound on its rank or torsion is required.

`isFinitelyGeneratedLocallyConstant_constant` proves the predicate for a
finitely generated constant model using the identity cover.
`isFinitelyGeneratedLocallyConstant_iff_of_iso` transports local
trivializations along a natural isomorphism of actual presheaves.
`isFinitelyGeneratedLocallyConstant_restrict` proves preservation along every
base morphism. It pulls back the witnessing étale cover and composes the
restriction comparisons, the pullback square equality, the restricted local
trivialization and `restrictConstantIso`. These are elementary consequences of
the concrete definitions, rather than additional claims from Conrad.

## Application to actual relative characters

After importing this module and
`Langlands.GroupScheme.Cartier.Characters`, for
`G : Langlands.CommGroupScheme S`, the expression

```lean
Langlands.AlgebraicGeometry.EtaleLocalSystem.IsFinitelyGeneratedLocallyConstant.{u,u}
  (Langlands.GroupScheme.Cartier.characters G)
```

is a proposition in every scheme universe `u`. The published character functor
already has domain `(Over S)ᵒᵖ` and codomain `AddCommGrpCat.{u}`, so the
predicate applies directly. The two occurrences of `u` select local coefficient
groups in that same universe; `max u u = u`. A downstream theorem may assert
this proposition under the appropriate group-scheme hypotheses. This module
provides the proposition and restriction interface without proving that
additional theorem.
