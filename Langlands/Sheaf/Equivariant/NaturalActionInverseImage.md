# The inverse image along a natural action

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.NaturalActionSheaf` (imported), and through it
  `Langlands.Sheaf.Equivariant.NaturalActionSections`: natural actions
  `NaturalAction K Φ` of a monoid `K` along `Φ : E ⥤ T`, with fields
  `act : ∀ V, K →* (End (Φ.obj V))ᵐᵒᵖ` and `comm`. For a group `K` they also give
  `actionRepresentation F (a.act V)` (the representation of `K` on `F(Φ V)` in which `k`
  acts by `F.map (a.act V k).unop.op`), the invariant presheaf
  `a.invariantPresheaf R F : V ↦ F(Φ V)^K` with its inclusion `a.invariantPresheafι R F`, the
  functors `a.invariantFunctor R` (module presheaves on `T` to module presheaves on `E`) and
  `a.sheafInvariantFunctor R J` (its precomposite with `sheafToPresheaf J`), and, for
  continuous `Φ`, the functor `a.sheafInvariantSheafFunctor R J JE` from module sheaves on
  `T` to module sheaves on `E` with `a.sheafInvariantSheafFunctorCompIso R J JE`.
- `Langlands.Sheaf.Equivariant.TwistedOver` (imported): the twisted category
  `TwistedOver P ρ` for `ρ : G →* Aut X`, with morphisms carrying a group element `twist`
  (`Hom.twist`, `comp_twist`: the twist of `f ≫ g` is `g.twist * f.twist`), and the
  inclusion `ι P ρ : P.Over ⊤ X ⥤ TwistedOver P ρ`. That inclusion is the identity on
  objects and gives twist `1` (`ι_map_twist`); it is faithful (`map_injective`), and
  `exists_ι_map_of_twist_eq_one` states that a twisted morphism between objects of
  `P.Over ⊤ X` with twist `1` is the image of a morphism over `X`.
- Mathlib: `SingleObj` (with `SingleObj.comp_as_mul`), `MulOpposite`, `Prod.sectL`,
  `CategoryTheory.Prod.fst`, `prod_comp`, `CategoryTheory.Prod.hom_ext`,
  `Adjunction.mkOfHomEquiv`, `Adjunction.comp`, `Adjunction.ofNatIsoRight`,
  `Adjunction.restrictFullyFaithful`, `LinearMap.codRestrict`, `LinearEquiv.ofEq`,
  `Functor.lan`, `Functor.lanAdjunction`, `Functor.HasLeftKanExtension`,
  `Functor.HasPointwiseLeftKanExtension`, `Functor.leftKanExtensionObjIsoColimit`,
  `presheafToSheaf`, `sheafificationAdjunction`, `fullyFaithfulSheafToPresheaf`,
  `CostructuredArrow` (with `mk`, `homMk`, `isoMk`, `hom_ext`, `w`, `proj`),
  `Functor.IsEquivalence` and `Functor.Final.colimitIso` (an equivalence is final).

All declarations are in the namespace `Langlands.Sheaf.Equivariant`, inside
`NaturalAction`.

## Purpose

`NaturalActionSections` and `NaturalActionSheaf` construct the functor
`F ↦ (V ↦ F(Φ V)^K)` of invariant sections along a natural action. This module constructs
its left adjoint, the inverse image, on presheaves and on sheaves. It also computes the
inverse image presheaf as a colimit. For a `G`-space `X`, the functor of invariant sections
is Berkovich's `(b_*F)^G`, and the left adjoint constructed here corresponds to his inverse
image `b^*` along `b : X → X(G)`. That case is `AnalyticInverseImage`.

The inverse image is a left Kan extension. Morphisms in `T` that differ by the action of `K`
have to be identified, so the Kan extension is taken along the inflation below rather than
along `Φ`. When `T` is a twisted category and the action of `k` has twist `k⁻¹`, the comma
categories of this Kan extension are equivalent to the comma categories of untwisted arrows.
The inverse image presheaf is then the colimit in Berkovich's formula (§1.2, printed p.3).

## Setting

`T : Type u` with `[Category.{v} T]` and `E : Type uE` with `[Category.{vE} E]`.
`R : Type uR` is a commutative ring, and modules live in `ModuleCat.{w} R`.

## The inflation

Let `K : Type uK` be a monoid, `Φ : E ⥤ T` and `a : NaturalAction K Φ`. In
`SingleObj Kᵐᵒᵖ` the composite `f ≫ g` is `g * f` in `Kᵐᵒᵖ`, that is, `f * g` in `K`
(`SingleObj.comp_as_mul`). This matches `act_mul_unop` below, so no inverses are needed.

- `act_one_unop`: `(a.act V 1).unop = 𝟙 (Φ.obj V)`. `act_mul_unop`:
  `(a.act V (k * l)).unop = (a.act V k).unop ≫ (a.act V l).unop`.
- `a.inflation : E × SingleObj Kᵐᵒᵖ ⥤ T`: the object `(V, ⋆)` goes to `Φ V`, and a morphism
  `(f, k) : (V, ⋆) ⟶ (W, ⋆)` goes to `Φ.map f ≫ (a.act W k.unop).unop`. Functoriality uses
  `act_one_unop`, `act_mul_unop` and `a.comm`. `inflation_obj`, `inflation_map` (both `rfl`).
- `a.sectInflationIso : Prod.sectL E ⋆ ⋙ a.inflation ≅ Φ`, componentwise the identity: on the
  objects `(V, ⋆)` and the morphisms `(f, 1)` the inflation is `Φ`.
- `starHom k`: the element `k` of `K` as an endomorphism of `⋆` in `SingleObj Kᵐᵒᵖ`.
- `sectAction E K : NaturalAction K (Prod.sectL E ⋆)`: `k` acts on `(V, ⋆)` by
  `(𝟙 V, k)` (`sectAction_act_unop`).
- `prod_hom_eq_sectL_map_comp f k`: `(f, k) = (f, 1) ≫ (𝟙 W, k)`; every morphism of
  `E × SingleObj Kᵐᵒᵖ` is a morphism `(f, 1)` followed by the action of an element of `K`.
- `inflation_map_sectL f`: the inflation sends `(f, 1)` to `Φ.map f`.
  `inflation_map_sectAction V k`: it sends the action of `k` on `(V, ⋆)` to the action of `k`
  on `Φ V`.
- `a.actIso V k`, for a group `K`: the action of `k` on `Φ V` as an isomorphism, with
  inverse the action of `k⁻¹` (`actIso_hom`, `actIso_inv`).

## The adjunction on presheaves

Now `K` is a group.

- `sectPullbackAdjunction E R K`: pulling a module presheaf on `E` back along
  `CategoryTheory.Prod.fst E (SingleObj Kᵐᵒᵖ)` (trivial action of `K`) is left adjoint to
  `(sectAction E K).invariantFunctor R`, which takes the `K`-invariant sections over the
  objects `(V, ⋆)`. Built with `Adjunction.mkOfHomEquiv`. A morphism `φ` from the pullback of
  `Q` to `P` has `K`-invariant values: naturality of `φ` along `(𝟙 V, k)` compares
  `φ(q)` with its translate by `k`, and `Q` sends `(𝟙 V, k)` to the identity. So `φ` factors
  through the invariant submodules (`LinearMap.codRestrict`). Conversely, a morphism `ψ` into
  the invariant sections, followed by the inclusion, is natural along every `(g, k)`. Indeed
  `(g, k) = (g, 1) ≫ (𝟙, k)` by `prod_hom_eq_sectL_map_comp`, and invariance absorbs
  `(𝟙, k)`. The two constructions are inverse, and both naturality conditions hold, by `rfl`.
- `invariants_inflation_eq R F V`: for `F : Tᵒᵖ ⥤ ModuleCat.{w} R`, the `K`-invariants of
  `a.inflation.op ⋙ F` at `(V, ⋆)` under `sectAction E K` equal the `K`-invariants of `F(Φ V)`
  under `a.act V`, as submodules of `F(Φ V)`. Proof: `inflation_map_sectAction`.
- `a.inflationInvariantIso R`: restricting along `a.inflation.op` and then taking
  `(sectAction E K).invariantFunctor R` is isomorphic to `a.invariantFunctor R`.
  Componentwise it is `LinearEquiv.ofEq` for `invariants_inflation_eq`. Naturality uses
  `inflation_map_sectL`.

Assume `[∀ F : (E × SingleObj Kᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{w} R, a.inflation.op.HasLeftKanExtension F]`.
This is a hypothesis of the section, not an instance found by search.
`AnalyticInverseImage` proves it in the analytic case.

- `a.inverseImagePresheafFunctor R : (Eᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Tᵒᵖ ⥤ ModuleCat.{w} R)`: the
  pullback along `CategoryTheory.Prod.fst E (SingleObj Kᵐᵒᵖ)` followed by the left Kan
  extension `Functor.lan` along `a.inflation.op`.
- `a.inverseImagePresheafAdjunction R : a.inverseImagePresheafFunctor R ⊣ a.invariantFunctor R`:
  the composite of `sectPullbackAdjunction` with `Functor.lanAdjunction`. Its right adjoint
  is identified with `a.invariantFunctor R` through `inflationInvariantIso`
  (`Adjunction.ofNatIsoRight`).
- `a.inverseImagePresheafObjIsoColimit R Q U`, assuming the pointwise left Kan extension
  `[a.inflation.op.HasPointwiseLeftKanExtension (Prod.fst.op ⋙ Q)]`: the value of the inverse
  image of `Q` at `U` is the colimit of `Q(V)` over `CostructuredArrow a.inflation.op (op U)`.
  This is `Functor.leftKanExtensionObjIsoColimit`. The objects of this comma category are the
  pairs of an object `V` of `E` and an arrow `h : U ⟶ Φ V` of `T`. A morphism from `(V, h)` to
  `(V', h')` is a pair `(f, k)` with `f : V' ⟶ V` such that
  `h' ≫ Φ.map f ≫ (a.act V k).unop = h`.

## The adjunction on sheaves

Let `J` be a Grothendieck topology on `T` with `[HasSheafify J (ModuleCat.{w} R)]`.

- `a.inverseImageFunctor R J : (Eᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R)`: the inverse
  image presheaf followed by `presheafToSheaf J`.
- `a.inverseImageAdjunction R J : a.inverseImageFunctor R J ⊣ a.sheafInvariantFunctor R J`:
  the composite of `inverseImagePresheafAdjunction` with `sheafificationAdjunction`.

Let moreover `JE` be a Grothendieck topology on `E` with `[Φ.IsContinuous JE J]`.

- `a.sheafInverseImageFunctor R J JE : Sheaf JE (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R)`:
  `sheafToPresheaf JE` followed by `a.inverseImageFunctor R J`.
- `a.sheafInverseImageAdjunction R J JE`:
  `a.sheafInverseImageFunctor R J JE ⊣ a.sheafInvariantSheafFunctor R J JE`. It is the
  restriction of `inverseImageAdjunction` along the fully faithful functor
  `sheafToPresheaf JE` (`Adjunction.restrictFullyFaithful`), using
  `sheafInvariantSheafFunctorCompIso`.

## Untwisted arrows

Let `C : Type uC` with `[Category.{vC} C]`, `P : MorphismProperty C`, `X : C`, `G : Type uG` a
group, `ρ : G →* Aut X`, `Ψ : E ⥤ P.Over ⊤ X`, and
`a : NaturalAction G (Ψ ⋙ TwistedOver.ι P ρ)`. Several results assume

  `htw : ∀ V k, TwistedOver.Hom.twist (a.act V k).unop = k⁻¹`,

that is, `k` acts by a twisted endomorphism with twist `k⁻¹`. The natural actions of
`AnalyticInvariantPresheaf` satisfy `htw` by `rfl`.

- `twist_inflation_map htw f`: the image under the inflation of `(f, k)` has twist `k⁻¹`.
  Proof: `comp_twist`, `htw` and `ι_map_twist`.
- `a.untwistedArrowsFunctor U`, for an object `U` of `P.Over ⊤ X`:
  `CostructuredArrow Ψ.op (op U) ⥤ CostructuredArrow a.inflation.op (op ((ι P ρ).obj U))`.
  It sends a pair `(V, h)` with `h : U ⟶ Ψ V` over `X` to `((V, ⋆), ι h)`, and a morphism `g`
  to `(g, 1)`, which is a morphism of the target by `inflation_map_sectL`. Simp lemmas
  `untwistedArrowsFunctor_obj`, `untwistedArrowsFunctor_map`.
- `untwistedArrowsFunctor_faithful U` (no `htw` needed).
- `untwistedArrowsFunctor_full htw U`. Let `(f, k)` be a morphism between the images of
  `(V, h)` and `(V', h')`. Then `ι h' ≫ inflation(f, k) = ι h`. Twists are multiplicative,
  `ι h` and `ι h'` have twist `1`, and `inflation(f, k)` has twist `k⁻¹`
  (`twist_inflation_map`). So `k = 1`, `inflation(f, 1) = ι (Ψ.map f)`, and `f` is a morphism
  from `(V, h)` to `(V', h')` by faithfulness of `ι`.
- `untwistedArrowsFunctor_essSurj htw U`. Let `((V, ⋆), h)` be an object of the target, where
  `h : U ⟶ Φ V` has twist `t`. The arrow `h ≫ (a.act V t).unop` has twist `t⁻¹ * t = 1`, so
  it is `ι h₀` for some `h₀ : U ⟶ Ψ V` over `X` (`exists_ι_map_of_twist_eq_one`). The
  isomorphism `(sectAction E G).actIso V t` of `(V, ⋆)` gives an isomorphism from the image
  of `(V, h₀)` to `((V, ⋆), h)` in the comma category (`CostructuredArrow.isoMk`, with
  `inflation_map_sectAction`).
- `untwistedArrowsFunctor_isEquivalence htw U`: from the three results above.

For `R : Type uR` and `[∀ F, a.inflation.op.HasLeftKanExtension F]` as before:

- `a.inverseImagePresheafObjIsoUntwistedColimit htw R Q U`, assuming the pointwise left Kan
  extension of `Prod.fst.op ⋙ Q` and `[HasColimit (CostructuredArrow.proj Ψ.op (op U) ⋙ Q)]`:
  the value of the inverse image of `Q` at `(ι P ρ).obj U` is the colimit of `Q(V)` over
  `CostructuredArrow Ψ.op (op U)`, the dual of the category of the pairs `(V, h : U ⟶ Ψ V)`.
  This is `inverseImagePresheafObjIsoColimit` composed with the inverse of
  `Functor.Final.colimitIso` for the equivalence `untwistedArrowsFunctor U`.

Since `ι P ρ` is the identity on objects, this computes the inverse image presheaf at every
object of `TwistedOver P ρ`. The twisted morphisms of `TwistedOver P ρ`, which are not in the
image of `ι`, give the action of `G` on these values.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers.

- §1.2, printed p.3: "For a morphism `Y(H) → X(G)`, let `C(Y(H)/X(G))` denote the category of
  morphisms `Y(H) → V(G)` over `X(G)`, where `V` is quasi-étale (resp. étale) over `X`. Then
  `ϕ^*F` is the sheaf associated with the presheaf
  `(U'(G') → X'(G')) ↦ ϕ_pF(U'(G')) := lim→ F(V(G))`, where the limit is taken over the dual
  category `C(U'(G')/X(G))°`."
- Proof of Theorem 1.4.2, steps A.4–A.5, printed p.9, uses the functors `b^*` and
  `(b_*F)^G`, with the maps `b^*((b_*F)^G) → F` and `E → (b_*b^*E)^G`. The quotation for
  `(b_*F)^G` is in `NaturalActionSections.md`.

The generic statements here (inflation, adjunctions, comma-category equivalence) are not in
the source.

## Provenance

Derived. The inverse image as a left adjoint of the invariant sections is the standard
construction: a left Kan extension, then sheafification. The inflation along
`E × SingleObj Kᵐᵒᵖ` is introduced here so that the invariant sections become a restriction
followed by invariants on `E × SingleObj Kᵐᵒᵖ` (`inflationInvariantIso`). Those invariants
have the pullback along `Prod.fst` as a left adjoint (`sectPullbackAdjunction`). The
existence of the Kan extensions is a hypothesis of the generic statements. The comparison
with Berkovich's colimit over untwisted arrows is the equivalence of comma categories in the
section "Untwisted arrows", proved here.

Not claimed: that the inverse image of a sheaf is smooth or discrete for any topology on `G`;
that the unit or counit of the adjunctions are isomorphisms; any comparison between the
sheafification on `T` and the sheafification on `P.Over ⊤ X`.
