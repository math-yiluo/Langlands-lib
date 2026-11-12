# The twisted category over an object with a group action

Author: Worker 26. Uses Mathlib's comma categories cut out by morphism
properties (`MorphismProperty.Over`), its Grothendieck topologies, cocontinuous
and continuous functors, and the published local action systems of
`Langlands.Sheaf.Equivariant.LocalAction` (Worker 13).

## Purpose

Let a group `G` act on an object `X` of a category `C`. An object `U ⟶ X` of a
site over `X`, such as the étale site, has no endomorphisms over `X` that cover
a nontrivial automorphism of `X`. So the action of an element `h` on `U`, lifting
the action of `h` on `X`, is not an endomorphism of `U` in the site over `X`. This
module builds the category in which such lifts are endomorphisms: the twisted
category. Sheaves on it, for the induced topology, are sheaves over `X` with the
structure of an equivariant sheaf for `G` with the discrete topology. Local
actions in the sense of `LocalAction` on this category can then lift the action
of `G`.

## Data and conventions

- `C : Type u` with `Category.{v} C`, a morphism property `P` of `C`, an object
  `X : C`, a group `G : Type uG`, and `ρ : G →* Aut X`. In Mathlib,
  `ρ (g * g')` has underlying morphism `(ρ g').hom ≫ (ρ g).hom`, so `ρ` is a
  left action (`rho_mul_hom`). `rho_one_hom`, `rho_inv_hom_hom`,
  `rho_hom_inv_hom` are the unit and inverse laws on underlying morphisms.
- Objects: `TwistedOver P ρ` is a one-field structure wrapping an object of
  `P.Over ⊤ X`, that is, an arrow `U.hom : U.left ⟶ X` with `P U.hom`.
  `TwistedOver.hom U : U.obj.left ⟶ X` is its structure map (an abbreviation
  with codomain written `X`). `hom_comp_rho_hom_inv`:
  `(U.hom ≫ (ρ g).hom) ≫ (ρ g⁻¹).hom = U.hom`.
- Morphisms: `TwistedOver.Hom U V` has a group element `twist`, an arrow
  `left : U.obj.left ⟶ V.obj.left`, and the condition
  `left ≫ V.hom = U.hom ≫ (ρ twist).hom`: the arrow covers the action of
  `twist` on `X`. The identity has twist `1` and arrow `𝟙`. The composite of
  `f : U ⟶ V` and `g : V ⟶ W` has twist `g.twist * f.twist` and arrow
  `f.left ≫ g.left`. This is the instance `TwistedOver.category`, with morphisms
  in `Type (max v uG)`. `hom_ext` (equal twists and equal arrows give equal
  morphisms), `homMk`, and the simp lemmas `id_twist`, `id_left`, `comp_twist`,
  `comp_left`, `homMk_twist`, `homMk_left` record these formulas.

## The inclusion and translations

- `ι P ρ : P.Over ⊤ X ⥤ TwistedOver P ρ` is the identity on objects and sends a
  morphism over `X` to the morphism with twist `1` and the same arrow
  (`ι_map_twist`, `ι_map_left`). It is faithful.
  `exists_ι_map_of_twist_eq_one`: a twisted morphism between objects of the
  image with twist `1` is the image of a morphism over `X`. `ι` is declared
  reducible, so `(ι P ρ).obj U` is syntactically the wrapped `U` for rewriting.
- With `[P.RespectsIso]`: `translate P ρ g : P.Over ⊤ X ⥤ P.Over ⊤ X` is
  Mathlib's `MorphismProperty.Comma.mapRightIso` along `ρ g`, viewed as an
  automorphism of the constant functor at `X`. It sends `U` to `gU`, with the
  same source and structure map `U.hom ≫ (ρ g).hom`, and keeps the arrows
  (`translate_obj_left`, `translate_obj_hom`, `translate_map_left`,
  `hom_translate`). For a space with a left action of `G`, `gU` is isomorphic
  over `X` to Berkovich's `gU = U ×_{X, g⁻¹} X`.
- `relabel ρ g U : (ι P ρ).obj U ⟶ (ι P ρ).obj (gU)` has twist `g` and arrow
  `𝟙 U.left` (`relabel_twist`, `relabel_left`). It is an isomorphism with
  inverse `relabelInv ρ g U` (twist `g⁻¹`, arrow `𝟙`). `ι_map_comp_relabel`:
  relabelling is natural in `U` for morphisms over `X`.
- `untwist g f hf`: for a twisted morphism `f : (ι P ρ).obj U ⟶ (ι P ρ).obj V`
  with `hf : twist f = g`, the morphism `gU ⟶ V` over `X` with arrow
  `f.left` (`untwist_left`). `relabel_comp_ι_map_untwist`:
  `relabel ρ g U ≫ (ι P ρ).map (untwist g f hf) = f`. So every twisted morphism
  is a relabelling followed by a morphism over `X`.

A presheaf `F` on the twisted category therefore consists of the presheaf
`(ι P ρ).op ⋙ F` on `P.Over ⊤ X` and the bijections
`F.map (relabel ρ g U).op : F(gU) ⟶ F(U)`, natural in `U`, with
`relabel ρ (g * g') U` equal to `relabel ρ g' U ≫ relabel ρ g (g'U)` up to the
identification of `g(g'U)` with `(gg')U`. This is the data of an equivariant
presheaf in Berkovich's sense for `G` with the discrete topology. The
equivalence between the two descriptions is not formalized here.

## The twisted topology

Assume `[P.RespectsIso]` and let `J` be a Grothendieck topology on
`P.Over ⊤ X`.

- `IsTranslationInvariant J` (with `ρ` implicit) is a class with one field:
  every `translate P ρ g` is cocontinuous from `J` to `J`, i.e. for a covering
  sieve `S` of `gU`, the sieve of arrows `k : W ⟶ U` with
  `(translate P ρ g).map k ∈ S` covers `U`.
- `twistedTopology ρ J`: a sieve `S` on an object `U` of the twisted category
  covers when `S.functorPullback (ι P ρ)`, its sieve of arrows over `X`, is a
  `J`-covering sieve of `U.obj` (`mem_twistedTopology_iff`). The maximal sieve
  covers. Transitivity follows from that of `J` and
  `Sieve.functorPullback_pullback`. For stability under pullback along a
  twisted morphism `f` with twist `g`, write `f` as a relabelling followed by
  `untwist g f rfl`. Pull the covering sieve back along `untwist g f rfl`, a
  `J`-covering sieve of `gV`. By invariance its preimage under `translate P ρ g`
  covers `V`. Each of its arrows `k` satisfies `(ι P ρ).map k ≫ f ∈ S`, by
  naturality of relabelling and the downward closure of `S`.
- With `[IsTranslationInvariant J]`:
  - `ι P ρ` is cocontinuous from `J` to `twistedTopology ρ J` (this is the
    definition) and cover preserving (`ι_coverPreserving`).
  - `ι_compatiblePreserving K`, for any topology `K` on the twisted category:
    let `f₁ ≫ ι g₁ = f₂ ≫ ι g₂` with `g₁, g₂` in a presieve. Then `f₁` and
    `f₂` have the same twist, both factor as the same relabelling followed by
    arrows over `X`, and these arrows composed with `g₁`, `g₂` agree. So
    compatibility over `X` gives compatibility in the twisted category.
  - Hence `ι P ρ` is continuous (Mathlib's
    `Functor.isContinuous_of_coverPreserving`), and `restriction ρ J A` is the
    functor `Sheaf (twistedTopology ρ J) A ⥤ Sheaf J A` restricting along `ι`.
  - `isSheaf_of_isSheaf_comp`: a presheaf of types on the twisted category
    whose restriction along `ι` is a `J`-sheaf is a sheaf for the twisted
    topology. A compatible family on a covering sieve `S` restricts to a
    compatible family on the arrows of `S` over `X` and has an amalgamation
    there. A twisted arrow `f` of `S` is `relabel ≫ ι (untwist f)`, and
    `ι (untwist f)` lies in `S` because `relabel` is invertible. Compatibility
    of the family then shows that the amalgamation also works at `f`.
    Uniqueness is checked on the arrows over `X`.
  - `isSheaf_iff_isSheaf_comp`: for any coefficient category `A`, a presheaf on
    the twisted category is a sheaf for `twistedTopology ρ J` exactly when its
    restriction along `ι` is a `J`-sheaf. So sheaves on the twisted site are
    `J`-sheaves with an equivariant structure.

## Lifts of the action

- `IsLift a`, for `a : H →* (End U)ᵐᵒᵖ` with `H : Subgroup G`: every `h` acts by
  a twisted endomorphism with twist `h⁻¹`. The action of `h` on sections of a
  presheaf `F` is `F.map (a h).unop.op` (as in `localRepresentation`), a left
  action. By `relabel_comp_ι_map_untwist`, `(a h).unop` is `relabel ρ h⁻¹ U`
  followed by a morphism `h⁻¹U ⟶ U` over `X`.
- `LocalActionSystem.IsLiftSystem L`, for `[TopologicalSpace G]` and
  `L : LocalActionSystem (TwistedOver P ρ) G`: every admissible local action of
  `L` is a lift.
- With `[P.ContainsIdentities]`: `base P ρ` is `X` with structure map `𝟙 X`
  (`base_obj_left`, `hom_base`). `baseEndo g` is its twisted endomorphism with
  twist `g` and arrow `(ρ g).hom` (`baseEndo_twist`, `baseEndo_left`), with
  `baseEndo_mul` and `baseEndo_one`. `baseAction P ρ : G →* (End (base P ρ))ᵐᵒᵖ`
  sends `g` to `baseEndo g⁻¹` (`baseAction_apply`). `isLift_baseAction`: its
  restriction to `⊤ : Subgroup G` is a lift. Sections over `base P ρ` thus carry
  an action of all of `G`; no smoothness is claimed.

## Provenance and scope

Derived infrastructure. Source, read in the original by Worker 26: Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), §1.4, printed p.7 = PDF p.7. For `G` discrete, a quasi-étale
(resp. étale) `G`-sheaf `F` is endowed with "a system of isomorphisms
`τ(g) : F ⥲ g^*F`, `g ∈ G`, such that `τ(gh) = h^*(τ(g)) ∘ τ(h)`", with the
inverse images `g^*`. Equivalently, for each `U → X` and `g ∈ G` there is a
functorial bijection `F(U) ⥲ F(ᵍU)`, `f ↦ ᵍf`, where `ᵍU = U ×_{X, g⁻¹} X`,
such that `ᵍʰf = ᵍ(ʰf)`. For a subgroup `H` and `U(H) → X(G)`, `h ∈ H` acts on
`F(U)` by `hf = σ(h)(ʰf)`, where `σ(h) : F(ʰU) ⥲ F(U)` is induced by the
isomorphism `U ⥲ ʰU` over `X` given by `h⁻¹ : U → U`. In this module `ᵍU` is
written `gU`. The same page defines `G`-sheaves for topological `G`
(Definition 1.4.1) as `G^d`-sheaves with discreteness conditions; that
condition is the subject of `LocalActionDiscretePart`.

Correspondence. The twisted category is a strict model of the Grothendieck
construction of `G` acting on `P.Over ⊤ X` by translation. Its presheaves carry
the bijections `F(gU) ≅ F(U)` and the cocycle law above, through the
relabelling isomorphisms. The twist convention `h⁻¹` in `IsLift` matches
Berkovich's formula: the twisted endomorphism with twist `h⁻¹` and arrow the
action of `h⁻¹` on `U` is the morphism `U ⟶ hU` over `X` with arrow `h⁻¹`,
followed by `relabelInv ρ h U`. Applying `F`, the composite is `σ(h)` after the
bijection `f ↦ ʰf : F(U) ⥲ F(ʰU)` given by `relabelInv ρ h U`. This
factorization is immediate from the definitions; it is not stated as a separate
lemma. The base action gives the usual left action `g · s = (g⁻¹)^* s` on global
sections.

Differences: the module uses translation by `U ↦ (U, U.hom ≫ ρ g)` in place of
the fibre product, and an arbitrary category `C`, morphism
property `P` and topology `J` in place of analytic spaces, quasi-étale or étale
morphisms and their topologies. It does not construct analytic sites, the
canonical actions given by Berkovich's Key Lemma, or an instance of
`IsTranslationInvariant`. These belong to the analytic specialization (Task
21 builds the analytic étale site). The class `IsTranslationInvariant` and the
twisted topology are formalization choices. The criterion
`isSheaf_iff_isSheaf_comp`, proved here, shows that the sheaves for the twisted
topology are exactly the presheaves on the twisted category whose underlying
presheaf over `X` is a `J`-sheaf.

Universes: `C : Type u` with `Category.{v} C`, `G : Type uG`; morphisms of the
twisted category in `Type (max v uG)`; `ι_compatiblePreserving` is stated for
sheaves of types in an arbitrary universe `w`, and `isSheaf_of_isSheaf_comp`
for presheaves of types in `Type w`.

Source registration: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
