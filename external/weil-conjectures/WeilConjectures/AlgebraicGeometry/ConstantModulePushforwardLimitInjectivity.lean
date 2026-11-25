/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardGermVanishing
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Injectivity of the constant-module continuity comparison

Source: Stacks Project, Tag 09Z1, degree zero.
(blueprint: lem-weil-pbc-constant-module-pushforward-limit-injectivity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The constant-module continuity comparison is a monomorphism.

The arbitrary diagram `K` and cocone `c` are identified with the constant-module
pushforward diagram by `eK`, `hK`, `e` and `hι`. These hypotheses fix the transition
maps and comparison components; they do not assume a colimit property.
Only injectivity is asserted, not the complementary surjectivity assertion.

Source: Stacks Project, Tag 09Z1, degree-zero continuity and its canonical maps;
Tag 09Z6, finite approximation paragraph.
(blueprint: lem-weil-pbc-constant-module-pushforward-limit-injectivity).

Proof:
1. Reindex the opposite of the small cofiltered category by a final functor from
   a nonempty directed partial order (Tag 0032). Its opposite is initial, so the
   restricted scheme cone is limiting. Affineness and qcqs are preserved. Finality
   identifies the colimits of the restricted and original pushforward diagrams.
2. Pull each constant sheaf back to the limit. The constant-sheaf pullback
   comparison identifies it with the same constant sheaf on the limit. The
   identity and composition equations for pullback, including the adjunction
   units, show that transitions become identities. The colimit on the limit is
   the constant sheaf, since the directed category is nonempty and connected.
3. Forget coefficients to abelian sheaves. Constant-sheaf pullback comparisons
   and pushforward commute with this forgetful functor. Apply Tag 09Z1 in degree
   zero: left exactness identifies R^0 of pushforward with ordinary pushforward.
   Under this identification, the higher-direct-image comparison components
   are the adjunction unit, constant-sheaf pullback comparison, and direct-image
   composition comparison. Thus `hK` and `hι` identify the supplied diagrams
   and cocone with the canonical continuity comparison.
4. Use only the injectivity part of degree-zero continuity. On each affine
   etale test object, two representatives with the same image at the limit
   agree after passing to a later stage. Equality in a filtered colimit is
   precisely eventual equality, so the comparison is injective on this basis.
   The affine etale objects cover every etale object; separation for
   sheaves therefore makes the comparison a monomorphism of abelian sheaves.
5. Forgetting coefficients preserves filtered colimits: sheafify the sectionwise
   filtered module colimit, whose underlying group is the filtered group colimit;
   the underlying abelian sheaf of module sheafification is abelian
   sheafification. Thus the underlying comparison is the abelian comparison of
   step 4. The forgetful functor is faithful, so it reflects
   monomorphisms by cancellation of any two maps. Hence the module comparison
   is monic. This argument does not need descent of sections.
6. Transfer along the final reindexing and the isomorphisms `eK` and `e`.
   Composition with these isomorphisms preserves injectivity.

Edge cases: a singleton diagram has invertible comparison; for the zero module
or an empty limit scheme the same continuity argument applies. Cofilteredness
excludes an empty index. No finite generation of the ring or module is used. -/
theorem mono_constantModulePushforwardComparison
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π))
    (K : Iᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eK : ∀ i : Iᵒᵖ, K.obj i ≅
      (lowerStar (ModuleCat.{u + 1} Λ) (p i.unop)).obj
        ((constantSheaf (D.obj i.unop).smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).obj M))
    (hK : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), K.map g =
      (eK i).hom ≫ constantModulePushforwardMap Λ M _ _ (D.map g.unop) (hp g.unop) ≫
        (eK j).inv)
    (c : Cocone K)
    (e : c.pt ≅ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
    (hι : ∀ i : Iᵒᵖ, c.ι.app i ≫ e.hom =
      (eK i).hom ≫ constantModulePushforwardMap Λ M _ _ (π.app i.unop) (hπ i.unop)) :
    Mono (colimit.desc K c) := by
  classical
  have hmono := (Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale X)
    |>.jointlyReflectMonomorphisms (ModuleCat.{u + 1} Λ)
  refine @JointlyReflectMonomorphisms.mono _ _ _ _ _ _ hmono _ _
    (colimit.desc K c) ?_
  rintro ⟨-, ⟨s⟩⟩
  let T := (X.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  apply (ModuleCat.mono_iff_injective _).2
  apply (injective_iff_map_eq_zero (T.map (colimit.desc K c)).hom).2
  intro z hz
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget (ModuleCat.{u + 1} Λ))
  have hC := isColimitOfPreserves (T ⋙ forget (ModuleCat.{u + 1} Λ))
    (colimit.isColimit K)
  obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit hC z
  change (T.map (colimit.ι K i)) x = z at hx
  subst z
  have hzero : (T.map (c.ι.app i)) x = 0 := by
    rw [← ConcreteCategory.comp_apply, ← T.map_comp, colimit.ι_desc] at hz
    exact hz
  have hcanonical : T.map
      (constantModulePushforwardMap Λ M (p i.unop) ν
        (π.app i.unop) (hπ i.unop)) ((T.map (eK i).hom) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← T.map_comp, ← hι i,
      T.map_comp, ConcreteCategory.comp_apply, hzero, map_zero]
  obtain ⟨j, g, hg⟩ := exists_constantModulePushforward_germ_eq_zero
    Λ M D p hp ν π hπ hc s i.unop ((T.map (eK i).hom) x) hcanonical
  have htransition : (T.map (K.map g.op)) x = 0 := by
    rw [hK, T.map_comp, T.map_comp]
    simp only [ConcreteCategory.comp_apply]
    change (T.map (eK (op j)).inv)
      ((T.map (constantModulePushforwardMap Λ M (p i.unop) (p j)
        (D.map g) (hp g))) ((T.map (eK i).hom) x)) = 0
    rw [hg, map_zero]
  calc
    (T.map (colimit.ι K i)) x =
        (T.map (colimit.ι K (op j))) ((T.map (K.map g.op)) x) := by
      rw [← ConcreteCategory.comp_apply, ← T.map_comp, colimit.w]
    _ = 0 := by rw [htransition, map_zero]

end AlgebraicGeometry.Etale
