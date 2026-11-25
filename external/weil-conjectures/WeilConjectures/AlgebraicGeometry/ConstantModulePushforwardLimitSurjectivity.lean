/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
import WeilConjectures.AlgebraicGeometry.ConstantModuleLimitFiberDescent
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Surjectivity of the constant-module continuity comparison

Source: Stacks Project, Tag 09Z1, degree zero.
(blueprint: lem-weil-pbc-constant-module-pushforward-limit-surjectivity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The constant-module continuity comparison is an epimorphism.

The arbitrary diagram `K` and cocone `c` are identified with the constant-module
pushforward diagram by `eK`, `hK`, `e` and `hι`. These hypotheses fix the transition
maps and comparison components; they do not assume a colimit property.
Only surjectivity is asserted, not the complementary injectivity assertion.

Source: Stacks Project, Tag 09Z1, degree-zero continuity and its canonical maps;
Tag 09Z6, finite approximation paragraph.
(blueprint: lem-weil-pbc-constant-module-pushforward-limit-surjectivity).

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
4. Use only the surjectivity part of degree-zero continuity. A section on
   an affine etale test object at the limit descends to some stage. Its image
   in the filtered colimit is a preimage under the comparison. For an
   arbitrary etale test object, cover by affine etale objects and do this
   locally. Local lifting of sections makes the abelian comparison epic;
   global lifting on arbitrary test objects is not required.
5. Forgetting coefficients preserves filtered colimits: sheafify the sectionwise
   filtered module colimit, whose underlying group is the filtered group colimit;
   the underlying abelian sheaf of module sheafification is abelian
   sheafification. Thus the underlying comparison is the abelian comparison of
   step 4. The forgetful functor is faithful, so it reflects
   epimorphisms by cancellation of any two maps. Hence the module comparison
   is epic. This argument does not need eventual equality of representatives.
6. Transfer along the final reindexing and the isomorphisms `eK` and `e`.
   Composition with these isomorphisms preserves surjectivity.

Edge cases: a singleton diagram has invertible comparison; for the zero module
or an empty limit scheme the same continuity argument applies. Cofilteredness
excludes an empty index. No finite generation of the ring or module is used. -/
theorem epi_constantModulePushforwardComparison
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
    Epi (colimit.desc K c) := by
  classical
  have _ := @hK
  apply (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale
    X (ModuleCat.{u + 1} Λ)).epi_of_epi_map
  rintro ⟨-, ⟨s⟩⟩
  let T := (X.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  apply (ModuleCat.epi_iff_surjective _).2
  intro x
  obtain ⟨i, y, hy⟩ := exists_constantModule_limit_fiber_rep
    Λ M D p hp ν π hπ hc s ((T.map e.hom) x)
  refine ⟨(T.map (colimit.ι K (op i))) ((T.map (eK (op i)).inv) y), ?_⟩
  apply (ModuleCat.mono_iff_injective (T.map e.hom)).1 inferInstance
  have hcomp : colimit.ι K (op i) ≫ colimit.desc K c ≫ e.hom =
      (eK (op i)).hom ≫ constantModulePushforwardMap Λ M _ _
        (π.app i) (hπ i) := by
    rw [colimit.ι_desc_assoc]
    exact hι (op i)
  have heq := congrArg (fun f => (T.map f) ((T.map (eK (op i)).inv) y)) hcomp
  simp only [Functor.map_comp, ModuleCat.comp_apply] at heq
  have hinv : (T.map (eK (op i)).hom) ((T.map (eK (op i)).inv) y) = y := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.inv_hom_id,
      T.map_id, ModuleCat.id_apply]
  rw [hinv] at heq
  simpa only [Functor.map_comp, ModuleCat.comp_apply] using heq.trans hy

end AlgebraicGeometry.Etale
