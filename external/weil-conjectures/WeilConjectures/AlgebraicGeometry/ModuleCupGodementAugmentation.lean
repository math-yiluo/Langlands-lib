/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
private theorem unit_naturality (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) :
    moduleCup_godementUnit X F ≫ moduleCup_godementMap X f =
      f ≫ moduleCup_godementUnit X G := by
  apply Pi.hom_ext
  intro x
  simp only [moduleCup_godementMap, moduleCup_godementUnit, Category.assoc, Pi.lift_comp_π]
  rw [Pi.lift_comp_π_assoc]
  refine hom_ext _ _ fun V ↦ ?_
  ext p
  refine SkyscraperSections.ext fun hx ↦ ?_
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  change f.stalkLinearMap x
      (skyscraperStalkEval x (F.presheaf.stalk x)
        ((skyscraper x (F.presheaf.stalk x)).presheaf.germ V x hx
          ((toSkyscraper (LinearMap.id :
            F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x)).app V p))) =
    G.presheaf.germ V x hx (f.app V p)
  rw [skyscraperStalkEval_germ, toSkyscraper_app_apply, LinearMap.id_apply,
    Hom.stalkLinearMap_germ]

/-- The germ in degree zero extends to the required cochain augmentation.
Source: Stacks Project, Tag 0FKR; Banerjee, arXiv:1004.1491, §1.1.4.
(blueprint: lem-sc-module-cup-godement-augmentation-exists)
Proof: the two degree-zero cofaces are the two composites of the unit with
itself and with the endofunctorial image of the unit. Naturality of the unit
makes them equal, so the germ has zero composite with the first alternating
differential. The universal constructor for maps from a complex concentrated
in degree zero then supplies the augmentation; extension by zero transports
it to integer degrees. The displayed identity follows from the degree-zero
component of that constructor and the single-object isomorphism. -/
theorem moduleCup_godement_augmentation_exists (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (h : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1))
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)),
      eqToHom (h n) ≫ moduleCup_godementInsert X F (n + 1) i =
        A.map (SimplexCategory.δ i) ≫ eqToHom (h (n + 1))) :
    ∃ a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        (((alternatingCofaceMapComplex X.Modules).obj A).extend
          ComplexShape.embeddingUpNat),
      ModuleCupGodementModel X F A a := by
  let C := (alternatingCofaceMapComplex X.Modules).obj A
  let e := ComplexShape.embeddingUpNat
  let g : F ⟶ C.X 0 := moduleCup_godementUnit X F ≫ (eqToIso (h 0)).inv
  have hg : g ≫ C.d 0 1 = 0 := by
    have hc (i : Fin 2) :
        g ≫ A.map (SimplexCategory.δ i) ≫ eqToHom (h 1) =
          moduleCup_godementUnit X F ≫ moduleCup_godementInsert X F 1 i := by
      dsimp [g]
      simp only [Category.assoc]
      rw [← hδ 0 i]
      simp
    have hi : moduleCup_godementUnit X F ≫ moduleCup_godementInsert X F 1 0 =
        moduleCup_godementUnit X F ≫ moduleCup_godementInsert X F 1 1 := by
      simpa [moduleCup_godementInsert, moduleCup_godementIterate] using
        (unit_naturality X (moduleCup_godementUnit X F)).symm
    have hd : g ≫ A.map (SimplexCategory.δ (0 : Fin 2)) =
        g ≫ A.map (SimplexCategory.δ (1 : Fin 2)) := by
      apply (cancel_mono (eqToHom (h 1))).mp
      simpa only [Category.assoc] using (hc 0).trans (hi.trans (hc 1).symm)
    change g ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD A 0 = 0
    simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two,
      CosimplicialObject.δ, Preadditive.comp_add, Preadditive.comp_neg, hd]
  let φ : F ⟶ (C.extend e).X 0 := g ≫ (C.extendXIso e (i := 0) rfl).inv
  have hφ : ∀ k : ℤ, (ComplexShape.up ℤ).Rel 0 k → φ ≫ (C.extend e).d 0 k = 0 := by
    intro k hk
    have hk' : k = 1 := by simpa using hk.symm
    subst k
    change φ ≫ (C.extend e).d 0 1 = 0
    rw [C.extend_d_eq e (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl]
    simp only [φ, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hg, zero_comp]
  refine ⟨HomologicalComplex.mkHomFromSingle φ hφ, h, hδ, ?_⟩
  dsimp only [C, e, φ, g]
  simp [HomologicalComplex.mkHomFromSingle_f, Category.assoc]

end
end AlgebraicGeometry.Scheme.Modules
