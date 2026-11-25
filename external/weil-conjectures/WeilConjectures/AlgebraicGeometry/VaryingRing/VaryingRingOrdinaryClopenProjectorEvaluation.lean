/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryEvaluationComparisons
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryOpenUnit
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# Ordinary realization of the intrinsic clopen projector

Source: Stacks Project, Tags 09AE and 0F7B; Zheng, Construction 4.1.
(blueprint: lem-sp-varying-ring-ordinary-clopen-projector-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

private theorem unit_comparison
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {J₀ : A ⥤ B} {G₀ : B ⥤ A} {J₁ : A' ⥤ B'} {G₁ : B' ⥤ A'}
    (a₀ : J₀ ⊣ G₀) (a₁ : J₁ ⊣ G₁)
    {E : B ⥤ B'} {F : A ⥤ A'} (g : G₀ ⋙ F ≅ E ⋙ G₁) (j : J₀ ⋙ E ≅ F ⋙ J₁)
    (h : mateEquiv a₀ a₁ j.inv = g.hom) (N : A) :
    F.map (a₀.unit.app N) ≫ g.hom.app (J₀.obj N) ≫ G₁.map (j.hom.app N) =
      a₁.unit.app (F.obj N) := by
  have he : (mateEquiv a₀ a₁).symm g.hom = j.inv := by
    rw [← h, Equiv.symm_apply_apply]
  have hu := unit_mateEquiv_symm a₀ a₁ g.hom N
  rw [he] at hu
  dsimp only [Functor.id_obj, Functor.comp_obj] at hu
  rw [← Category.assoc, hu, Category.assoc, ← G₁.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [G₁.map_id, Category.comp_id]

private theorem projector_comparison
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {J₀ : A ⥤ B} {G₀ : B ⥤ A} {J₁ : A' ⥤ B'} {G₁ : B' ⥤ A'}
    (a₀ : J₀ ⊣ G₀) (a₁ : J₁ ⊣ G₁)
    {P₁ : A' ⥤ B'} (d₁ : G₁ ⊣ P₁) (ρ : J₁ ≅ P₁)
    {E : B ⥤ B'} {F : A ⥤ A'} (g : G₀ ⋙ F ≅ E ⋙ G₁) (j : J₀ ⋙ E ≅ F ⋙ J₁)
    (π₀ : 𝟭 B ⟶ G₀ ⋙ J₀) (π₁ : 𝟭 B' ⟶ G₁ ⋙ J₁)
    (h₀ : ∀ M, G₀.map (π₀.app M) = a₀.unit.app (G₀.obj M))
    (h₁ : ∀ M, G₁.map (π₁.app M) = a₁.unit.app (G₁.obj M))
    (hu : ∀ A, F.map (a₀.unit.app A) ≫ g.hom.app (J₀.obj A) ≫
      G₁.map (j.hom.app A) = a₁.unit.app (F.obj A)) (M : B) :
    E.map (π₀.app M) ≫ j.hom.app (G₀.obj M) ≫ J₁.map (g.hom.app M) =
      π₁.app (E.obj M) := by
  have he : G₁.map (E.map (π₀.app M) ≫ j.hom.app (G₀.obj M) ≫
        J₁.map (g.hom.app M)) = G₁.map (π₁.app (E.obj M)) := by
    apply (cancel_epi (g.hom.app M)).1
    simp only [Functor.map_comp, h₁]
    have hn := g.hom.naturality (π₀.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn, h₀, reassoc_of% (hu (G₀.obj M))]
    simpa only [Functor.id_map, Functor.comp_map, Functor.comp_obj] using
      (a₁.unit.naturality (g.hom.app M)).symm
  apply (cancel_mono (ρ.hom.app (G₁.obj (E.obj M)))).1
  apply (d₁.homEquiv (E.obj M) (G₁.obj (E.obj M))).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, he]

private theorem modulePi_image {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Modules R φ X) :
    (pull R φ s).map ((modulePi R φ s).app M) =
      (moduleJAdj R φ s).unit.app ((pull R φ s).obj M) := by
  have hu := moduleJAdj_unit_isIso R φ s
  have ho := moduleOpenToP_isIso R φ s
  let t : Adjunction.Triple (extension R φ s) (pull R φ s) (push R φ s) :=
    ⟨moduleJAdj R φ s, moduleAdj R φ s⟩
  let ff := (moduleJAdj R φ s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have he : moduleOpenToP R φ s = t.leftToRight := by
    ext N
    simp [moduleOpenToP, push, t, Adjunction.Triple.leftToRight]
  simp only [modulePi, NatTrans.comp_app, Functor.whiskerLeft_app,
    NatIso.isIso_inv_app, Functor.map_comp]
  apply (cancel_mono ((pull R φ s).map
    ((moduleOpenToP R φ s).app ((pull R φ s).obj M)))).1
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
  rw [he, t.leftToRight_app_obj, Functor.map_comp]
  change _ = (moduleJAdj R φ s).unit.app _ ≫
    (pull R φ s).map ((moduleJAdj R φ s).counit.app M) ≫ _
  rw [← Category.assoc, (moduleJAdj R φ s).right_triangle_components]
  exact (Category.id_comp _).symm

/-- Ordinary realization preserves the intrinsic projection onto a clopen component.
Source: Stacks 09AE and 0F7B, open case; Zheng, Construction 4.1
(blueprint: lem-sp-varying-ring-ordinary-clopen-projector-evaluation).
Proof: for an adjoint triple J ⊣ G ⊣ P, the intrinsic clopen projection
satisfies G(pi_M) = unit_(G M). This is the triangle identity after cancelling
the invertible canonical J-to-P comparison. Apply it to ordinary systems and
strict towers. Naturality of the ordinary pullback comparison, together with
ordinaryOpen_mate, shows that the image under strict G of the realized
ordinary projection is the strict open unit. Thus its image under G agrees
with that of strict pi. To detect this equality of maps into J(G(E M)), compose
with the invertible J-to-P comparison and transpose under G ⊣ P. The transpose
is G applied to the map followed by the counit, so the two transposes agree.
Injectivity of the adjunction equivalence proves the equation. This argument
requires no complementary-open choice or faithfulness of derived evaluations. -/
theorem ordinaryClopenProjectorEvaluation (n : ℕ) {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Modules R φ X) :
    (ordinaryRealization R φ n X).map ((modulePi R φ s).app M) ≫
        (ordinaryOpenComparison R φ n U X s).hom.app ((pull R φ s).obj M) ≫
        (StrictTower.J (R n) s).map ((ordinaryPullComparison R φ n U X s).hom.app M) =
      (StrictTower.pi (R n) s).app ((ordinaryRealization R φ n X).obj M) := by
  have hi := StrictTower.openToR_isIso (R n) s
  exact projector_comparison (moduleJAdj R φ s) (StrictTower.jAdj (R n) s)
    (StrictTower.adj (R n) s) (asIso (StrictTower.openToR (R n) s))
    (ordinaryPullComparison R φ n U X s) (ordinaryOpenComparison R φ n U X s)
    (modulePi R φ s) (StrictTower.pi (R n) s)
    (modulePi_image R φ s) (StrictTower.pi_image (R n) s)
    (unit_comparison (moduleJAdj R φ s) (StrictTower.jAdj (R n) s)
      (ordinaryPullComparison R φ n U X s) (ordinaryOpenComparison R φ n U X s)
      (ordinaryOpen_mate R φ n s)) M

end AlgebraicGeometry.ProEtale.VaryingRing
