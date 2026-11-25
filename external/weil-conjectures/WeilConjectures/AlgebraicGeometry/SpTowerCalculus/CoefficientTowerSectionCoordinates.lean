/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian

/-! # Section-normalized strict tower coordinates

Source: blueprint Local pairs and Levels, coefficient tower shriek calculus.
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem evaluation_sections (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.obj U)
      (((spCoefficientEvaluation l E T D.equivalence n).obj M).val.obj U) := by
  dsimp [SpTowerShriek.ev, SemilinearSections.evaluation, SheafOfModules.pushforward,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj,
    spCoefficientEvaluation, systemEvaluation]
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app, eqToHom_refl]
  exact (b.sections T M n U).trans (D.sections M n U).symm

private theorem hom_function_heq {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {g : M' ⟶ N'} (hfg : HEq f g) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  cases hM
  cases hN
  cases hfg
  rfl

-- Comparing the two concrete ring-presheaf presentations requires unfolding their objects.
private theorem evaluation_restrictions (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.map f x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).obj M).val.map f x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.obj M).val.map
      (Prod.mkHom (𝟙 n) f.unop).op x)
    (fun x ↦ ((D.equivalence.functor.obj M).level n).val.map f x)
  have hB := b.restrictions T M (Prod.mkHom (𝟙 n) f.unop).op
  have hD := D.restrictions M n f
  refine hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm)) ?_
    (hB.trans hD.symm)
  have hmap :
      ((SemilinearSections.ring (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj.map
            (Prod.mkHom (𝟙 n) f.unop).op).hom =
      ((spCoefficientRing l E T n).obj.map f).hom := by
    change ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((((SemilinearSections.rings (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (𝟙 (op n))).hom.app U) ≫
          (SpTowerShriek.B l E T n).obj.map f)).hom =
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((SpTowerShriek.B l E T n).obj.map f)).hom
    erw [CategoryTheory.Functor.map_id]
    simp
  rw [hmap]
  exact congrArg (ModuleCat.restrictScalars
    (((spCoefficientRing l E T n).obj).map f).hom).obj
    (eq_of_heq ((b.sections T M n V).trans (D.sections M n V).symm))

-- Evaluation changes scalar actions but leaves these underlying section functions intact.
private theorem evaluation_maps (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    {M N : spCoefficientTowers l E T} (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦
      ((SpTowerShriek.ev l E T n).map ((b.realization T).functor.map f)).val.app U x)
      (fun x ↦ ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U x) := by
  change HEq
    (fun x ↦ ((b.realization T).functor.map f).val.app (op (n, U.unop)) x)
    (fun x ↦ ((D.equivalence.functor.map f).app n).val.app U x)
  exact hom_function_heq
    (eq_of_heq ((b.sections T M n U).trans (D.sections M n U).symm))
    (eq_of_heq ((b.sections T N n U).trans (D.sections N n U).symm))
    ((b.morphisms T f (op (n, U.unop))).trans (D.morphisms f n U).symm)

private theorem transport_restriction {A B : Type*} [Ring A] [Ring B]
    (q : A →+* B) {M M' : ModuleCat A} {N N' : ModuleCat B}
    (hM : M = M') (hN : N = N')
    (f : M ⟶ (ModuleCat.restrictScalars q).obj N)
    (g : M' ⟶ (ModuleCat.restrictScalars q).obj N')
    (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ (ModuleCat.restrictScalars q).map (eqToHom hN) = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private theorem transport_morphism {R : Type*} [Ring R]
    {M M' N N' : ModuleCat R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (hfg : HEq (fun x ↦ f x) (fun x ↦ g x)) :
    f ≫ eqToHom hN = eqToHom hM ≫ g := by
  cases hM
  cases hN
  ext x
  exact congrFun (eq_of_heq hfg) x

private def evaluation_object (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) :
    (SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M) ≅
      (spCoefficientEvaluation l E T D.equivalence n).obj M where
  hom := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U))
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D M n V)) _ _
      (evaluation_restrictions l E b T D M n f) }⟩
  inv := ⟨{
    app := fun U ↦ eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm
    naturality := fun {U V} f ↦ transport_restriction _
      (eq_of_heq (evaluation_sections l E b T D M n U)).symm
      (eq_of_heq (evaluation_sections l E b T D M n V)).symm _ _
      (evaluation_restrictions l E b T D M n f).symm }⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)).symm ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]

private def evaluation_iso (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (b.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T D.equivalence n :=
  NatIso.ofComponents (fun M ↦ evaluation_object l E b T D M n) (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    change ((SpTowerShriek.ev l E T n).map
        ((b.realization T).functor.map f)).val.app U ≫
      eqToHom (eq_of_heq (evaluation_sections l E b T D N n U)) =
      eqToHom (eq_of_heq (evaluation_sections l E b T D M n U)) ≫
        ((spCoefficientEvaluation l E T D.equivalence n).map f).val.app U
    exact transport_morphism
      (eq_of_heq (evaluation_sections l E b T D M n U))
      (eq_of_heq (evaluation_sections l E b T D N n U)) _ _
      (evaluation_maps l E b T D f n U))

private def quotientDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (SpTowerShriek.R l E n.unop)
  map f := CommRingCat.ofHom (quotient l E (leOfHom f.unop))
  map_id n := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

end AlgebraicGeometry.ProEtale.SpTowerCalculus

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
