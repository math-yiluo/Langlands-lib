/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement

/-! # Differential compatibility for normalized Hom degree maps

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option backward.isDefEq.respectTransparency true
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

open scoped ChangeOfRings

namespace CategoryTheory

-- Use the projection API without unfolding the chosen bifunctor.
attribute [local irreducible] homComplexFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem pure_linear_ext
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    {N : Type u} [AddCommGroup N] [Module B N]
    (f g : (F.obj M).val.obj U →ₗ[B] N)
    (ht : ∀ b x, f (ringExtensionPure φ F h M U b x) =
      g (ringExtensionPure φ F h M U b x)) : f = g := by
  let : Module A B := Module.compHom B φ
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) M
  let η := toSheafify ⊥ T.presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  let α := (eqToHom (h M).symm).val.app U
  have : IsIso α := by
    change IsIso ((SheafOfModules.evaluation _ _).map (eqToHom (h M).symm))
    infer_instance
  have hs := (ConcreteCategory.bijective_of_isIso α).2.comp
    (ConcreteCategory.bijective_of_isIso (η.app U)).2
  ext z
  obtain ⟨z, rfl⟩ := hs z
  induction z using TensorProduct.inductionOn with
  | tmul b x => exact ht b x
  | add z w hz hw => simpa only [Function.comp_apply, map_add] using congrArg₂ (· + ·) hz hw

set_option backward.isDefEq.respectTransparency false in
private theorem pure_hom_ext
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) {N : RingSiteModules B} (f g : F.obj M ⟶ N)
    (ht : ∀ U b x, f.val.app U (ringExtensionPure φ F h M U b x) =
      g.val.app U (ringExtensionPure φ F h M U b x)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact pure_linear_ext φ F h M U (f.val.app U).hom (g.val.app U).hom (ht U)

set_option backward.isDefEq.respectTransparency false

private abbrev HomProjection {A : Type u} [CommRing A]
    (P Q H : CochainComplex (RingSiteModules A) ℤ) :=
  ∀ (n p q : ℤ) (_hpq : p + n = q), H.X n ⟶
    SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) (P.X p) (Q.X q)

private structure HomPresentation {A : Type u} [CommRing A]
    (P Q H : CochainComplex (RingSiteModules A) ℤ) (projection : HomProjection P Q H) :
    Prop where
  isLimit : ∀ n, Nonempty (IsLimit (Fan.mk (H.X n)
    (fun p : ℤ ↦ projection n p (p + n) rfl)))
  differential : ∀ (n m p q q' p' : ℤ), n + 1 = m →
    ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
    H.d n m ≫ projection m p q hpq =
      projection n p q' hq' ≫
        SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
          (𝟙 (P.X p)) (Q.d q' q) -
      n.negOnePow • (projection n p' q hp' ≫
        SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
          (P.d p p') (𝟙 (Q.X q)))

-- Evaluation depends only on the projection data, never its large specification proof.
private abbrev CanonicalProjection {A : Type u} [CommRing A]
    (P Q H : CochainComplex (RingSiteModules A) ℤ) :=
  ∀ n p : ℤ, H.X n ⟶ SheafOfModules.homObj
    (R := CochainComplex.onePointRingSheaf A) (P.X p) (Q.X (p + n))

private noncomputable def fullProjection {A : Type u} [CommRing A]
    {P Q H : CochainComplex (RingSiteModules A) ℤ} (π : CanonicalProjection P Q H) :
    HomProjection P Q H := fun n p _q hpq ↦ hpq ▸ π n p

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] ringExtensionPure

-- The two tensor inductions and internal-Hom extensionality need this elaboration budget.
private theorem canonicalPresentation {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) :
    HomPresentation P Q (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)
      (fullProjection (ringHomComplexProjection P Q)) := by
  let π := (homComplex_projections_exists
    (R := CochainComplex.onePointRingSheaf A)).choose P Q
  have hπ (n p q : ℤ) (hpq : p + n = q) :
      fullProjection (ringHomComplexProjection P Q) n p q hpq = π n p q hpq := by
    subst q
    rfl
  constructor
  · exact (homComplex_projections_exists
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.1 P Q
  · intro n m p q q' p' hnm hpq hq' hp'
    rw [hπ, hπ, hπ]
    exact (homComplex_projections_exists
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.2.1
      P Q n m p q q' p' hnm hpq hq' hp'

end CategoryTheory
