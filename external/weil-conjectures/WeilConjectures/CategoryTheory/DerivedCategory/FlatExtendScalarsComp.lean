/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatExtendScalars

/-!
# Transitivity of the derived extension of scalars

For flat ring morphisms `f : A →+* B` and `g : B →+* C`, the derived extensions of scalars
satisfy `D(C ⊗_A -) ≅ D(C ⊗_B -) ∘ D(B ⊗_A -)`
(`ModuleCat.derivedExtendScalarsComp`), induced by `ModuleCat.extendScalarsComp`, and these
isomorphisms satisfy the associativity constraint (`ModuleCat.derivedExtendScalarsComp_assoc`),
which follows from the one for modules (`ModuleCat.extendScalars_assoc`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {A B C D : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

section

variable (f : A →+* B) (g : B →+* C) (hf : f.Flat) (hg : g.Flat) (hgf : (g.comp f).Flat)

/-- The transitivity isomorphism `D(C ⊗_A -) ≅ D(C ⊗_B -) ∘ D(B ⊗_A -)`. -/
noncomputable def derivedExtendScalarsComp :
    derivedExtendScalars (g.comp f) hgf ≅ derivedExtendScalars f hf ⋙ derivedExtendScalars g hg :=
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} g) :=
    preservesFiniteLimits_extendScalars_of_flat hg
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} (g.comp f)) :=
    preservesFiniteLimits_extendScalars_of_flat hgf
  Functor.mapDerivedCategoryNatIso (extendScalarsComp.{u + 1, u + 1} f g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

lemma derivedExtendScalarsComp_hom_app_factors (K : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
      preservesFiniteLimits_extendScalars_of_flat hf
    have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} g) :=
      preservesFiniteLimits_extendScalars_of_flat hg
    have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} (g.comp f)) :=
      preservesFiniteLimits_extendScalars_of_flat hgf
    (derivedExtendScalarsComp f g hf hg hgf).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedExtendScalars g hg).map
        ((extendScalars.{u + 1, u + 1, u + 1} f).mapDerivedCategoryFactors.hom.app K) ≫
      (extendScalars.{u + 1, u + 1, u + 1} g).mapDerivedCategoryFactors.hom.app
        (((extendScalars.{u + 1, u + 1, u + 1} f).mapHomologicalComplex _).obj K) =
    (extendScalars.{u + 1, u + 1, u + 1} (g.comp f)).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (extendScalarsComp.{u + 1, u + 1} f g).hom _).app K) := by
  intro _ _ _
  have h := Functor.mapDerivedCategoryCompIso_fac (extendScalars.{u + 1, u + 1, u + 1} f)
    (extendScalars.{u + 1, u + 1, u + 1} g) K
  have h' : DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (extendScalars.{u + 1, u + 1, u + 1} f ⋙ extendScalars.{u + 1, u + 1, u + 1} g))
      (ComplexShape.up ℤ)).hom.app K) = 𝟙 _ := by
    rw [← DerivedCategory.Q.map_id]
    congr 1
  rw [h'] at h
  erw [Category.comp_id] at h
  simp only [derivedExtendScalarsComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  erw [h]
  exact Functor.mapDerivedCategoryNatIso_fac _ K

end

variable (f : A →+* B) (g : B →+* C) (h : C →+* D) (hf : f.Flat) (hg : g.Flat) (hh : h.Flat)
  (hgf : (g.comp f).Flat) (hhg : (h.comp g).Flat) (hhgf : (h.comp (g.comp f)).Flat)

/-- The associativity of the transitivity isomorphisms of the derived extension of scalars. -/
lemma derivedExtendScalarsComp_assoc (X : DerivedCategory (ModuleCat.{u + 1} A)) :
    (derivedExtendScalarsComp f (h.comp g) hf hhg hhgf).hom.app X ≫
      (derivedExtendScalarsComp g h hg hh hhg).hom.app ((derivedExtendScalars f hf).obj X) =
    (derivedExtendScalarsComp (g.comp f) h hgf hh hhgf).hom.app X ≫
      (derivedExtendScalars h hh).map ((derivedExtendScalarsComp f g hf hg hgf).hom.app X) := by
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} g) :=
    preservesFiniteLimits_extendScalars_of_flat hg
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} h) :=
    preservesFiniteLimits_extendScalars_of_flat hh
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} (g.comp f)) :=
    preservesFiniteLimits_extendScalars_of_flat hgf
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} (h.comp g)) :=
    preservesFiniteLimits_extendScalars_of_flat hhg
  have : PreservesFiniteLimits (extendScalars.{u + 1, u + 1, u + 1} (h.comp (g.comp f))) :=
    preservesFiniteLimits_extendScalars_of_flat hhgf
  let τ₁ : derivedExtendScalars (h.comp (g.comp f)) hhgf ⟶
      derivedExtendScalars f hf ⋙ derivedExtendScalars g hg ⋙ derivedExtendScalars h hh :=
    (derivedExtendScalarsComp f (h.comp g) hf hhg hhgf).hom ≫
      Functor.whiskerLeft _ (derivedExtendScalarsComp g h hg hh hhg).hom
  let τ₂ : derivedExtendScalars (h.comp (g.comp f)) hhgf ⟶
      derivedExtendScalars f hf ⋙ derivedExtendScalars g hg ⋙ derivedExtendScalars h hh :=
    (derivedExtendScalarsComp (g.comp f) h hgf hh hhgf).hom ≫
      Functor.whiskerRight (derivedExtendScalarsComp f g hf hg hgf).hom _
  suffices τ₁ = τ₂ from congr_app this X
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) fun K ↦ ?_
  let Ef := extendScalars.{u + 1, u + 1, u + 1} f
  let Eg := extendScalars.{u + 1, u + 1, u + 1} g
  let Eh := extendScalars.{u + 1, u + 1, u + 1} h
  let Ψ := (derivedExtendScalars h hh).map ((derivedExtendScalars g hg).map
      (Ef.mapDerivedCategoryFactors.hom.app K)) ≫
    (derivedExtendScalars h hh).map (Eg.mapDerivedCategoryFactors.hom.app
      ((Ef.mapHomologicalComplex _).obj K)) ≫
    Eh.mapDerivedCategoryFactors.hom.app
      ((Eg.mapHomologicalComplex _).obj ((Ef.mapHomologicalComplex _).obj K))
  have : IsIso Ψ := by dsimp only [Ψ]; infer_instance
  rw [← cancel_mono Ψ]
  have h₁ := derivedExtendScalarsComp_hom_app_factors f (h.comp g) hf hhg hhgf K
  have h₂ := derivedExtendScalarsComp_hom_app_factors g h hg hh hhg
    ((Ef.mapHomologicalComplex _).obj K)
  have h₃ := derivedExtendScalarsComp_hom_app_factors (g.comp f) h hgf hh hhgf K
  have h₄ := derivedExtendScalarsComp_hom_app_factors f g hf hg hgf K
  have n₁ := (derivedExtendScalarsComp g h hg hh hhg).hom.naturality
    (Ef.mapDerivedCategoryFactors.hom.app K)
  dsimp only at h₁ h₂ h₃ h₄
  have n₂ := Eh.mapDerivedCategoryFactors_hom_naturality
    ((NatTrans.mapHomologicalComplex (extendScalarsComp.{u + 1, u + 1} f g).hom
      (ComplexShape.up ℤ)).app K)
  simp only [τ₁, τ₂, Ψ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  have e₁ : (derivedExtendScalarsComp g h hg hh hhg).hom.app
        ((derivedExtendScalars f hf).obj (DerivedCategory.Q.obj K)) ≫
      (derivedExtendScalars h hh).map ((derivedExtendScalars g hg).map
        (Ef.mapDerivedCategoryFactors.hom.app K)) =
      (derivedExtendScalars (h.comp g) hhg).map (Ef.mapDerivedCategoryFactors.hom.app K) ≫
        (derivedExtendScalarsComp g h hg hh hhg).hom.app
          (DerivedCategory.Q.obj ((Ef.mapHomologicalComplex _).obj K)) := n₁.symm
  have e₂ : (derivedExtendScalars h hh).map ((derivedExtendScalarsComp f g hf hg hgf).hom.app
        (DerivedCategory.Q.obj K)) ≫
      (derivedExtendScalars h hh).map ((derivedExtendScalars g hg).map
        (Ef.mapDerivedCategoryFactors.hom.app K)) ≫
      (derivedExtendScalars h hh).map (Eg.mapDerivedCategoryFactors.hom.app
        ((Ef.mapHomologicalComplex _).obj K)) =
      (derivedExtendScalars h hh).map
        ((extendScalars.{u + 1, u + 1, u + 1} (g.comp f)).mapDerivedCategoryFactors.hom.app K) ≫
      (derivedExtendScalars h hh).map (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (extendScalarsComp.{u + 1, u + 1} f g).hom _).app K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, h₄]
  rw [reassoc_of% e₁, h₂, reassoc_of% h₁, reassoc_of% e₂]
  erw [n₂]
  rw [reassoc_of% h₃, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 2
  ext n : 2
  have := congr_app (extendScalars_assoc.{u + 1, u + 1} f g h) (K.X n)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id] at this
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact congr_arg ModuleCat.Hom.hom this.symm

end ModuleCat
