/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

universe w uA vA

open CategoryTheory

namespace CategoryTheory

private theorem injective_single_from_upper_eq_zero
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (I : A) [Injective I] (E : DerivedCategory A) [E.IsGE 1]
    (f : E ⟶ (DerivedCategory.singleFunctor A 0).obj I) : f = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E 1
  have := hK
  have h : e.inv ≫ f = 0 :=
    DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective (e.inv ≫ f) 1 (by omega)
  simpa using (cancel_epi e.inv).1 (by simpa using h)

/-- Injectivity half of the injective-target derived homology comparison.

Source: proof step 1 of `new-stage3-derived-homology-injective-bijective`.
Proof: if a chain map into the injective complex concentrated in degree zero
induces zero on degree-zero homology, its degree-zero component factors through
the image of the preceding differential; injectivity extends this factor to a
null homotopy. Transporting across the derived localization gives equality of
the original morphisms. The statement is isolated as the injectivity half.

(auxiliary; not a blueprint node) -/
theorem derived_homology_injective_injective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (I : A) [Injective I] :
    Function.Injective
      ((DerivedCategory.homologyFunctor A 0).map :
        (K ⟶ (DerivedCategory.singleFunctor A 0).obj I) →
        ((DerivedCategory.homologyFunctor A 0).obj K ⟶
          (DerivedCategory.homologyFunctor A 0).obj
            ((DerivedCategory.singleFunctor A 0).obj I))) := by
  let ts := DerivedCategory.TStructure.t (C := A)
  let S := (DerivedCategory.singleFunctor A 0).obj I
  let T := (ts.triangleLTGE 1).obj K
  have hT := ts.triangleLTGE_distinguished 1 K
  have : ts.IsGE T.obj₃ 1 := by
    change ts.IsGE ((ts.truncGE 1).obj K) 1
    infer_instance
  have hv (f : T.obj₃ ⟶ S) : f = 0 := injective_single_from_upper_eq_zero I _ f
  have hpre : Function.Injective (fun f : K ⟶ S ↦ T.mor₁ ≫ f) := by
    intro f g h
    obtain ⟨a, ha⟩ := T.yoneda_exact₂ hT (f - g) (by simp [h])
    rw [hv a, Limits.comp_zero] at ha
    exact sub_eq_zero.mp ha
  have : ts.IsLE T.obj₁ 0 := ts.isLE_truncLT_obj K 1 0 (by omega)
  let H := DerivedCategory.homologyFunctor A 0
  have hH : Function.Injective (fun f : T.obj₁ ⟶ S ↦ H.map f) :=
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).1
  intro f g h
  apply hpre
  apply hH
  simpa only [Functor.map_comp] using congrArg (fun a ↦ H.map T.mor₁ ≫ a) h

end CategoryTheory
