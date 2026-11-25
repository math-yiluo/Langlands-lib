/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # Ordinary normalization of the quotient section tensor comparison

## References

* Stacks 03EK, 03EL and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

open PresheafOfModules in
private theorem scalar_element_eq (T : Scheme.{u})
    (c : ScalarSectionData a T) (M : modules Λ T) (W : T.ProEtᵒᵖ)
    (m : M.val.obj W) (s : (ring Λ' T).obj.obj W) :
    sectionScalarElement a T c M W m s =
      (eqToHom (c.model.obj_eq M).symm).val.app W
        (SheafOfModules.scalarExtensionConstraintTmul (sectionQuotient a T) M W m s) := by
  unfold sectionScalarElement
  apply congrArg ((eqToHom (c.model.obj_eq M).symm).val.app W)
  symm
  unfold SheafOfModules.scalarExtensionConstraintTmul
  let RS : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ' T)
  have h := toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u, u + 1, u + 1}
    (C := T.ProEt) (J := Scheme.ProEt.topology T) (R := RS) (𝟙 RS.obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (sectionQuotient a T) M)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h W) _

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem pure_cast (T : Scheme.{u})
    {M N M' N' : modules Λ' T} (hM : M = M') (hN : N = N')
    (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    (eqToHom hM ⊗ₘ eqToHom hN).val.app W (sectionPureTensor Λ' T M N W m n) =
      sectionPureTensor Λ' T M' N' W
        ((eqToHom hM).val.app W m) ((eqToHom hN).val.app W n) := by
  subst M' N'
  simp

/-- The underlying section comparison has the prescribed pure-tensor formula. -/
theorem section_tensor_transport_normalized_pure (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) :
    ∃ e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
        (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
          (curriedTensor (modules Λ' T)),
      ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W)
        (s : (ring Λ' T).obj.obj W),
        (((e.app M).app N).val.app W)
            (sectionScalarElement a T c (M ⊗ N) W
              (sectionPureTensor Λ T M N W m n) s) =
          sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
            (sectionScalarElement a T c M W m 1)
            (sectionScalarElement a T c N W n s) := by
  have _ := hc
  have _ := hb
  have _ := barB
  obtain ⟨d⟩ := SheafOfModules.scalarExtension_constraint_coherence
    (ring Λ T) (ring Λ' T) (sectionQuotient a T)
  let q (M N : modules Λ T) : c.model.E.obj (M ⊗ N) ⟶
      c.model.E.obj M ⊗ c.model.E.obj N :=
    eqToHom (c.model.obj_eq (M ⊗ N)) ≫ (d.tensorIso M N).hom ≫
      (eqToHom (c.model.obj_eq M).symm ⊗ₘ eqToHom (c.model.obj_eq N).symm)
  have hq (M N M' N' : modules Λ T) (f : M ⟶ M') (g : N ⟶ N') :
      c.model.E.map (f ⊗ₘ g) ≫ q M' N' =
        q M N ≫ (c.model.E.map f ⊗ₘ c.model.E.map g) := by
    simp only [q, c.model.map_eq, Category.assoc, ← tensorHom_comp_tensorHom,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simpa only [Category.assoc, tensorHom_comp_tensorHom, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp] using
      congrArg (fun z ↦ eqToHom (c.model.obj_eq (M ⊗ N)) ≫ z ≫
        (eqToHom (c.model.obj_eq M').symm ⊗ₘ eqToHom (c.model.obj_eq N').symm))
        (d.natural M N M' N' f g)
  let e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
      (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
        (curriedTensor (modules Λ' T)) :=
    { app := fun M ↦
        { app := fun N ↦ q M N
          naturality := by
            intro N N' g
            change c.model.E.map (M ◁ g) ≫ q M N' =
              q M N ≫ (c.model.E.obj M ◁ c.model.E.map g)
            have h := hq M N M N' (𝟙 M) g
            rw [c.model.E.map_id] at h
            simpa only [id_tensorHom] using h }
      naturality := by
        intro M M' f
        apply NatTrans.ext
        funext N
        change c.model.E.map (f ▷ N) ≫ q M' N =
          q M N ≫ (c.model.E.map f ▷ c.model.E.obj N)
        have h := hq M N M' N f (𝟙 N)
        rw [c.model.E.map_id] at h
        simpa only [tensorHom_id] using h }
  refine ⟨e, ?_⟩
  intro M N W m n s
  have hd : (d.tensorIso M N).hom.val.app W
      (SheafOfModules.scalarExtensionConstraintTmul (sectionQuotient a T) (M ⊗ N) W
        (sectionPureTensor Λ T M N W m n) s) =
      sectionPureTensor Λ' T _ _ W
        (SheafOfModules.scalarExtensionConstraintTmul (sectionQuotient a T) M W m 1)
        (SheafOfModules.scalarExtensionConstraintTmul (sectionQuotient a T) N W n s) := by
    have hi := d.tensor_inv M N W m n 1 s
    simp only [one_mul] at hi
    have hh := congrArg ((d.tensorIso M N).hom.val.app W) hi
    have hid (z : (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (sectionQuotient a T) M ⊗
        SheafOfModules.changeOfRings.{u, u + 1, u + 1} (sectionQuotient a T) N).val.obj W) :
        (d.tensorIso M N).hom.val.app W ((d.tensorIso M N).inv.val.app W z) = z := by
      change ((d.tensorIso M N).inv ≫ (d.tensorIso M N).hom).val.app W z = z
      rw [(d.tensorIso M N).inv_hom_id]
      rfl
    exact hh.symm.trans (hid _)
  change (q M N).val.app W _ = _
  rw [scalar_element_eq]
  change ((eqToHom (c.model.obj_eq M).symm ⊗ₘ
    eqToHom (c.model.obj_eq N).symm).val.app W)
      ((d.tensorIso M N).hom.val.app W
        ((eqToHom (c.model.obj_eq (M ⊗ N))).val.app W
          ((eqToHom (c.model.obj_eq (M ⊗ N)).symm).val.app W _))) = _
  have hcanc (H : modules Λ T)
      (z : (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (sectionQuotient a T) H).val.obj W) :
      (eqToHom (c.model.obj_eq H)).val.app W
        ((eqToHom (c.model.obj_eq H).symm).val.app W z) = z := by
    change ((eqToHom (c.model.obj_eq H).symm ≫
      eqToHom (c.model.obj_eq H)).val.app W) z = z
    simp
  rw [hcanc, hd, pure_cast, scalar_element_eq, scalar_element_eq]

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
