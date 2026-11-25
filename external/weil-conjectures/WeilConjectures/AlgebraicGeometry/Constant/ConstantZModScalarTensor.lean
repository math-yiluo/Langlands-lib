/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree
public import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Absolute tensor and scalar extension from a constant cyclic ring

Source: the finite-level tensor comparison in the Tate-twist construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace AlgebraicGeometry.Scheme

private local instance abSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private local instance abSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private local instance abBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private local instance commModuleSections (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : _root_.PresheafOfModules.{u + 1} (purTwistRing X R).obj) (V : X.ProEtᵒᵖ) :
    Module (R.obj.obj V) (M.obj V) := (M.obj V).isModule

private local instance constantAbForget (X : Scheme.{u}) :
    (ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) where
  le := by
    intro P Q f hf
    let : Presheaf.IsLocallyInjective (ProEt.topology X) f := hf.isLocallyInjective
    let : Presheaf.IsLocallySurjective (ProEt.topology X) f := hf.isLocallySurjective
    let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
    let : Presheaf.IsLocallyInjective (ProEt.topology X) (Functor.whiskerRight f F) :=
      ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology X) f x y h⟩
    let : Presheaf.IsLocallySurjective (ProEt.topology X) (Functor.whiskerRight f F) :=
      ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology X) f x⟩
    exact (ProEt.topology X).W_of_isLocallyBijective (Functor.whiskerRight f F)

private noncomputable def abTensorMap (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    {V W : X.ProEtᵒᵖ} (f : V ⟶ W) :
    ModuleCat.of (S.obj.obj V) ((S.obj.obj V) ⊗[ℤ] (M.obj.obj V)) ⟶
      (ModuleCat.restrictScalars (S.obj.map f).hom).obj
        (ModuleCat.of (S.obj.obj W) ((S.obj.obj W) ⊗[ℤ] (M.obj.obj W))) := by
  let N := (ModuleCat.restrictScalars (S.obj.map f).hom).obj
    (ModuleCat.of (S.obj.obj W) ((S.obj.obj W) ⊗[ℤ] (M.obj.obj W)))
  let t : (S.obj.obj V) ⊗[ℤ] (M.obj.obj V) →+ N :=
    (TensorProduct.map (S.obj.map f).hom.toAddMonoidHom.toIntLinearMap
      (M.obj.map f).hom.toIntLinearMap).toAddMonoidHom
  exact ModuleCat.ofHom (Y := N)
    { toFun := t
      map_add' := t.map_add
      map_smul' := fun s z ↦ by
        induction z using TensorProduct.inductionOn with
        | add z z' hz hz' =>
          calc
            t (s • (z + z')) = t (s • z) + t (s • z') :=
              (congrArg t (smul_add s z z')).trans (t.map_add _ _)
            _ = s • t z + s • t z' := congrArg₂ (fun x y : N ↦ x + y) hz hz'
            _ = s • t (z + z') :=
              (smul_add s (t z) (t z')).symm.trans (congrArg (s • ·) (t.map_add z z').symm)
        | tmul b m =>
          change (S.obj.map f (s * b)) ⊗ₜ[ℤ] (M.obj.map f m) =
            (S.obj.map f s * S.obj.map f b) ⊗ₜ[ℤ] (M.obj.map f m)
          rw [map_mul] }

private local instance tensorSectionModule (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) (V : X.ProEtᵒᵖ) :
    Module ((purTwistRing X S).obj.obj V) ((S.obj.obj V) ⊗[ℤ] (M.obj.obj V)) :=
  inferInstanceAs (Module (S.obj.obj V) ((S.obj.obj V) ⊗[ℤ] (M.obj.obj V)))

private noncomputable abbrev abTensorPresheaf (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    _root_.PresheafOfModules.{u + 1} (purTwistRing X S).obj where
  obj V := ModuleCat.of (S.obj.obj V) ((S.obj.obj V) ⊗[ℤ] (M.obj.obj V))
  map f := abTensorMap X S M f
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b m =>
      change (S.obj.map (𝟙 V) b) ⊗ₜ[ℤ] (M.obj.map (𝟙 V) m) = b ⊗ₜ[ℤ] m
      have hb : S.obj.map (𝟙 V) b = b :=
        ConcreteCategory.congr_hom (S.obj.map_id V) b
      have hm : M.obj.map (𝟙 V) m = m :=
        ConcreteCategory.congr_hom (M.obj.map_id V) m
      rw [hb, hm]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b m =>
      change (S.obj.map (f ≫ g) b) ⊗ₜ[ℤ] (M.obj.map (f ≫ g) m) =
        (S.obj.map g (S.obj.map f b)) ⊗ₜ[ℤ] (M.obj.map g (M.obj.map f m))
      simp only [Functor.map_comp, CategoryTheory.ConcreteCategory.comp_apply]

private noncomputable abbrev abTensorSheaf (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  (PresheafOfModules.sheafification (R := purTwistRing X S) (𝟙 _)).obj
    (abTensorPresheaf X S M)

private noncomputable def abTensorRawToExtension (X : Scheme.{u}) (ℓ n : ℕ)
    (A : Type (u + 1)) [CommRing A] (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (M : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n))) :
    abTensorPresheaf X (tateFiniteCoefficient X A) ((SheafOfModules.toSheaf _).obj M) ⟶
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (tateFiniteScalar X ℓ A n a) M).val := by
  let S := tateFiniteCoefficient X A
  let α := tateFiniteScalar X ℓ A n a
  let T := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M
  let P := abTensorPresheaf X S ((SheafOfModules.toSheaf _).obj M)
  let η : SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M ⟶
      T.val := (PresheafOfModules.sheafificationAdjunction
        (R := purTwistRing X S) (𝟙 _)).unit.app _
  let f (V : X.ProEtᵒᵖ) : (S.obj.obj V) ⊗[ℤ] (M.val.obj V) →ₗ[ℤ] T.val.obj V := by
    letI : Algebra ((purTwistFiniteRing X ℓ n).obj.obj V) (S.obj.obj V) :=
      (α.hom.app V).hom.toAlgebra
    let f₁ (b : S.obj.obj V) : M.val.obj V →ₗ[ℤ] T.val.obj V :=
      (show M.val.obj V →+ T.val.obj V from
        { toFun := fun m ↦ SheafOfModules.scalarExtensionSection α M V b m
          map_zero' := SheafOfModules.scalarExtensionSection_zero α M V b
          map_add' := fun x y ↦ SheafOfModules.scalarExtensionSection_add α M V b x y
        }).toIntLinearMap
    let f₂ : S.obj.obj V →+ (M.val.obj V →ₗ[ℤ] T.val.obj V) :=
      { toFun := f₁
        map_zero' := by
          apply LinearMap.ext
          intro m
          change η.app V ((0 : S.obj.obj V) ⊗ₜ[_, (α.hom.app V).hom] m) = 0
          exact (congrArg (η.app V) (TensorProduct.zero_tmul (S.obj.obj V) m)).trans
            ((η.app V).hom.map_zero)
        map_add' := fun b c ↦ by
          apply LinearMap.ext
          intro m
          change η.app V ((b + c) ⊗ₜ[_, (α.hom.app V).hom] m) =
            η.app V (b ⊗ₜ[_, (α.hom.app V).hom] m) +
              η.app V (c ⊗ₜ[_, (α.hom.app V).hom] m)
          exact (congrArg (η.app V) (TensorProduct.add_tmul b c m)).trans
            ((η.app V).hom.map_add _ _) }
    exact TensorProduct.lift f₂.toIntLinearMap
  let g : P ⟶ T.val :=
    { app := fun V ↦ ModuleCat.ofHom (X := P.obj V) (Y := T.val.obj V)
        { toFun := f V
          map_add' := (f V).map_add
          map_smul' := fun b z ↦ by
            induction z using TensorProduct.inductionOn with
            | add z z' hz hz' =>
              exact ((congrArg (f V) (smul_add b z z')).trans ((f V).map_add _ _)).trans
                ((congrArg₂ (fun x y : T.val.obj V ↦ x + y) hz hz').trans
                  ((smul_add b ((f V) z) ((f V) z')).symm.trans
                    (congrArg (b • ·) ((f V).map_add z z').symm)))
            | tmul c m =>
              let := (α.hom.app V).hom.toAlgebra
              change η.app V ((b * c) ⊗ₜ[_, (α.hom.app V).hom] m) =
                b • η.app V (c ⊗ₜ[_, (α.hom.app V).hom] m)
              have h := (η.app V).hom.map_smul b (c ⊗ₜ[_, (α.hom.app V).hom] m)
              change η.app V ((b * c) ⊗ₜ[_, (α.hom.app V).hom] m) =
                b • η.app V (c ⊗ₜ[_, (α.hom.app V).hom] m) at h
              exact h }
      naturality := by
        intro V W i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | add z z' hz hz' => simp only [map_add, hz, hz']
        | tmul b m =>
          exact (SheafOfModules.scalarExtensionSection_naturality α M i b m).symm }
  exact g

private noncomputable def abTensorToExtension (X : Scheme.{u}) (ℓ n : ℕ)
    (A : Type (u + 1)) [CommRing A] (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (M : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n))) :
    abTensorSheaf X (tateFiniteCoefficient X A) ((SheafOfModules.toSheaf _).obj M) ⟶
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (tateFiniteScalar X ℓ A n a) M := by
  exact (PresheafOfModules.sheafificationHomEquiv
    (R := purTwistRing X (tateFiniteCoefficient X A)) (𝟙 _)
    (P := abTensorPresheaf X (tateFiniteCoefficient X A)
      ((SheafOfModules.toSheaf _).obj M))
    (F := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (tateFiniteScalar X ℓ A n a) M)).symm
      (abTensorRawToExtension X ℓ n A a M)

private noncomputable def abTensorInsertion (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    M ⟶ (SheafOfModules.toSheaf _).obj (abTensorSheaf X S M) := by
  let η : abTensorPresheaf X S M ⟶ (abTensorSheaf X S M).val :=
    (PresheafOfModules.sheafificationAdjunction (R := purTwistRing X S)
      (𝟙 _)).unit.app _
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro V
    exact AddCommGrpCat.ofHom
      { toFun := fun m ↦ η.app V ((1 : S.obj.obj V) ⊗ₜ[ℤ] m)
        map_zero' := by
          exact (congrArg (η.app V)
            (TensorProduct.tmul_zero (R := ℤ) (M.obj.obj V) (1 : S.obj.obj V))).trans
              (map_zero _)
        map_add' := fun m m' ↦ by
          exact (congrArg (η.app V) (TensorProduct.tmul_add _ m m')).trans (map_add _ _ _) }
  · intro V W i
    ext m
    have h := PresheafOfModules.naturality_apply η i ((1 : S.obj.obj V) ⊗ₜ[ℤ] m)
    change η.app W ((1 : S.obj.obj W) ⊗ₜ[ℤ] M.obj.map i m) = _
    change η.app W ((S.obj.map i 1) ⊗ₜ[ℤ] M.obj.map i m) = _ at h
    have h1 : S.obj.map i (1 : S.obj.obj V) = 1 := (S.obj.map i).hom.map_one
    rw [h1] at h
    exact h

private theorem abTensorToExtension_unit (X : Scheme.{u}) (ℓ n : ℕ)
    (A : Type (u + 1)) [CommRing A] (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (M : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n)))
    (V : X.ProEtᵒᵖ) (b : (tateFiniteCoefficient X A).obj.obj V) (m : M.val.obj V) :
    (abTensorToExtension X ℓ n A a M).val.app V
      ((toSheafify (ProEt.topology X)
        (abTensorPresheaf X (tateFiniteCoefficient X A)
          ((SheafOfModules.toSheaf _).obj M)).presheaf).app V (b ⊗ₜ[ℤ] m)) =
      SheafOfModules.scalarExtensionSection (tateFiniteScalar X ℓ A n a) M V b m := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (R := purTwistRing X (tateFiniteCoefficient X A)) (𝟙 _)
    (P := abTensorPresheaf X (tateFiniteCoefficient X A)
      ((SheafOfModules.toSheaf _).obj M))
    (F := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (tateFiniteScalar X ℓ A n a) M)).apply_symm_apply
      (abTensorRawToExtension X ℓ n A a M)
  have h' := congrArg (fun f ↦ f.app V (b ⊗ₜ[ℤ] m)) h
  change (abTensorToExtension X ℓ n A a M).val.app V
      ((toSheafify (ProEt.topology X)
        (abTensorPresheaf X (tateFiniteCoefficient X A)
          ((SheafOfModules.toSheaf _).obj M)).presheaf).app V (b ⊗ₜ[ℤ] m)) =
      SheafOfModules.scalarExtensionSection (tateFiniteScalar X ℓ A n a) M V b m at h'
  exact h'

private noncomputable def abResidueLinearLift (X : Scheme.{u}) (ℓ n : ℕ)
    (M P : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n)))
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj P) : M ⟶ P := by
  let a := Functor.whiskerRight (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallySurjective (ProEt.topology X) a := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology X)
      (Functor.whiskerRight (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  let g : (PresheafOfModules.restrictScalars a).obj M.val ⟶
      (PresheafOfModules.restrictScalars a).obj P.val :=
    PresheafOfModules.homMk f.hom (by
      intro V b x
      obtain ⟨b⟩ := b
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective b
      change f.hom.app V
          (@SMul.smul _ _ (M.val.obj V).isModule.toSMul
            (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) x) =
        @SMul.smul _ _ (P.val.obj V).isModule.toSMul
          (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) (f.hom.app V x)
      simp only [map_intCast]
      have hM := @Int.cast_smul_eq_zsmul
        ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
        (M.val.obj V) _ _ (M.val.obj V).isModule z x
      have hP := @Int.cast_smul_eq_zsmul
        ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
        (P.val.obj V) _ _ (P.val.obj V).isModule z (f.hom.app V x)
      exact (congrArg (f.hom.app V) hM).trans
        (((f.hom.app V).hom.map_zsmul z x).trans hP.symm))
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a P.isSheaf).symm g⟩

/-- For a module over the constant cyclic ring, tensoring its underlying abelian
sheaf with the constant coefficient group computes scalar extension.

Source: blueprint `sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md`,
finite-level formula and local-generator paragraph
(blueprint: lem-sp-constant-zmod-scalar-tensor).

Proof: sheafify the presheaf of integer tensor products A(V) tensor_Z M(V).
A bilinear map out of this presheaf is balanced over the constant cyclic ring:
locally each scalar lifts to an integer, and integer balancing follows from
additivity. The balancing equality descends by separatedness of the target sheaf.
Thus its sheafification has the scalar-extension universal property. Explicitly,
the comparison sends b tensor m to the scalar-extension pure tensor b tensor m;
the inverse uses the same formula on local representatives. Both composites are
the identity on pure tensors, hence on their sums and after sheafification.
This includes the zero coefficient ring and the empty scheme. -/
theorem constantZMod_scalarTensor (X : Scheme.{u}) (ℓ n : ℕ)
    (A : Type (u + 1)) [CommRing A] (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (M : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n))) :
    Nonempty (((constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A) ⊗ (SheafOfModules.toSheaf _).obj M) ≅
      (SheafOfModules.toSheaf _).obj
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (tateFiniteScalar X ℓ A n a) M)) := by
  let J := ProEt.topology X
  let S := tateFiniteCoefficient X A
  let α := tateFiniteScalar X ℓ A n a
  let M₀ := (SheafOfModules.toSheaf _).obj M
  let P := abTensorPresheaf X S M₀
  let Q := abTensorSheaf X S M₀
  let T := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M
  let η : P ⟶ Q.val :=
    (PresheafOfModules.sheafificationAdjunction (R := purTwistRing X S)
      (𝟙 _)).unit.app P
  let p : Q ⟶ T := abTensorToExtension X ℓ n A a M
  let i := abTensorInsertion X S M₀
  let iR : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj Q :=
    abResidueLinearLift X ℓ n M _ i
  let q : T ⟶ Q := SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1}
    α M Q iR
  have hp (V : X.ProEtᵒᵖ) (b : S.obj.obj V) (m : M.val.obj V) :
      p.val.app V (η.app V (b ⊗ₜ[ℤ] m)) =
        SheafOfModules.scalarExtensionSection α M V b m :=
    abTensorToExtension_unit X ℓ n A a M V b m
  have hq (V : X.ProEtᵒᵖ) (b : S.obj.obj V) (m : M.val.obj V) :
      q.val.app V (SheafOfModules.scalarExtensionSection α M V b m) =
        η.app V (b ⊗ₜ[ℤ] m) := by
    have h := SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}
      α M Q iR V b m
    calc
      _ = b • (show Q.val.obj V from iR.val.app V m) := h
      _ = b • (η.app V ((1 : S.obj.obj V) ⊗ₜ[ℤ] m)) := rfl
      _ = _ := by
        exact ((η.app V).hom.map_smul b ((1 : S.obj.obj V) ⊗ₜ[ℤ] m)).symm.trans
          (congrArg (η.app V) (by
            change (b * 1) ⊗ₜ[ℤ] m = b ⊗ₜ[ℤ] m
            rw [mul_one]))
  have hpq : p ≫ q = 𝟙 Q := by
    apply (PresheafOfModules.sheafificationHomEquiv
      (R := purTwistRing X S) (𝟙 _) (P := P) (F := Q)).injective
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b m =>
      change q.val.app V (p.val.app V (η.app V (b ⊗ₜ[ℤ] m))) =
        η.app V (b ⊗ₜ[ℤ] m)
      exact (congrArg (q.val.app V) (hp V b m)).trans (hq V b m)
  have hqp : q ≫ p = 𝟙 T := by
    apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1} α M
    intro V b m
    change p.val.app V (q.val.app V
      (SheafOfModules.scalarExtensionSection α M V b m)) =
        SheafOfModules.scalarExtensionSection α M V b m
    exact (congrArg (p.val.app V) (hq V b m)).trans (hp V b m)
  let e : Q ≅ T := ⟨p, q, hpq, hqp⟩
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj S
  let eP : P.presheaf ≅ B.obj ⊗ M₀.obj :=
    NatIso.ofComponents (fun V ↦ Iso.refl _) (by intro V W f; ext z; rfl)
  let eQ : (SheafOfModules.toSheaf _).obj Q ≅ B ⊗ M₀ :=
    (presheafToSheaf J AddCommGrpCat.{u + 1}).mapIso eP ≪≫
      (Functor.Monoidal.μIso (presheafToSheaf J AddCommGrpCat.{u + 1}) B.obj M₀.obj).symm ≪≫
      (asIso ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit.app B) ⊗ᵢ
        asIso ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit.app M₀))
  let eB : B ≅ (constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of A) :=
    (constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app (CommRingCat.of A)
  exact ⟨(eB.symm ⊗ᵢ Iso.refl _) ≪≫ eQ.symm ≪≫ (SheafOfModules.toSheaf _).mapIso e⟩

end AlgebraicGeometry.Scheme
