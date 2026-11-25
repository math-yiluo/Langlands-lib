/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardConstantSectionsTensor
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ExternalSectionsComponents
public import WeilConjectures.AlgebraicGeometry.PicardConstantTensorBalancedSections

/-! # The ordinary external section map on constant tensor coefficients

Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation.
(blueprint: lem-sc-external-constant-sections-tensor-map).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem externalSectionsComponent_smul
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens) (a : Γ(Y, V))
    (s : scalarObj f F (op ⊤)) (t : scalarObj g G (op V)) :
    externalSectionsComponent f g F G V
        (TensorProduct.tmul k s
          (show scalarObj g G (op V) from a • (show G.val.obj (op V) from t))) =
      (show ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
          (externalCupCoefficients f g F G)).val.obj (op V) from a •
        (show ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
            (externalCupCoefficients f g F G)).val.obj (op V) from
          externalSectionsComponent f g F G V (TensorProduct.tmul k s t))) := by
  change tmulSection
      (scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ V) s)
      (scalarUnitSection g (pullback.snd f g) G V (a • (show G.val.obj (op V) from t))) =
    ((pullback.snd f g).app V).hom a • tmulSection _ _
  change tmulSection
      (scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ V) s)
      (((Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G).app
        V (a • (show G.val.obj (op V) from t))) = _
  rw [Hom.app_smul]
  exact tmulSection_smul (((pullback.snd f g).app V).hom a)
    (scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ V) s)
    (scalarUnitSection g (pullback.snd f g) G V t)

-- Elaborating section modules across scalar restriction and the pullback needs this budget.
/-- The external section map on constant tensor coefficients, as an `O_Y`-linear presheaf
morphism: on an open `V` it is the balanced identification
`picardConstantTensorBalancedSections` of the constant tensor sections with
`Γ(X, F) ⊗_k G(V)`, followed by `externalSectionsComponent f g F G V`.
Source: Stacks Project, Varieties, Tag 0BED, affine-open degree-zero calculation.
(blueprint: lem-sc-external-constant-sections-tensor-map).

Multiplication on tensor sections and `O_Y`-linearity of the second projection's adjunction
unit give `O_Y(V)`-linearity, and `externalSectionsComponent_naturality` gives naturality. -/
noncomputable def externalConstantSectionsTensorMap
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G ⟶
      ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
        (externalCupCoefficients f g F G)).val where
  app V := ModuleCat.ofHom
    (X := (picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G).obj V)
    (Y := ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
      (externalCupCoefficients f g F G)).val.obj V)
    { toFun := fun x ↦ externalSectionsComponent f g F G V.unop
        (picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G V.unop x)
      map_add' := by intros; simp
      map_smul' := by
        classical
        intro a x
        obtain ⟨z, rfl⟩ :=
          (picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G V.unop).symm
            |>.surjective x
        induction z using TensorProduct.inductionOn with
        | tmul s t =>
          rw [picardConstantTensorBalancedSections_smul]
          simpa only [AddEquiv.apply_symm_apply, RingHom.id_apply] using
            externalSectionsComponent_smul k X Y f g F G V.unop a s t
        | add z z' hz hz' => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hz hz' }
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    ext x
    change externalSectionsComponent f g F G V.unop
      (picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G V.unop
        ((picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G).map i x)) = _
    rw [picardConstantTensorBalancedSections_map]
    exact congrArg (fun q ↦ q
      (picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G U.unop x))
      (externalSectionsComponent_naturality f g F G i)

theorem externalConstantSectionsTensorMap_app
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens)
    (x : (picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G).obj (op V)) :
    (externalConstantSectionsTensorMap k X Y f g F G).app (op V) x =
      externalSectionsComponent f g F G V
        (picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G V x) :=
  rfl

/-- A component of `externalConstantSectionsTensorMap` is bijective exactly when the
corresponding `k`-linear external section component is bijective.
Source: Stacks Project, Varieties, Tag 0BED, affine-open degree-zero calculation.
(blueprint: lem-sc-external-constant-sections-tensor-map).

Proof: the component is the external section component composed with the bijective balanced
identification. No affine, compactness or quasi-coherence hypothesis is used. -/
theorem externalConstantSectionsTensorMap_app_bijective_iff
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens) :
    Function.Bijective ((externalConstantSectionsTensorMap k X Y f g F G).app (op V)) ↔
      Function.Bijective (externalSectionsComponent f g F G V) := by
  change Function.Bijective (fun x ↦ externalSectionsComponent f g F G V
    (picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G V x)) ↔ _
  exact (picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G V).bijective
    |>.of_comp_iff (externalSectionsComponent f g F G V)

end AlgebraicGeometry.Scheme.Modules
