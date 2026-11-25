/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive

/-!

# Kernels, cokernels and biproducts of module objects

Let `C` be a preadditive monoidal category whose tensor product is additive in each variable, and
let `R : C` be an algebra object. This file constructs kernels, cokernels, biproducts and the zero
object of the category `Mod C R` of left `R`-module objects on the underlying objects of `C`, so
that the forgetful functor `Mod C R ⥤ C` preserves them. That `Mod C R` is abelian when `C` is
abelian and `R ⊗ -` is right exact is `CategoryTheory.Mod.instAbelian`.

* Kernels need no exactness: the action of `R` on `M` restricts to the kernel of an `R`-linear
  map `f : M ⟶ N` because `R ◁ kernel.ι f ≫ γ ≫ f = R ◁ (kernel.ι f ≫ f) ≫ γ = 0`.
* Cokernels use that `R ◁ cokernel.π f` is a cokernel of `R ◁ f`, which is where right
  exactness of `R ⊗ -` enters.
* Binary biproducts and the zero object are computed in `C` as well.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Preadditive

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] {R : C} [MonObj R]

section Kernels

variable {M N : Mod C R} (f : M ⟶ N) [HasKernel f.hom]

/-- The action of `R` on the kernel of an `R`-linear map. -/
noncomputable def kernelSMul : R ⊗ kernel f.hom ⟶ kernel f.hom :=
  kernel.lift f.hom (R ◁ kernel.ι f.hom ≫ γ[R,M.X]) (by
    rw [Category.assoc, act_hom, ← whiskerLeft_comp_assoc, kernel.condition,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp])

@[reassoc (attr := simp)]
lemma kernelSMul_ι : kernelSMul f ≫ kernel.ι f.hom = R ◁ kernel.ι f.hom ≫ γ[R,M.X] :=
  kernel.lift_ι _ _ _

/-- The kernel of an `R`-linear map, as an `R`-module object. -/
noncomputable def kernelObj : Mod C R :=
  letI : ModObj R (kernel f.hom) :=
    { smul := kernelSMul f
      one_smul := by
        change η[R] ▷ _ ≫ kernelSMul f = (λ_ _).hom
        ext
        simp [← whisker_exchange_assoc]
      mul_smul := by
        change μ[R] ▷ _ ≫ kernelSMul f = (α_ R R _).hom ≫ R ◁ kernelSMul f ≫ kernelSMul f
        ext
        simp only [Category.assoc, kernelSMul_ι]
        rw [← whisker_exchange_assoc, mul_act, associator_naturality_right_assoc,
          ← whiskerLeft_comp_assoc R (kernelSMul f), kernelSMul_ι, whiskerLeft_comp_assoc] }
  ⟨kernel f.hom⟩

/-- The inclusion of the kernel of an `R`-linear map. -/
noncomputable def kernelι : kernelObj f ⟶ M :=
  Hom.mk' (kernel.ι f.hom) (kernelSMul_ι f)

@[simp]
lemma kernelι_hom : (kernelι f).hom = kernel.ι f.hom := rfl

/-- The kernel fork of an `R`-linear map, computed in `C`. -/
noncomputable def kernelFork : KernelFork f :=
  KernelFork.ofι (kernelι f) (by ext; simp)

/-- The kernel fork computed in `C` is a limit. -/
noncomputable def isLimitKernelFork : IsLimit (kernelFork f) :=
  KernelFork.IsLimit.ofι (kernelι f) (by ext; simp)
    (fun g hg ↦ Hom.mk' (kernel.lift f.hom g.hom (by rw [← comp_hom', hg, zero_hom])) (by
      change γ[R,_] ≫ _ = R ◁ _ ≫ kernelSMul f
      ext
      rw [Category.assoc, kernel.lift_ι, act_hom, Category.assoc, kernelSMul_ι,
        ← whiskerLeft_comp_assoc, kernel.lift_ι]))
    (fun g hg ↦ by ext; simp)
    (fun g hg m hm ↦ hom_ext _ _ (by
      rw [← cancel_mono (kernel.ι f.hom)]
      simpa using congrArg Hom.hom hm))

instance : HasKernel f := ⟨⟨⟨_, isLimitKernelFork f⟩⟩⟩

instance : PreservesLimit (parallelPair f 0) (forget R : Mod C R ⥤ C) :=
  preservesLimit_of_preserves_limit_cone (isLimitKernelFork f)
    ((KernelFork.isLimitMapConeEquiv _ _).symm (kernelIsKernel f.hom))

end Kernels

section Cokernels

variable [PreservesFiniteColimits (tensorLeft R)]
  {M N : Mod C R} (f : M ⟶ N) [HasCokernel f.hom]

/-- `R ◁ cokernel.π f` is a cokernel of `R ◁ f`, because `R ⊗ -` preserves cokernels. -/
noncomputable def isColimitWhiskerLeftCokernel :
    IsColimit (CokernelCofork.ofπ (R ◁ cokernel.π f.hom) (by
      rw [← whiskerLeft_comp, cokernel.condition, MonoidalPreadditive.whiskerLeft_zero]) :
        Cofork (R ◁ f.hom) 0) :=
  isColimitOfHasCokernelOfPreservesColimit (tensorLeft R) f.hom

instance : Epi (R ◁ cokernel.π f.hom) :=
  Cofork.IsColimit.epi (isColimitWhiskerLeftCokernel f)

/-- The action of `R` on the cokernel of an `R`-linear map. -/
noncomputable def cokernelSMul : R ⊗ cokernel f.hom ⟶ cokernel f.hom :=
  (isColimitWhiskerLeftCokernel f).desc (CokernelCofork.ofπ (γ[R,N.X] ≫ cokernel.π f.hom) (by
    rw [← act_hom_assoc, cokernel.condition, comp_zero]))

@[reassoc (attr := simp)]
lemma π_cokernelSMul :
    R ◁ cokernel.π f.hom ≫ cokernelSMul f = γ[R,N.X] ≫ cokernel.π f.hom :=
  (isColimitWhiskerLeftCokernel f).fac _ WalkingParallelPair.one

/-- The cokernel of an `R`-linear map, as an `R`-module object. -/
noncomputable def cokernelObj : Mod C R :=
  letI : ModObj R (cokernel f.hom) :=
    { smul := cokernelSMul f
      one_smul := by
        change η[R] ▷ _ ≫ cokernelSMul f = (λ_ _).hom
        have : Epi (𝟙_ C ◁ cokernel.π f.hom) := by
          rw [id_whiskerLeft]
          infer_instance
        rw [← cancel_epi (𝟙_ C ◁ cokernel.π f.hom), whisker_exchange_assoc, π_cokernelSMul,
          one_act_assoc, leftUnitor_naturality]
      mul_smul := by
        change μ[R] ▷ _ ≫ cokernelSMul f = (α_ R R _).hom ≫ R ◁ cokernelSMul f ≫ cokernelSMul f
        have : Epi ((R ⊗ R) ◁ cokernel.π f.hom) := by
          have : Epi (R ◁ R ◁ cokernel.π f.hom) := (tensorLeft R).map_epi (R ◁ cokernel.π f.hom)
          rw [tensor_whiskerLeft]
          infer_instance
        rw [← cancel_epi ((R ⊗ R) ◁ cokernel.π f.hom), whisker_exchange_assoc, π_cokernelSMul,
          mul_act_assoc, tensor_whiskerLeft_assoc, Iso.inv_hom_id_assoc,
          ← whiskerLeft_comp_assoc, π_cokernelSMul, whiskerLeft_comp_assoc, π_cokernelSMul] }
  ⟨cokernel f.hom⟩

/-- The projection onto the cokernel of an `R`-linear map. -/
noncomputable def cokernelπ : N ⟶ cokernelObj f :=
  Hom.mk' (cokernel.π f.hom) (π_cokernelSMul f).symm

@[simp]
lemma cokernelπ_hom : (cokernelπ f).hom = cokernel.π f.hom := rfl

/-- The cokernel cofork of an `R`-linear map, computed in `C`. -/
noncomputable def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (by ext; simp)

/-- The cokernel cofork computed in `C` is a colimit. -/
noncomputable def isColimitCokernelCofork : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (cokernelπ f) (by ext; simp)
    (fun g hg ↦ Hom.mk' (cokernel.desc f.hom g.hom (by rw [← comp_hom', hg, zero_hom])) (by
      change cokernelSMul f ≫ _ = R ◁ _ ≫ γ[R,_]
      rw [← cancel_epi (R ◁ cokernel.π f.hom), π_cokernelSMul_assoc, cokernel.π_desc,
        ← whiskerLeft_comp_assoc, cokernel.π_desc, act_hom]))
    (fun g hg ↦ by ext; simp)
    (fun g hg m hm ↦ hom_ext _ _ (by
      rw [← cancel_epi (cokernel.π f.hom)]
      simpa using congrArg Hom.hom hm))

instance : HasCokernel f := ⟨⟨⟨_, isColimitCokernelCofork f⟩⟩⟩

instance : PreservesColimit (parallelPair f 0) (forget R : Mod C R ⥤ C) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCokernelCofork f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (cokernelIsCokernel f.hom))

end Cokernels

section Biproducts

variable [HasBinaryBiproducts C] (M N : Mod C R)

/-- The action of `R` on the biproduct of two `R`-module objects. -/
noncomputable def biprodSMul : R ⊗ (M.X ⊞ N.X) ⟶ M.X ⊞ N.X :=
  biprod.lift (R ◁ biprod.fst ≫ γ[R,M.X]) (R ◁ biprod.snd ≫ γ[R,N.X])

omit [MonoidalPreadditive C] in
@[reassoc (attr := simp)]
lemma biprodSMul_fst : biprodSMul M N ≫ biprod.fst = R ◁ biprod.fst ≫ γ[R,M.X] :=
  biprod.lift_fst _ _

omit [MonoidalPreadditive C] in
@[reassoc (attr := simp)]
lemma biprodSMul_snd : biprodSMul M N ≫ biprod.snd = R ◁ biprod.snd ≫ γ[R,N.X] :=
  biprod.lift_snd _ _

omit [MonoidalPreadditive C] in
@[reassoc (attr := simp)]
lemma whiskerLeft_biprodSMul_fst (X : C) :
    X ◁ biprodSMul M N ≫ X ◁ biprod.fst = X ◁ R ◁ biprod.fst ≫ X ◁ γ[R,M.X] := by
  rw [← whiskerLeft_comp, biprodSMul_fst, whiskerLeft_comp]

omit [MonoidalPreadditive C] in
@[reassoc (attr := simp)]
lemma whiskerLeft_biprodSMul_snd (X : C) :
    X ◁ biprodSMul M N ≫ X ◁ biprod.snd = X ◁ R ◁ biprod.snd ≫ X ◁ γ[R,N.X] := by
  rw [← whiskerLeft_comp, biprodSMul_snd, whiskerLeft_comp]

/-- The biproduct of two `R`-module objects, computed in `C`. -/
noncomputable def biprodObj : Mod C R :=
  letI : ModObj R (M.X ⊞ N.X) :=
    { smul := biprodSMul M N
      one_smul := by
        change η[R] ▷ _ ≫ biprodSMul M N = (λ_ _).hom
        ext <;> simp [← whisker_exchange_assoc]
      mul_smul := by
        change μ[R] ▷ _ ≫ biprodSMul M N = (α_ R R _).hom ≫ R ◁ biprodSMul M N ≫ biprodSMul M N
        ext <;> simp [← whisker_exchange_assoc] }
  ⟨M.X ⊞ N.X⟩

/-- The binary bicone of `R`-module objects, computed in `C`. -/
noncomputable def binaryBicone : BinaryBicone M N where
  pt := biprodObj M N
  fst := Hom.mk' biprod.fst (biprodSMul_fst M N)
  snd := Hom.mk' biprod.snd (biprodSMul_snd M N)
  inl := Hom.mk' biprod.inl (by
    change γ[R,M.X] ≫ biprod.inl = R ◁ biprod.inl ≫ biprodSMul M N
    ext
    · simp only [Category.assoc, biprodSMul_fst, biprod.inl_fst, Category.comp_id]
      rw [← whiskerLeft_comp_assoc, biprod.inl_fst, whiskerLeft_id, Category.id_comp]
    · simp only [Category.assoc, biprodSMul_snd, biprod.inl_snd, comp_zero]
      rw [← whiskerLeft_comp_assoc, biprod.inl_snd, MonoidalPreadditive.whiskerLeft_zero,
        zero_comp])
  inr := Hom.mk' biprod.inr (by
    change γ[R,N.X] ≫ biprod.inr = R ◁ biprod.inr ≫ biprodSMul M N
    ext
    · simp only [Category.assoc, biprodSMul_fst, biprod.inr_fst, comp_zero]
      rw [← whiskerLeft_comp_assoc, biprod.inr_fst, MonoidalPreadditive.whiskerLeft_zero,
        zero_comp]
    · simp only [Category.assoc, biprodSMul_snd, biprod.inr_snd, Category.comp_id]
      rw [← whiskerLeft_comp_assoc, biprod.inr_snd, whiskerLeft_id, Category.id_comp])
  inl_fst := by ext; simp
  inl_snd := by ext; simp
  inr_fst := by ext; simp
  inr_snd := by ext; simp

/-- The binary bicone of `R`-module objects computed in `C` is a bilimit. -/
noncomputable def isBilimitBinaryBicone : (binaryBicone M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (by ext; simp [binaryBicone, biprodObj])

instance : HasBinaryBiproducts (Mod C R) where
  has_binary_biproduct M N := .mk ⟨_, isBilimitBinaryBicone M N⟩

end Biproducts

section ZeroObject

open ZeroObject

variable [HasZeroObject C]

/-- The zero object of `C`, as an `R`-module object. -/
noncomputable def zeroObj : Mod C R :=
  letI : ModObj R (0 : C) :=
    { smul := 0
      one_smul := (isZero_zero C).eq_of_tgt _ _
      mul_smul := (isZero_zero C).eq_of_tgt _ _ }
  ⟨0⟩

lemma isZero_zeroObj : IsZero (zeroObj : Mod C R) :=
  (IsZero.iff_id_eq_zero _).2 (by ext; exact (isZero_zero C).eq_of_src _ _)

instance : HasZeroObject (Mod C R) := ⟨⟨_, isZero_zeroObj⟩⟩

instance [HasBinaryBiproducts C] : HasFiniteProducts (Mod C R) :=
  hasFiniteProducts_of_has_binary_and_terminal

instance [HasBinaryBiproducts C] : HasFiniteBiproducts (Mod C R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end ZeroObject

end CategoryTheory.Mod
