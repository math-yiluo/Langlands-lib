/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.Logic.Equiv.Fin.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor

/-!
# Tensoring with the regular module

For a commutative monoid `A` in a braided monoidal category, the tensor product `P ⊗_A A` of an
`A`-module `P` with the regular module is `P` itself: the coequalizer of `P ⊗ (A ⊗ A) ⇉ P ⊗ A`
is split by `p ↦ p ⊗ 1` and `p ⊗ a ↦ p ⊗ a ⊗ 1`, with quotient map the right action
(`CategoryTheory.Mod.tensorLeftRegularIso`). Hence `Hom_A(A, -)` is the identity
(`CategoryTheory.Mod.ihomRegularIso`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {A : C}
  [MonObj A] [IsCommMonObj A]

/-- The right action `P ⊗ A ⟶ P` as a morphism of `A`-modules, `A` acting on `P ⊗ A` through
`P`. -/
def rightActHom (P : Mod C A) : (tensorRight A A).obj P ⟶ P :=
  homMk (M := (tensorRight A A).obj P) (N := P) (rightAct P) (by
    change ((α_ A P.X A).inv ≫ act P.X ▷ A) ≫ rightAct P = A ◁ rightAct P ≫ act P.X
    rw [Category.assoc, act_whiskerRight_rightAct, Iso.inv_hom_id_assoc])

/-- The morphism `P ⟶ P ⊗ A`, `p ↦ p ⊗ 1`, of `A`-modules. -/
def unitRight (P : Mod C A) : P ⟶ (tensorRight A A).obj P :=
  homMk (M := P) (N := (tensorRight A A).obj P) ((ρ_ P.X).inv ≫ P.X ◁ η[A]) (by
    change act P.X ≫ (ρ_ P.X).inv ≫ P.X ◁ η[A] =
      A ◁ ((ρ_ P.X).inv ≫ P.X ◁ η[A]) ≫ (α_ A P.X A).inv ≫ act P.X ▷ A
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange]
    simp)

/-- The unit `p ↦ p ⊗ 1` is a section of the right action: `P → P ⊗ A → P` is the identity. -/
lemma unitRight_rightActHom (P : Mod C A) : unitRight P ≫ rightActHom P = 𝟙 P := by
  ext
  change ((ρ_ P.X).inv ≫ P.X ◁ η[A]) ≫ (β_ P.X A).hom ≫ act P.X = 𝟙 _
  rw [Category.assoc, BraidedCategory.braiding_naturality_right_assoc,
    rightUnitor_inv_braiding_assoc, one_act, Iso.inv_hom_id]

/-- The right action is associative: `p ⊗ (a ⊗ b) ↦ p (a b) = (p a) b`. -/
lemma whiskerLeft_mul_rightAct (P : Mod C A) :
    P.X ◁ μ[A] ≫ rightAct P = (α_ P.X A A).inv ≫ rightAct P ▷ A ≫ rightAct P := by
  have h : A ◁ act P.X ≫ act P.X = (α_ A A P.X).inv ≫ μ[A] ▷ P.X ≫ act P.X := by simp
  have key : (β_ P.X (A ⊗ A)).hom ≫ (β_ A A).hom ▷ P.X = (α_ P.X A A).inv ≫
      (β_ P.X A).hom ▷ A ≫ (β_ (A ⊗ P.X) A).hom ≫ (α_ A A P.X).inv := by
    rw [BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom]
    monoidal
  calc P.X ◁ μ[A] ≫ rightAct P = (β_ P.X (A ⊗ A)).hom ≫ μ[A] ▷ P.X ≫ act P.X := by
        simp only [rightAct, BraidedCategory.braiding_naturality_right_assoc]
    _ = ((β_ P.X (A ⊗ A)).hom ≫ (β_ A A).hom ▷ P.X) ≫ μ[A] ▷ P.X ≫ act P.X := by
        rw [Category.assoc, ← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]
    _ = _ := by
        rw [key]
        simp only [rightAct, comp_whiskerRight, Category.assoc,
          BraidedCategory.braiding_naturality_left_assoc, h]

/-- The right action is natural: `P ⊗ A → Q ⊗ A → Q` equals `P ⊗ A → P → Q`. -/
lemma rightActHom_naturality {P Q : Mod C A} (f : P ⟶ Q) :
    (tensorRight A A).map f ≫ rightActHom Q = rightActHom P ≫ f := by
  ext
  change f.hom ▷ A ≫ (β_ Q.X A).hom ≫ act Q.X = ((β_ P.X A).hom ≫ act P.X) ≫ f.hom
  simp only [BraidedCategory.braiding_naturality_left_assoc, Category.assoc, act_hom]

/-- The right action coequalizes the two maps `P ⊗ (A ⊗ A) ⇉ P ⊗ A`:
`P ⊗ (A ⊗ A) → P ⊗ A → P` is the same through the multiplication of `A` and through the action
on `P`. -/
lemma tensorRightMap_act_comp_rightActHom (P : Mod C A) :
    (tensorRightMap A (act (regular A).X)).app P ≫ rightActHom P =
      (tensorRightRightAct A A).app P ≫ rightActHom P := by
  ext
  exact (whiskerLeft_mul_rightAct P).trans (Category.assoc _ _ _).symm

/-- The cofork `P ⊗ (A ⊗ A) ⇉ P ⊗ A ⟶ P` of the right action. -/
noncomputable abbrev rightActCofork (P : Mod C A) :=
  Cofork.ofπ (rightActHom P) (tensorRightMap_act_comp_rightActHom P)

/-- The right action `P ⊗ A ⟶ P` is the coequalizer of `P ⊗ (A ⊗ A) ⇉ P ⊗ A`: it is split by
`p ↦ p ⊗ 1` and `p ⊗ a ↦ p ⊗ a ⊗ 1`. -/
noncomputable def rightActCoforkIsColimit (P : Mod C A) : IsColimit (rightActCofork P) := by
  let t : (tensorRight A A).obj P ⟶ (tensorRight A (A ⊗ A)).obj P :=
    (tensorRightMap A ((ρ_ A).inv ≫ A ◁ η[A])).app P
  have ht₁ : t ≫ (tensorRightMap A (act (regular A).X)).app P = 𝟙 _ := by
    ext
    change P.X ◁ ((ρ_ A).inv ≫ A ◁ η[A]) ≫ P.X ◁ μ[A] = 𝟙 _
    rw [← MonoidalCategory.whiskerLeft_comp, Category.assoc, MonObj.mul_one, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]
  have ht₂ : t ≫ (tensorRightRightAct A A).app P = rightActHom P ≫ unitRight P := by
    ext
    change P.X ◁ ((ρ_ A).inv ≫ A ◁ η[A]) ≫ (α_ P.X A A).inv ≫ rightAct P ▷ A =
      rightAct P ≫ (ρ_ P.X).inv ≫ P.X ◁ η[A]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange]
    simp
  refine Cofork.IsColimit.mk _ (fun s ↦ unitRight P ≫ s.π) (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · change rightActHom P ≫ unitRight P ≫ s.π = s.π
    rw [← Category.assoc, ← ht₂, Category.assoc, ← s.condition, ← Category.assoc, ht₁,
      Category.id_comp]
  · rw [← hm]
    change m = unitRight P ≫ rightActHom P ≫ m
    rw [← Category.assoc, unitRight_rightActHom, Category.id_comp]

section TensorLeft

variable [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]

/-- The cocone on the diagram defining `P ⊗_A A` given by the right action. -/
noncomputable abbrev rightActCocone (P : Mod C A) :
    Cocone ((tensorLeftDiagram A (regular A)).flip.obj P) :=
  (Cocone.precompose (diagramIsoParallelPair _).hom).obj (rightActCofork P)

/-- The cocone of the right action is a colimit. -/
noncomputable def rightActCoconeIsColimit (P : Mod C A) : IsColimit (rightActCocone P) :=
  (IsColimit.precomposeHomEquiv _ _).symm (rightActCoforkIsColimit P)

/-- The map `P ⊗_A A ⟶ P` induced by the right action, natural in `P`. -/
noncomputable def tensorLeftRegularHom : tensorLeft (regular A) ⟶ 𝟭 (Mod C A) where
  app P := colimit.desc _ (rightActCocone P)
  naturality P Q f := by
    refine colimit.hom_ext fun j ↦ ?_
    simp only [tensorLeft, Functor.comp_map, colim_map, Functor.id_map, ι_colimMap_assoc,
      colimit.ι_desc, colimit.ι_desc_assoc]
    cases j
    · simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, diagramIsoParallelPair_hom_app,
        Cofork.ofπ_ι_app]
      dsimp
      simp only [Category.id_comp, Category.assoc]
      erw [(tensorRightMap A (act (regular A).X)).naturality_assoc f, rightActHom_naturality]
      rfl
    · simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, diagramIsoParallelPair_hom_app,
        Cofork.ofπ_ι_app]
      dsimp
      simp only [Category.id_comp]
      exact rightActHom_naturality f

instance : IsIso (tensorLeftRegularHom (A := A)) := by
  have (P : Mod C A) : IsIso (tensorLeftRegularHom.app P) :=
    inferInstanceAs (IsIso ((colimit.isColimit _).coconePointUniqueUpToIso
      (rightActCoconeIsColimit P)).hom)
  exact NatIso.isIso_of_isIso_app _

/-- **Tensoring with the regular module is the identity**: `P ⊗_A A ≅ P` through the right
action. -/
noncomputable def tensorLeftRegularIso : tensorLeft (regular A) ≅ 𝟭 (Mod C A) :=
  asIso tensorLeftRegularHom

end TensorLeft

section Hom

variable [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- **`Hom_A(A, -)` is the identity**, being right adjoint to `- ⊗_A A ≅ 𝟭`. -/
noncomputable def ihomRegularIso : ihom (regular A) ≅ 𝟭 (Mod C A) :=
  (ihomAdjunction (regular A)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft tensorLeftRegularIso.symm)

/-- `Hom_A(-, ·)` as an additive map on morphisms. -/
@[simps]
noncomputable def ihomMapAddHom (M M' : Mod C A) : (M ⟶ M') →+ (ihom M' ⟶ ihom M) where
  toFun := ihomMap
  map_zero' := by
    have h := ihomMap_add (0 : M ⟶ M') 0
    rwa [add_zero, left_eq_add] at h
  map_add' := ihomMap_add

lemma sum_ihomMap_ι_comp_ihomMap_π {n : ℕ} (M : Fin n → Mod C A) :
    ∑ i, ihomMap (biproduct.ι M i) ≫ ihomMap (biproduct.π M i) = 𝟙 (ihom (⨁ M)) := by
  simp_rw [← ihomMap_comp]
  calc ∑ i, ihomMap (biproduct.π M i ≫ biproduct.ι M i) =
      ihomMapAddHom (⨁ M) (⨁ M) (∑ i, biproduct.π M i ≫ biproduct.ι M i) := by
        rw [map_sum]; rfl
    _ = 𝟙 _ := by rw [biproduct.total]; exact ihomMap_id _

/-- `Hom_A(⨁ᵢ Mᵢ, -)` preserves epimorphisms if each `Hom_A(Mᵢ, -)` does: it is the direct sum
of the `Hom_A(Mᵢ, -)`, the projections and inclusions being induced by those of `⨁ᵢ Mᵢ`. -/
lemma epi_ihom_biproduct_map {n : ℕ} (M : Fin n → Mod C A) {N N' : Mod C A} (f : N ⟶ N')
    (h : ∀ i, Epi ((ihom (M i)).map f)) : Epi ((ihom (⨁ M)).map f) := by
  refine Preadditive.epi_of_cancel_zero _ fun {Z} g hg ↦ ?_
  have htot := sum_ihomMap_ι_comp_ihomMap_π M
  have hi (i : Fin n) : (ihomMap (biproduct.π M i)).app N' ≫ g = 0 := by
    have := h i
    rw [← cancel_epi ((ihom (M i)).map f), ← Category.assoc, (ihomMap _).naturality,
      Category.assoc, hg, comp_zero, comp_zero]
  rw [← Category.id_comp g, ← NatTrans.id_app, ← htot, NatTrans.app_sum, Preadditive.sum_comp]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [NatTrans.comp_app, Category.assoc, hi, comp_zero]

/-- The bicone exhibiting `Hom_A(⨁ᵢ Mᵢ, N)` as the direct sum of the `Hom_A(Mᵢ, N)`. -/
@[simps]
noncomputable def ihomBiproductBicone {n : ℕ} (M : Fin n → Mod C A) (N : Mod C A) :
    Bicone fun i ↦ (ihom (M i)).obj N where
  pt := (ihom (⨁ M)).obj N
  π i := (ihomMap (biproduct.ι M i)).app N
  ι i := (ihomMap (biproduct.π M i)).app N
  ι_π i j := by
    rw [← NatTrans.comp_app, ← ihomMap_comp]
    by_cases h : i = j
    · subst h
      simp [ihomMap_id]
    · rw [biproduct.ι_π_ne _ (Ne.symm h), dite_eq_right h]
      exact congrArg (NatTrans.app · N) ((ihomMapAddHom _ _).map_zero)

/-- **`Hom_A(-, N)` takes finite direct sums to direct sums.** -/
noncomputable def ihomBiproductIso {n : ℕ} (M : Fin n → Mod C A) (N : Mod C A) :
    (ihom (⨁ M)).obj N ≅ ⨁ fun i ↦ (ihom (M i)).obj N :=
  biproduct.uniqueUpToIso _ (isBilimitOfTotal (ihomBiproductBicone M N) (by
    simp only [ihomBiproductBicone_π, ihomBiproductBicone_ι]
    simp_rw [← NatTrans.comp_app]
    rw [← NatTrans.app_sum, sum_ihomMap_ι_comp_ihomMap_π]
    rfl))

/-- The internal hom between free modules of finite rank is free:
`Hom_A(Aⁿ, Aᵐ) ≅ A^{n m}`. -/
noncomputable def ihomFreeIso (n m : ℕ) :
    (ihom (⨁ fun _ : Fin n ↦ regular A)).obj (⨁ fun _ : Fin m ↦ regular A) ≅
      ⨁ fun _ : Fin (n * m) ↦ regular A :=
  ihomBiproductIso _ _ ≪≫ biproduct.mapIso (fun _ ↦ ihomRegularIso.app _) ≪≫
    biproductBiproductIso (fun _ : Fin n ↦ Fin m) (fun _ _ ↦ regular A) ≪≫
    biproduct.whiskerEquiv (f := fun _ : (Σ _ : Fin n, Fin m) ↦ regular A)
      (g := fun _ : Fin (n * m) ↦ regular A)
      ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv) (fun _ ↦ Iso.refl _)

/-- `Hom_A(M, -)` preserves epimorphisms for `M` free of finite rank. -/
lemma epi_ihom_map_of_iso_biproduct {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) {N N' : Mod C A} (f : N ⟶ N') [Epi f] :
    Epi ((ihom M).map f) := by
  have : Epi ((ihom (⨁ fun _ : Fin n ↦ regular A)).map f) :=
    epi_ihom_biproduct_map _ f fun _ ↦ by
      rw [← NatIso.naturality_2 ihomRegularIso f]
      infer_instance
  rw [← NatIso.naturality_2 (ihomMapIso e).symm f]
  infer_instance

end Hom

end CategoryTheory.Mod
