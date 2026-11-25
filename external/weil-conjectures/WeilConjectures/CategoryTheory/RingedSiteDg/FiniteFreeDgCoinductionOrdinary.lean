/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.FiniteFreeDgCoinductionData
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! Ordinary finite-free coinduction package.

Source: Stacks Project, `sdga.tex`, Tags 0FRS and finite-basis evaluation
(blueprint: lem-sf-finite-free-dg-coinduction-ordinary-core-stage3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite CategoryTheory.MonoidalClosed MonObj
namespace CategoryTheory.Mod
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  (A : V) [MonObj A] [Closed A]
/-- The action `(a · f)(x) = f (x a)` of `A` on `[A, Y]`. -/
private def localCofreeAct (Y : V) :
    A ⊗ (CategoryTheory.ihom A).obj Y ⟶ (CategoryTheory.ihom A).obj Y :=
  curry ((α_ A A _).inv ≫ μ ▷ _ ≫ (ihom.ev A).app Y)

/-- The uncurried action of `A` on `[A, Y]`. -/
private theorem localUncurry_cofreeAct (Y : V) :
    uncurry (localCofreeAct A Y) = (α_ A A _).inv ≫ μ ▷ _ ≫ (ihom.ev A).app Y := by
  rw [localCofreeAct, uncurry_curry]

/-- The `A`-module structure on `[A, Y]`. -/
@[implicit_reducible]
private def localCofreeModObj (Y : V) : ModObj A ((CategoryTheory.ihom A).obj Y) :=
  .mk' A (localCofreeAct A Y)
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, localUncurry_cofreeAct, uncurry_eq,
        associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, MonObj.mul_one]
      simp)
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, localUncurry_cofreeAct, uncurry_natural_left, uncurry_natural_left,
        localUncurry_cofreeAct, associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]
      have hμ : A ◁ μ ≫ μ = (α_ A A A).inv ≫ μ ▷ A ≫ μ := by
        rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc]
      rw [hμ, associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← uncurry_eq,
        localUncurry_cofreeAct]
      simp only [comp_whiskerRight, Category.assoc]
      monoidal)

/-- The action of `A` on `[A, Y]` is natural in `Y`. -/
private theorem localCofreeAct_natural {Y Y' : V} (f : Y ⟶ Y') :
    localCofreeAct A Y ≫ (CategoryTheory.ihom A).map f =
      A ◁ (CategoryTheory.ihom A).map f ≫ localCofreeAct A Y' := by
  apply uncurry_injective
  rw [uncurry_natural_right, localUncurry_cofreeAct, uncurry_natural_left, localUncurry_cofreeAct]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ihom.ev_naturality]

/-- The cofree module `[A,Y]`, using only the closed structure at A. -/
private def localCofree : V ⥤ Mod V A where
  obj Y :=
    letI := localCofreeModObj A Y
    ⟨(CategoryTheory.ihom A).obj Y⟩
  map {Y Y'} f :=
    letI := localCofreeModObj A Y
    letI := localCofreeModObj A Y'
    homMk (M := ⟨(CategoryTheory.ihom A).obj Y⟩)
      (N := ⟨(CategoryTheory.ihom A).obj Y'⟩) ((CategoryTheory.ihom A).map f)
      (localCofreeAct_natural A f)
  map_id _ := Mod.hom_ext _ _ ((CategoryTheory.ihom A).map_id _)
  map_comp _ _ := Mod.hom_ext _ _ ((CategoryTheory.ihom A).map_comp _ _)

/-- The action on the localCofree module. -/
private theorem localAct_cofree_obj (Y : V) :
    act ((localCofree A).obj Y).X = localCofreeAct A Y := rfl

/-- Evaluation at `1`, `[A, Y] ⟶ Y`. -/
private def localCofreeEval (Y : V) : (CategoryTheory.ihom A).obj Y ⟶ Y :=
  (λ_ _).inv ≫ η ▷ _ ≫ (ihom.ev A).app Y

/-- Evaluating `a · f` at `1` is evaluating `f` at `a`. -/
private theorem localCofreeAct_comp_cofreeEval (Y : V) :
    localCofreeAct A Y ≫ localCofreeEval A Y = (ihom.ev A).app Y := by
  rw [localCofreeEval, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← uncurry_eq,
    localUncurry_cofreeAct, associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
  rw [MonObj.one_mul]
  simp


/-- The morphism of modules `P ⟶ [A, Y]` adjoint to `u : P ⟶ Y`, `p ↦ (a ↦ u (a p))`. -/
private def localToCofree {P : Mod V A} {Y : V} (u : P.X ⟶ Y) : P ⟶ (localCofree A).obj Y :=
  homMk (curry (act P.X ≫ u)) (by
    change act P.X ≫ curry (act P.X ≫ u) = A ◁ curry (act P.X ≫ u) ≫ localCofreeAct A Y
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, localUncurry_cofreeAct,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← uncurry_eq,
      uncurry_curry, mul_act_assoc, Iso.inv_hom_id_assoc])

/-- Uniqueness of the right adjoint identifies internal Hom with dual tensor. -/
private noncomputable def localIhomIsoTensorLeft (Y X : V) [Closed X]
    [ExactPairing Y X] : CategoryTheory.ihom X ≅ MonoidalCategory.tensorLeft Y :=
  (ihom.adjunction X).rightAdjointUniq (tensorLeftAdjunction Y X)

/-- If `Y` is a left dual of `X`, then `(CategoryTheory.ihom X).obj Z ≅ Y ⊗ Z`. -/
private noncomputable def localIhomObjIsoTensor (Y X : V) [Closed X] [ExactPairing Y X] (Z : V) :
    (CategoryTheory.ihom X).obj Z ≅ Y ⊗ Z :=
  (localIhomIsoTensorLeft Y X).app Z

/-- The internal dual of X is its chosen left dual Y. -/
private noncomputable def localIhomObjUnitIso (Y X : V) [Closed X]
    [ExactPairing Y X] : (CategoryTheory.ihom X).obj (𝟙_ V) ≅ Y :=
  localIhomObjIsoTensor Y X (𝟙_ V) ≪≫ ρ_ Y

/-- The canonical comparison is the transpose of tensor-dual evaluation. -/
private noncomputable def localIhomUnitTensorToIhom (X Z : V) [Closed X] :
    (CategoryTheory.ihom X).obj (𝟙_ V) ⊗ Z ⟶ (CategoryTheory.ihom X).obj Z :=
  curry ((α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ V) ▷ Z ≫ (λ_ Z).hom)

/-- The canonical comparison is a composite of dual-tensor isomorphisms. -/
private theorem localIhomUnitTensorToIhom_eq (Y X : V) [Closed X] [ExactPairing Y X] (Z : V) :
    localIhomUnitTensorToIhom X Z =
      (localIhomObjUnitIso Y X).hom ▷ Z ≫ (localIhomObjIsoTensor Y X Z).inv := by
  have h₁ := (ihom.adjunction X).rightAdjointUniq_hom_app_counit (tensorLeftAdjunction Y X) (𝟙_ V)
  have h₂ := (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) Z
  rw [tensorLeftAdjunction_counit_app] at h₁ h₂
  dsimp only [ihom.ihom_adjunction_counit] at h₁ h₂
  simp only [curriedTensor_obj_map] at h₁ h₂
  simp only [localIhomUnitTensorToIhom, curry_eq_iff, uncurry_eq,
    localIhomObjUnitIso, localIhomObjIsoTensor,
    localIhomIsoTensorLeft, Iso.trans_hom, Iso.app_inv, Adjunction.rightAdjointUniq_inv_app,
    Iso.app_hom]
  rw [← h₁, MonoidalCategory.whiskerLeft_comp_assoc, h₂]
  monoidal


private def tensorCofree : V ⥤ Mod V A where
  obj Y := (Mod.tensorRight A Y).obj ((localCofree A).obj (𝟙_ V))
  map f := (tensorRightMap A f).app ((localCofree A).obj (𝟙_ V))
  map_id Y := by apply Mod.hom_ext; exact whiskerLeft_id _ _
  map_comp f g := by apply Mod.hom_ext; exact whiskerLeft_comp _ _ _
private def comparisonHom (Y : V) :
    (tensorCofree A).obj Y ⟶ (localCofree A).obj Y :=
  localToCofree A ((localCofreeEval A (𝟙_ V) ▷ Y) ≫ (λ_ Y).hom)
private theorem comparisonHom_hom (Y : V) :
    (comparisonHom A Y).hom = localIhomUnitTensorToIhom A Y := by
  change curry (((α_ A _ Y).inv ≫ localCofreeAct A (𝟙_ V) ▷ Y) ≫
    localCofreeEval A (𝟙_ V) ▷ Y ≫ (λ_ Y).hom) = _
  rw [Category.assoc, ← comp_whiskerRight_assoc, localCofreeAct_comp_cofreeEval]
  rfl
private def comparisonNat : tensorCofree A ⟶ localCofree A where
  app Y := comparisonHom A Y
  naturality X Y f := by
    apply Mod.hom_ext
    change ((CategoryTheory.ihom A).obj (𝟙_ V) ◁ f) ≫ (comparisonHom A Y).hom =
      (comparisonHom A X).hom ≫ (CategoryTheory.ihom A).map f
    rw [comparisonHom_hom, comparisonHom_hom]
    dsimp only [localIhomUnitTensorToIhom]
    rw [← curry_natural_left, ← curry_natural_right]
    congr 1
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
    erw [leftUnitor_naturality]
    simp only [Category.assoc]
private theorem comparisonNat_iso [HasLeftDual A] : IsIso (comparisonNat A) := by
  have (Y : V) : IsIso ((forget A).map ((comparisonNat A).app Y)) := by
    change IsIso (comparisonHom A Y).hom
    rw [comparisonHom_hom, localIhomUnitTensorToIhom_eq (ᘁA) A]
    infer_instance
  have (Y : V) : IsIso ((comparisonNat A).app Y) :=
    isIso_of_reflects_iso _ (forget A)
  exact NatIso.isIso_of_isIso_app _

private theorem comparison_evaluation (Y : V) :
    A ◁ (comparisonHom A Y).hom ≫ (ihom.ev A).app Y =
      (α_ A ((CategoryTheory.ihom A).obj (𝟙_ V)) Y).inv ≫
        (ihom.ev A).app (𝟙_ V) ▷ Y ≫ (λ_ Y).hom := by
  rw [comparisonHom_hom]
  exact MonoidalClosed.uncurry_curry _
end CategoryTheory.Mod


namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- The free right DG module functor is the existing free module functor
in the reversed tensor category. -/
def finiteFreeDgExtension (A : Algebra O) : Complex O ⥤ Module A :=
  mopFunctor (Complex O) ⋙ Mod.free (mop A.X)

/-- Forgetting free extension gives the displayed right tensor functor. -/
def finiteFreeDgExtensionIso (A : Algebra O) :
    finiteFreeDgExtension A ⋙ underlying A ≅ tensorRight A.X := Iso.refl _

/-- The ordinary free-forgetful adjunction, transported from the monoidal opposite. -/
def finiteFreeDgExtensionAdjunction (A : Algebra O) :
    finiteFreeDgExtension A ⊣ underlying A :=
  (MonoidalOpposite.mopEquiv (Complex O)).toAdjunction.comp (Mod.freeForgetAdjunction (mop A.X))

/-- Free extension acts by multiplication on the right factor. -/
theorem finiteFreeDgExtension_action (A : Algebra O) (M : Complex O) :
    action ((finiteFreeDgExtension A).obj M) ≫
        (finiteFreeDgExtensionIso A).hom.app M =
      ((finiteFreeDgExtensionIso A).hom.app M ▷ A.X) ≫ (α_ M A.X A.X).hom ≫
        (M ◁ (MonObj.mul : A.X ⊗ A.X ⟶ A.X)) := by
  change _ ≫ 𝟙 _ = (𝟙 _ ▷ A.X) ≫ _
  simp only [Category.comp_id, id_whiskerRight, Category.id_comp]
  rfl

/-- The free extension unit inserts the algebra unit. -/
theorem finiteFreeDgExtension_unit (A : Algebra O) (M : Complex O) :
    (finiteFreeDgExtensionAdjunction A).unit.app M ≫
        (finiteFreeDgExtensionIso A).hom.app M =
      (ρ_ M).inv ≫ (M ◁ (MonObj.one : 𝟙_ (Complex O) ⟶ A.X)) := by
  rfl

private theorem right_action_assoc {A : Algebra O} (M : Module A) :
    (action M ▷ A.X) ≫ action M =
      (α_ ((underlying A).obj M) A.X A.X).hom ≫
        (((underlying A).obj M) ◁ (MonObj.mul : A.X ⊗ A.X ⟶ A.X)) ≫ action M := by
  exact congrArg Quiver.Hom.unmop (ModObj.assoc_flip M.X)
private theorem right_action_unit {A : Algebra O} (M : Module A) :
    (((underlying A).obj M) ◁ (MonObj.one : 𝟙_ (Complex O) ⟶ A.X)) ≫ action M =
      (ρ_ ((underlying A).obj M)).hom := by
  exact congrArg Quiver.Hom.unmop (Mod.one_act (A := mop A.X) M.X)
private noncomputable def liftUnderlying {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Module A) (N : Complex O)
    (f : (underlying A).obj M ⟶ N) :
    (underlying A).obj M ⟶ (underlying A).obj (core.coinduction.obj N) :=
  ((core.hom_universal N ((underlying A).obj M)).surjective (action M ≫ f)).choose

private theorem liftUnderlying_eval {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Module A) (N : Complex O)
    (f : (underlying A).obj M ⟶ N) :
    (liftUnderlying core M N f ▷ A.X) ≫ core.evaluation N = action M ≫ f :=
  ((core.hom_universal N ((underlying A).obj M)).surjective (action M ≫ f)).choose_spec

private theorem liftUnderlying_linear {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Module A) (N : Complex O)
    (f : (underlying A).obj M ⟶ N) :
    action M ≫ liftUnderlying core M N f =
      (liftUnderlying core M N f ▷ A.X) ≫ action (core.coinduction.obj N) := by
  apply (core.hom_universal N (((underlying A).obj M) ⊗ A.X)).injective
  dsimp only
  rw [comp_whiskerRight, Category.assoc, liftUnderlying_eval,
    ← Category.assoc, right_action_assoc, Category.assoc,
    comp_whiskerRight, Category.assoc, Category.assoc, core.hom_action]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, liftUnderlying_eval]

private def evaluationOne {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (N : Complex O) :
    (underlying A).obj (core.coinduction.obj N) ⟶ N :=
  (ρ_ ((underlying A).obj (core.coinduction.obj N))).inv ≫
    (((underlying A).obj (core.coinduction.obj N)) ◁
      (MonObj.one : 𝟙_ (Complex O) ⟶ A.X)) ≫ core.evaluation N

private theorem liftUnderlying_evaluationOne {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Module A) (N : Complex O)
    (f : (underlying A).obj M ⟶ N) :
    liftUnderlying core M N f ≫ evaluationOne core N = f := by
  dsimp only [evaluationOne]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    liftUnderlying_eval, reassoc_of% (right_action_unit M), Iso.inv_hom_id_assoc]

private theorem action_evaluationOne {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (N : Complex O) :
    action (core.coinduction.obj N) ≫ evaluationOne core N = core.evaluation N := by
  dsimp only [evaluationOne]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    core.hom_action, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, MonObj.mul_one]
  monoidal

private def liftModule {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Module A) (N : Complex O)
    (f : (underlying A).obj M ⟶ N) : M ⟶ core.coinduction.obj N :=
  Mod.homMk (liftUnderlying core M N f).mop (by
    apply Quiver.Hom.unmop_inj
    exact liftUnderlying_linear core M N f)

private theorem right_linear {A : Algebra O} {M N : Module A} (f : M ⟶ N) :
    action M ≫ (underlying A).map f =
      ((underlying A).map f ▷ A.X) ≫ action N := by
  exact congrArg Quiver.Hom.unmop (Mod.act_hom f)

private theorem liftModule_inverse {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Module A) (N : Complex O)
    (f : M ⟶ core.coinduction.obj N) :
    liftModule core M N ((underlying A).map f ≫ evaluationOne core N) = f := by
  apply Mod.hom_ext
  apply Quiver.Hom.unmop_inj
  apply (core.hom_universal N ((underlying A).obj M)).injective
  change (liftUnderlying core M N _ ▷ A.X) ≫ core.evaluation N =
    ((underlying A).map f ▷ A.X) ≫ core.evaluation N
  rw [liftUnderlying_eval, reassoc_of% (right_linear f), action_evaluationOne]

private def coinductionHomEquiv {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Module A) (N : Complex O) :
    ((underlying A).obj M ⟶ N) ≃ (M ⟶ core.coinduction.obj N) where
  toFun := liftModule core M N
  invFun f := (underlying A).map f ≫ evaluationOne core N
  left_inv f := liftUnderlying_evaluationOne core M N f
  right_inv f := liftModule_inverse core M N f

private theorem evaluationOne_natural {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) {M N : Complex O} (f : M ⟶ N) :
    (underlying A).map (core.coinduction.map f) ≫ evaluationOne core N =
      evaluationOne core M ≫ f := by
  dsimp only [evaluationOne]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    core.evaluation_natural]
  simp only [Category.assoc]

/-- The coinduction adjunction follows from the representing evaluation and action.
Transpose the module action, then evaluate at the unit for the inverse map.
Associativity proves linearity; the action and unit laws prove the two inverses.
Source: Stacks 0FRS (blueprint: lem-sf-finite-free-dg-coinduction). -/
private def coinductionAdjunction {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) : underlying A ⊣ core.coinduction :=
  Adjunction.mkOfHomEquiv
    { homEquiv := coinductionHomEquiv core
      homEquiv_naturality_left_symm := by
        intros X' X Y f g
        change (underlying A).map (f ≫ g) ≫ evaluationOne core Y = _
        rw [Functor.map_comp, Category.assoc]
        rfl
      homEquiv_naturality_right := by
        intros X Y Y' f g
        apply (coinductionHomEquiv core X Y').symm.injective
        change _ ≫ evaluationOne core Y' =
          (underlying A).map (liftModule core X Y f ≫ core.coinduction.map g) ≫
            evaluationOne core Y'
        rw [Functor.map_comp, Category.assoc, evaluationOne_natural]
        change liftUnderlying core X Y' (f ≫ g) ≫ evaluationOne core Y' =
          liftUnderlying core X Y f ≫ evaluationOne core Y ≫ g
        rw [liftUnderlying_evaluationOne, reassoc_of% (liftUnderlying_evaluationOne core X Y f)] }

/-- The counit of the constructed adjunction is evaluation at the algebra unit.
Source: Stacks 0FRS (blueprint: lem-sf-finite-free-dg-coinduction). -/
private theorem coinductionAdjunction_counit {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) (M : Complex O) :
    (coinductionAdjunction core).counit.app M = evaluationOne core M := by
  change (underlying A).map (𝟙 (core.coinduction.obj M)) ≫ evaluationOne core M = _
  rw [Functor.map_id, Category.id_comp]


/-- Representing evaluation and its action equation imply the normalized
forgetful-coinduction adjunction. Transposing a module action gives the forward
Hom map. Evaluation at one is its natural inverse, as proved above.
Source: Stacks 0FRS (blueprint: lem-sf-finite-free-dg-coinduction). -/
theorem finiteFreeDgCoinductionAdjunction_exists {A : Algebra O}
    (core : FiniteFreeCoinductionOrdinaryCore A) :
    ∃ adj : underlying A ⊣ core.coinduction, ∀ M : Complex O,
      adj.counit.app M =
        (ρ_ ((underlying A).obj (core.coinduction.obj M))).inv ≫
          (((underlying A).obj (core.coinduction.obj M)) ◁
            (MonObj.one : 𝟙_ (Complex O) ⟶ A.X)) ≫ core.evaluation M := by
  exact ⟨coinductionAdjunction core, coinductionAdjunction_counit core⟩

private def unitCopiesSuccIso (n : ℕ) :
    ∐ (fun _ : Fin (n+1) ↦ 𝟙_ (Coeff O)) ≅
      (𝟙_ (Coeff O)) ⊞ ∐ (fun _ : Fin n ↦ 𝟙_ (Coeff O)) where
  hom := Sigma.desc (Fin.cases biprod.inl
    (fun i ↦ Sigma.ι (fun _ : Fin n ↦ 𝟙_ (Coeff O)) i ≫ biprod.inr))
  inv := biprod.desc (Sigma.ι (fun _ : Fin (n+1) ↦ 𝟙_ (Coeff O)) 0)
    (Sigma.desc fun i ↦ Sigma.ι (fun _ : Fin (n+1) ↦ 𝟙_ (Coeff O)) i.succ)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp
    · apply Sigma.hom_ext
      intro i
      simp

private theorem finiteCopiesDualizable (n : ℕ) :
    IsDualizable (∐ (fun _ : Fin n ↦ 𝟙_ (Coeff O))) := by
  induction n with
  | zero =>
      apply IsZero.isDualizable
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      exact (isDualizable_unit.biprod ih).of_iso (unitCopiesSuccIso n).symm

private theorem finiteFreeDualizable (A : Algebra O)
    (bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (A.X.X n))
    (finiteFree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (A.X.X n ≅ ∐ (fun _ : Fin r ↦ 𝟙_ (Coeff O)))) :
    IsDualizable A.X := by
  obtain ⟨a,b,h⟩ := bounded
  have : A.X.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).2
    (fun n hn ↦ h n (Or.inl hn))
  have : A.X.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    (fun n hn ↦ h n (Or.inr hn))
  apply CochainComplex.isDualizable_of_isStrictlyGE_of_isStrictlyLE (K := A.X) a b
  intro n
  obtain ⟨r, ⟨e⟩⟩ := finiteFree n
  exact (finiteCopiesDualizable r).of_iso e.symm

/-- Construct the core with the closed structure kept as a parameter during the transport proofs. -/
private theorem coinductionCoreOfClosed (A : Algebra O) [HasLeftDual (mop A.X)]
    [Closed (mop A.X)] : Nonempty (FiniteFreeCoinductionOrdinaryCore A) := by
  let := Mod.comparisonNat_iso (mop A.X)
  refine ⟨{
    coinduction := mopFunctor (Complex O) ⋙ Mod.localCofree (mop A.X)
    evaluation M := ((ihom.ev (mop A.X)).app (mop M)).unmop
    hom_universal := ?_
    evaluation_natural := ?_
    hom_action := ?_
    tensorDual := mopFunctor (Complex O) ⋙ Mod.tensorCofree (mop A.X)
    tensorDualIso := Iso.refl _
    tensorDual_action := ?_
    comparison := Functor.isoWhiskerLeft (mopFunctor (Complex O))
      (asIso (Mod.comparisonNat (mop A.X)))
    comparison_evaluation := ?_ }⟩
  · intro M L
    constructor
    · intro f g h
      apply Quiver.Hom.mop_inj
      apply (MonoidalClosed.uncurry_injective
        (A := mop A.X) (X := mop M) (Y := mop L))
      exact congrArg Quiver.Hom.mop h
    · intro f
      refine ⟨(MonoidalClosed.curry (A := mop A.X) (X := mop M) (Y := mop L)
        f.mop).unmop, ?_⟩
      exact congrArg Quiver.Hom.unmop (MonoidalClosed.uncurry_curry (A := mop A.X) f.mop)
  · intro M N f
    exact congrArg Quiver.Hom.unmop ((ihom.ev (mop A.X)).naturality f.mop)
  · intro M
    exact congrArg Quiver.Hom.unmop (Mod.localUncurry_cofreeAct (mop A.X) (mop M))
  · intro M
    change _ ≫ 𝟙 _ = (𝟙 _ ▷ A.X) ≫ _
    simp only [Category.comp_id, id_whiskerRight, Category.id_comp]
    rfl
  · intro M
    change ((Mod.comparisonHom (mop A.X) (mop M)).hom.unmop ▷ A.X) ≫ _ = _
    simp only [Iso.refl_hom, NatTrans.id_app, id_whiskerRight, Category.id_comp]
    have h := congrArg Quiver.Hom.unmop
      (Mod.comparison_evaluation (mop A.X) (mop M))
    exact h


/-- Ordinary finite-free coinduction with its representing evaluation and tensor-dual map.

Source: Stacks 0FRS; the bounded-dual construction in
`WeilConjectures.Algebra.Homology.Monoidal.Dual` and the cofree construction in
`WeilConjectures.CategoryTheory.Monoidal.Mod.Cofree`.

Proof: Finite coproducts of the tensor unit are dualizable, by induction using
biproducts (including the empty coproduct). The bounded-complex duality theorem
then makes A dualizable. Reverse the tensor order to turn its right dual into a
left dual; this supplies the closed structure needed for this single object A,
without requiring every unbounded complex to be closed. The cofree construction
above transposes multiplication into the right action on the representing Hom.
Currying and uncurrying prove the universal property for every unbounded L and M,
and their naturality proves the functor and evaluation laws.

Tensor the cofree tensor unit with M, with action on its dual factor. The map to
coinduction is the transpose of evaluation at the unit. Its uncurried formula is
exactly tensor-dual evaluation. Uniqueness of right adjoints to tensoring by A
identifies the underlying comparison with the two tensor-dual isomorphisms, hence
it is invertible. Forgetting reflects isomorphisms, so the comparison is a module
isomorphism. Its naturality and evaluation equation are proved above.

(blueprint: lem-sf-finite-free-dg-coinduction-ordinary-core-stage3) -/
theorem finite_free_dg_coinduction_core (A : Algebra O)
    (bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (A.X.X n))
    (finiteFree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (A.X.X n ≅ ∐ (fun _ : Fin r ↦ 𝟙_ (Coeff O)))) :
    Nonempty (FiniteFreeCoinductionOrdinaryCore A) := by
  let : HasRightDual A.X := (finiteFreeDualizable A bounded finiteFree).some
  let : ExactPairing (mop A.Xᘁ) (mop A.X) :=
    { coevaluation' := (η_ A.X A.Xᘁ).mop
      evaluation' := (ε_ A.X A.Xᘁ).mop
      coevaluation_evaluation' := by
        apply Quiver.Hom.unmop_inj
        exact ExactPairing.evaluation_coevaluation A.X A.Xᘁ
      evaluation_coevaluation' := by
        apply Quiver.Hom.unmop_inj
        exact ExactPairing.coevaluation_evaluation A.X A.Xᘁ }
  let : HasLeftDual (mop A.X) := ⟨mop A.Xᘁ⟩
  let : Closed (mop A.X) := closedOfHasLeftDual (mop A.X)
  exact coinductionCoreOfClosed A

end CategoryTheory.RingedSiteDg
