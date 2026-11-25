/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # A correction cochain from local horseshoe lifts

Source: Stacks Project, Cohomology, Tag 01EQ and Tag 0B8S.
(blueprint: lem-sc-cech-horseshoe-correction-cochain).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

local instance localInst_CechHorseshoeCorrectionCochain_1
    (R : Type u) [Ring R] (J : Type*) [Small.{u} J] :
    HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

private theorem cechMapπ {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (f : F ⟶ G) (n : ℕ) (y : Fin (n + 1) → ι)
    (v : ((cechComplexFunctor U).obj F.presheafModuleCat).X n) :
    TopCat.Presheaf.cechComplexFunctorπ U G.presheafModuleCat n y
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          f.val)).f n v) =
      f.val.app (op (∏ᶜ fun k : Fin (n + 1) ↦ U (y k)))
        (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y v) := by
  exact congrArg (fun m ↦ m v)
    (TopCat.Presheaf.cechComplexFunctor_map_f_π U F.presheafModuleCat
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        f.val) n y)

private theorem moduleCechZero_naturality {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (f : F ⟶ G) :
    moduleCechZero U F ≫
        ((CategoryTheory.cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            f.val)).f 0 =
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f ≫ moduleCechZero U G := by
  apply Pi.hom_ext
  intro y
  dsimp [moduleCechZero, CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor, FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.map]
  simp only [Category.assoc]
  erw [Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
  ext x
  simp only [ModuleCat.comp_apply]
  exact PresheafOfModules.naturality_apply f.val _ x

/-- The two restrictions of a global section to each pairwise intersection agree.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
private theorem moduleCechZero_d {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) :
    moduleCechZero U F ≫
      ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).d 0 1 = 0 := by
  change moduleCechZero U F ≫
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
      ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj F.presheafModuleCat) 0 = 0
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Fin.sum_univ_two]
  simp only [
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  rw [← sub_eq_add_neg]
  apply sub_eq_zero.mpr
  apply Pi.hom_ext
  intro y
  dsimp [moduleCechZero, FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, CosimplicialObject.δ]
  simp only [Category.assoc]
  erw [Pi.lift_comp_π, Pi.lift_comp_π]
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π_assoc]
  congr 1
  erw [← F.presheafModuleCat.map_comp, ← F.presheafModuleCat.map_comp]
  congr 1

private theorem cechMap_injective {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (f : F ⟶ G) [Mono f] (n : ℕ) :
    Function.Injective (((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        f.val)).f n) := by
  intro v w h
  apply TopCat.Presheaf.cechComplexFunctor_ext U F.presheafModuleCat
  intro y
  let E := SheafOfModules.evaluation.{u} X.ringCatSheaf
    (op (∏ᶜ fun k : Fin (n + 1) ↦ U (y k)))
  apply (ModuleCat.mono_iff_injective (E.map f)).mp inferInstance
  change f.val.app _ _ = f.val.app _ _
  rw [← cechMapπ, ← cechMapπ, h]

private theorem cechZeroπ {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) (v : F.val.obj (op ⊤)) (y : Fin 1 → ι) :
    TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat 0 y
      (moduleCechZero U F v) =
      F.val.presheaf.map (homOfLE (le_top : (∏ᶜ fun k : Fin 1 ↦ U (y k)) ≤ ⊤)).op v := by
  change ((moduleCechZero U F ≫
    TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat 0 y) v) = _
  dsimp only [moduleCechZero, TopCat.Presheaf.cechComplexFunctorπ]
  rw [Category.assoc]
  have hh := Pi.lift_comp_π (fun w : Fin 1 → ι ↦
    F.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l ↦ U (w l)))).op) y
  erw [hh]
  rfl

private theorem cech_localSections_d {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (M : X.Modules) (x : ∀ i : ι, M.val.obj (op (U i)))
    (y : Fin 2 → ι) :
    TopCat.Presheaf.cechComplexFunctorπ U M.presheafModuleCat 1 y
      (((cechComplexFunctor U).obj M.presheafModuleCat).d 0 1
        ((ModuleCat.piIsoPi (fun w : Fin 1 → ι ↦ M.presheafModuleCat.obj
          (op (∏ᶜ fun k : Fin 1 ↦ U (w k))))).inv
          (fun w ↦ M.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (w k)) 0).op
            (x (w 0))))) =
      M.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
        M.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0)) := by
  rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul]
  rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv,
    TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
  have h₁ := TopCat.Presheaf.map_map_apply
    (M.presheafModuleCat)
    (Pi.π (fun k : Fin 1 ↦ U ((y ∘ (0 : Fin 2).succAbove) k)) 0).op
    (Pi.lift fun l ↦ Pi.π (fun l : Fin 2 ↦ U (y l))
      ((0 : Fin 2).succAbove l)).op (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1))
  have h₀ := TopCat.Presheaf.map_map_apply
    (M.presheafModuleCat)
    (Pi.π (fun k : Fin 1 ↦ U ((y ∘ (1 : Fin 2).succAbove) k)) 0).op
    (Pi.lift fun l ↦ Pi.π (fun l : Fin 2 ↦ U (y l))
      ((1 : Fin 2).succAbove l)).op (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))
  have h := congrArg₂ (fun a b ↦ a + -b) h₁ h₀
  dsimp [presheafModuleCat, PresheafOfModules.forgetToPresheafModuleCat,
    PresheafOfModules.forgetToPresheafModuleCatObj,
    PresheafOfModules.forgetToPresheafModuleCatObjMap,
    PresheafOfModules.presheaf] at h ⊢
  simp only [AddMonoidHom.mk'_apply,
    sub_eq_add_neg] at h ⊢
  convert h using 1
  rfl

private theorem cochain_comm_apply {R : Type u} [Ring R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (i j : ℕ) (x : K.X i) :
    L.d i j (f.f i x) = f.f j (K.d i j x) :=
  ConcreteCategory.congr_hom (f.comm i j) x

private theorem mapCochain_comp_apply {X : Scheme.{u}} {R : Type u} [Ring R]
    (F : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ)
    {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) (x : (F.obj A).X n) :
    (F.map g).f n ((F.map f).f n x) = (F.map (f ≫ g)).f n x := by
  rw [F.map_comp, HomologicalComplex.comp_f]
  rfl

private theorem mapCochain_zero_apply {X : Scheme.{u}} {R : Type u} [Ring R]
    (F : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ) [F.Additive]
    {A B : X.Modules} (n : ℕ) (x : (F.obj A).X n) :
    (F.map (0 : A ⟶ B)).f n x = 0 := by
  rw [F.map_zero]
  rfl

private theorem moduleCechZero_naturality_apply {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {A B : X.Modules} (f : A ⟶ B) (x : A.val.obj (op ⊤)) :
    (((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        f.val)).f 0) (moduleCechZero U A x) =
      moduleCechZero U B (f.val.app (op ⊤) x) :=
  ConcreteCategory.congr_hom (moduleCechZero_naturality U f) x

private theorem moduleCechZero_d_apply {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (A : X.Modules) (x : A.val.obj (op ⊤)) :
    ((cechComplexFunctor U).obj A.presheafModuleCat).d 0 1 (moduleCechZero U A x) = 0 :=
  ConcreteCategory.congr_hom (moduleCechZero_d U A) x

private theorem cochain_correction_d {R : Type u} [Ring R]
    {A B C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (α : A ⟶ B) (jA : C ⟶ A) (jB : D ⟶ B) (f : C ⟶ D)
    (hsq : jA ≫ α = f ≫ jB) (hinj : Function.Injective (α.f 1))
    (t : A.X 0) (x : D.X 0) (b : B.X 0) (z : C.X 1)
    (ht : α.f 0 t = jB.f 0 x - b) (hx : D.d 0 1 x = f.f 1 z)
    (hb : B.d 0 1 b = 0) : A.d 0 1 t = jA.f 1 z := by
  apply hinj
  rw [← cochain_comm_apply, ht, map_sub, hb, sub_zero, cochain_comm_apply, hx]
  exact (ConcreteCategory.congr_hom (congrArg (fun g ↦ g.f 1) hsq) z).symm

-- The sectionwise and two cochain calculations repeatedly compare categorical product modules.
set_option backward.isDefEq.respectTransparency false in
/-- A Cech zero cochain with prescribed resolution and Cech differentials.
Source: Stacks Project, Cohomology, Tag 01EQ (double-complex proof) and Tag 0B8S.
(blueprint: lem-sc-cech-horseshoe-correction-cochain).

Proof. For each open U_i, the difference aug_B(x_i) - b|U_i lies in the
kernel of beta^0 by the augmentation square, hx and hb. The short exact
row identifies alpha^0 with this kernel, which is computed sectionwise.
Take its unique preimage t_i. Applying alpha^0 shows that the Cech
coboundary of these preimages is aug_A(z): the restrictions of b cancel,
and hz and the first augmentation square identify the remaining terms.
Cancel the sectionwise monomorphism alpha^0. Applying alpha^1 to the
resolution differential of t_i gives -d(b)|U_i, since d aug_B = 0.
Use ha and cancel alpha^1 to obtain -a|U_i. View the family t_i as a
Cech zero cochain (the onefold intersection is canonically U_i), and
use the product projections to express the two equations as identities
in Cech cochain modules. These are precisely the displayed identities.
This also covers empty index types and empty opens:
products and sectionwise kernel identifications remain valid. -/
theorem cech_horseshoe_correction_cochain (X : Scheme.{u})
    (S : ShortComplex X.Modules)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    {ι : Type u} (U : ι → X.Opens)
    (q : S.X₃.val.obj (op ⊤)) (x : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (hx : ∀ i : ι, S.g.val.app (op (U i)) (x i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q)
    (b : (IB.cocomplex.X 0).val.obj (op ⊤))
    (a : (RingedSpace.globalSectionsComplex IA).cycles 1)
    (hb : (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q)
    (ha : (α.f 1).val.app (op ⊤)
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
        (IB.cocomplex.d 0 1).val.app (op ⊤) b)
    (z : ((cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1)
    (hz : ∀ y : Fin 2 → ι,
      S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
        ((Pi.π (fun w : Fin 2 → ι ↦
          S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
          (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
        S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))) :
    ∃ t : ((moduleCechDouble U IA).X 0).X 0,
      (((moduleCechDouble U IA).d 0 1).f 0) t =
        -(moduleCechZero U (IA.cocomplex.X 1))
          ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) ∧
      (((moduleCechDouble U IA).X 0).d 0 1) t =
        ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (IA.ι.f 0).val)).f 1
          (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z) := by
  classical
  let jA : S.X₁ ⟶ IA.cocomplex.X 0 := IA.ι.f 0
  let jB : S.X₂ ⟶ IB.cocomplex.X 0 := IB.ι.f 0
  let F : X.Modules ⥤ CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℕ :=
    SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
      cechComplexFunctor U
  let : F.Additive := cechComplexFunctor_presheafModuleCat_additive X U
  let A₀ := (cechComplexFunctor U).obj (IA.cocomplex.X 0).presheafModuleCat
  let B₀ := (cechComplexFunctor U).obj (IB.cocomplex.X 0).presheafModuleCat
  let B := (cechComplexFunctor U).obj S.X₂.presheafModuleCat
  let x₀ : B.X 0 := (ModuleCat.piIsoPi
    (fun y : Fin 1 → ι ↦ S.X₂.presheafModuleCat.obj
      (op (∏ᶜ fun k : Fin 1 ↦ U (y k))))).inv
    (fun y ↦ S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0)))
  have hx₀ (y : Fin 2 → ι) :
      TopCat.Presheaf.cechComplexFunctorπ U (S.X₂.presheafModuleCat) 1 y (B.d 0 1 x₀) =
        S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0)) := by
    exact cech_localSections_d U S.X₂ x y
  have hdx : B.d 0 1 x₀ = (F.map S.f).f 1
      (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z) := by
    apply TopCat.Presheaf.cechComplexFunctor_ext U S.X₂.presheafModuleCat
    intro y
    change TopCat.Presheaf.cechComplexFunctorπ U S.X₂.presheafModuleCat 1 y
      (B.d 0 1 x₀) = TopCat.Presheaf.cechComplexFunctorπ U S.X₂.presheafModuleCat 1 y
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          S.f.val)).f 1 _)
    rw [hx₀, cechMapπ]
    exact (hz y).symm
  let v : B₀.X 0 := (show B₀.X 0 from (F.map jB).f 0 x₀) -
    (show B₀.X 0 from moduleCechZero U (IB.cocomplex.X 0) b)
  have hιB₀ : jB ≫ β.f 0 = S.g ≫ IC.ι.f 0 := by
    simpa [jB] using congrArg (fun f ↦ f.f 0) hιB
  have hvπ (y : Fin 1 → ι) :
      TopCat.Presheaf.cechComplexFunctorπ U (IB.cocomplex.X 0).presheafModuleCat 0 y v =
      jB.val.app _
        (S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0))) -
      (show (IB.cocomplex.X 0).val.obj (op (∏ᶜ fun k : Fin 1 ↦ U (y k))) from
        (IB.cocomplex.X 0).val.presheaf.map
          (homOfLE (le_top : (∏ᶜ fun k : Fin 1 ↦ U (y k)) ≤ ⊤)).op b) := by
    dsimp only [v]
    rw [map_sub]
    apply congrArg₂ (fun v w : (IB.cocomplex.X 0).val.obj
      (op (∏ᶜ fun k : Fin 1 ↦ U (y k))) ↦ v - w)
    · have hπx : TopCat.Presheaf.cechComplexFunctorπ U S.X₂.presheafModuleCat 0 y x₀ =
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0)) := by
        dsimp only [x₀]
        rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
      exact (cechMapπ U jB 0 y x₀).trans (congrArg (jB.val.app _) hπx)
    · exact cechZeroπ U (IB.cocomplex.X 0) b y
  have hvβ (y : Fin 1 → ι) :
      (β.f 0).val.app (op (∏ᶜ fun k : Fin 1 ↦ U (y k)))
        (TopCat.Presheaf.cechComplexFunctorπ
          U (IB.cocomplex.X 0).presheafModuleCat 0 y v) = 0 := by
    rw [hvπ, map_sub]
    have hi := congrArg (fun f ↦ f.val.app (op (∏ᶜ fun k : Fin 1 ↦ U (y k)))) hιB₀
    have hi' := ConcreteCategory.congr_hom hi
      (S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0)))
    change (β.f 0).val.app _ (jB.val.app _ _) =
      (IC.ι.f 0).val.app _ (S.g.val.app _ _) at hi'
    rw [hi']
    erw [PresheafOfModules.naturality_apply S.g.val,
      PresheafOfModules.naturality_apply (β.f 0).val, hx, hb]
    erw [← PresheafOfModules.naturality_apply (IC.ι.f 0).val]
    have hm := S.X₃.val.map_comp_apply
      (homOfLE (le_top : U (y 0) ≤ ⊤)).op
      (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op q
    erw [← hm]
    apply sub_eq_zero.mpr
    congr 2
  have he (W : X.Opens) := by
    let E := SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)
    let : E.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} X.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op W)).Additive)
    let : PreservesLimits E := inferInstanceAs
      (PreservesLimits (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op W)))
    exact (hrows 0).exact.map_of_mono_of_preservesKernel E (hrows 0).mono_f inferInstance
  choose c hc using fun y : Fin 1 → ι ↦
    (ShortComplex.moduleCat_exact_iff _).mp (he (∏ᶜ fun k : Fin 1 ↦ U (y k)))
      (TopCat.Presheaf.cechComplexFunctorπ
        U (IB.cocomplex.X 0).presheafModuleCat 0 y v) (hvβ y)
  let t : A₀.X 0 := (ModuleCat.piIsoPi
    (fun y : Fin 1 → ι ↦ (IA.cocomplex.X 0).presheafModuleCat.obj
      (op (∏ᶜ fun k : Fin 1 ↦ U (y k))))).inv c
  have hαt : (F.map (α.f 0)).f 0 t = v := by
    apply TopCat.Presheaf.cechComplexFunctor_ext
      U (IB.cocomplex.X 0).presheafModuleCat
    intro y
    change TopCat.Presheaf.cechComplexFunctorπ
      U (IB.cocomplex.X 0).presheafModuleCat 0 y
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (α.f 0).val)).f 0 t) = _
    rw [cechMapπ]
    dsimp only [t]
    rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
    exact hc y
  refine ⟨t, ?_, ?_⟩
  · have : Mono (α.f 1) := (hrows 1).mono_f
    apply cechMap_injective U (α.f 1) 0
    change (F.map (α.f 1)).f 0 ((F.map (IA.cocomplex.d 0 1)).f 0 t) =
      (F.map (α.f 1)).f 0 (-(moduleCechZero U (IA.cocomplex.X 1))
        ((RingedSpace.globalSectionsComplex IA).iCycles 1 a))
    rw [mapCochain_comp_apply, ← α.comm, ← mapCochain_comp_apply, hαt]
    dsimp only [v]
    rw [map_sub, map_neg]
    have haug : jB ≫ IB.cocomplex.d 0 1 = 0 := by
      dsimp only [jB]
      simp
    rw [mapCochain_comp_apply, haug, mapCochain_zero_apply, zero_sub]
    erw [moduleCechZero_naturality_apply U (IB.cocomplex.d 0 1), ← ha,
      moduleCechZero_naturality_apply U (α.f 1)]
  · have : Mono (α.f 0) := (hrows 0).mono_f
    have hιA₀ : jA ≫ α.f 0 = S.f ≫ jB := by
      simpa [jA, jB] using congrArg (fun f ↦ f.f 0) hιA
    apply cochain_correction_d (F.map (α.f 0)) (F.map jA) (F.map jB) (F.map S.f)
      (by rw [← F.map_comp, ← F.map_comp, hιA₀])
      (cechMap_injective U (α.f 0) 1) t x₀
      (moduleCechZero U (IB.cocomplex.X 0) b) _ hαt hdx
    exact moduleCechZero_d_apply U (IB.cocomplex.X 0) b

end AlgebraicGeometry.Scheme.Modules
