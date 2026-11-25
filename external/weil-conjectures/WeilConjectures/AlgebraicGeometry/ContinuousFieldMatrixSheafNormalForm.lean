/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
public import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination

import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.CategoryTheory.Sites.MonObj

/-!
# Lifting a specified continuous matrix factorization to module sheaves

Source: Hemo--Richarz--Scholbach, Example 3.1, and the Gaussian elimination step
of the accompanying rank/descent argument.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Opposite Functor.LaxMonoidal

private noncomputable abbrev coeff (E : Type u) [NormedField E] (V : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology V)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf V E)

private lemma coeff_app_mul (E : Type u) [NormedField E] (V : Scheme.{u})
    (f : coeff E V ⟶ coeff E V)
    (hf : (MonObj.mul : coeff E V ⊗ coeff E V ⟶ _) ≫ f =
      coeff E V ◁ f ≫ MonObj.mul) (U : V.ProEtᵒᵖ) (s : (coeff E V).obj.obj U) :
    f.hom.app U s = ULift.up (s.down * (f.hom.app U (ULift.up 1)).down) := by
  have h2 := congrArg (fun g ↦ μ (sheafToPresheaf _ _) (coeff E V)
    (coeff E V) ≫ (sheafToPresheaf _ _).map g) hf
  simp only [Functor.map_comp] at h2
  rw [← μ_natural_right_assoc, ← Category.assoc, Sheaf.μ_comp_map_mul] at h2
  have h3 := congrArg (fun g ↦ g.app U (s ⊗ₜ (ULift.up 1 : (coeff E V).obj.obj U))) h2
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h3
  change f.hom.app U (ULift.up (s.down * 1)) =
    ULift.up (s.down * (f.hom.app U (ULift.up 1)).down) at h3
  simpa only [mul_one, ULift.up_down] using h3

private noncomputable def coeffEndFun {E : Type u} [NormedField E] {V : Scheme.{u}}
    (f : coeff E V ⟶ coeff E V) : C(V, E) :=
  (f.hom.app (op (Scheme.ProEt.mk (𝟙 V))) (ULift.up 1)).down

private lemma coeff_app_one {E : Type u} [NormedField E] {V : Scheme.{u}}
    (f : coeff E V ⟶ coeff E V) (U : V.ProEt) :
    f.hom.app (op U) (ULift.up 1) =
      ULift.up ((coeffEndFun f).comp U.hom.base.hom) := by
  let t : U ⟶ Scheme.ProEt.mk (𝟙 V) :=
    MorphismProperty.Over.homMk U.hom (Category.comp_id _)
  have h := NatTrans.naturality_apply f.hom t.op
    (ULift.up 1 : (coeff E V).obj.obj (op (Scheme.ProEt.mk (𝟙 V))))
  have h1 : (coeff E V).obj.map t.op
      (ULift.up 1 : (coeff E V).obj.obj (op (Scheme.ProEt.mk (𝟙 V)))) = ULift.up 1 := rfl
  rw [h1] at h
  rw [h]
  rfl

private lemma coeff_end_ext {E : Type u} [NormedField E] {V : Scheme.{u}}
    {f g : coeff E V ⟶ coeff E V}
    (hf : (MonObj.mul : coeff E V ⊗ coeff E V ⟶ _) ≫ f =
      coeff E V ◁ f ≫ MonObj.mul)
    (hg : (MonObj.mul : coeff E V ⊗ coeff E V ⟶ _) ≫ g =
      coeff E V ◁ g ≫ MonObj.mul)
    (h : coeffEndFun f = coeffEndFun g) : f = g := by
  apply Sheaf.hom_ext
  ext U s
  rw [coeff_app_mul E V f hf, coeff_app_mul E V g hg, coeff_app_one, coeff_app_one, h]

private noncomputable def coeffMul {E : Type u} [NormedField E] {V : Scheme.{u}}
    (a : C(V, E)) : coeff E V ⟶ coeff E V :=
  ⟨{ app U := AddCommGrpCat.ofHom
      { toFun s := ULift.up (s.down * (a.comp U.unop.hom.base.hom : C(U.unop.left, E)))
        map_zero' := by
          change ULift.up (0 * _) = ULift.up (0 : C(U.unop.left, E))
          rw [zero_mul]
        map_add' s t := by exact congrArg ULift.up (add_mul _ _ _) }
     naturality U U' g := by
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       apply ContinuousMap.ext
       intro x
       change s.down (g.unop.left x) * a (U'.unop.hom x) =
         s.down (g.unop.left x) * a (U.unop.hom (g.unop.left x))
       congr 1
       exact congrArg a (by rw [← MorphismProperty.Over.w g.unop]; rfl) }⟩

private lemma coeffMul_linear {E : Type u} [NormedField E] {V : Scheme.{u}}
    (a : C(V, E)) :
    (MonObj.mul : coeff E V ⊗ coeff E V ⟶ _) ≫ coeffMul a =
      coeff E V ◁ coeffMul a ≫ MonObj.mul := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← μ_natural_right_assoc, ← Category.assoc,
    Sheaf.μ_comp_map_mul]
  ext U : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext
  ext s t : 2
  change ULift.up ((s.down * t.down) * _) = ULift.up (s.down * (t.down * _))
  rw [mul_assoc]

private lemma coeffEndFun_mul {E : Type u} [NormedField E] {V : Scheme.{u}}
    (a : C(V, E)) : coeffEndFun (coeffMul a) = a := by
  change 1 * _ = a
  rw [one_mul]
  rfl

section Matrix

variable {E : Type u} [NormedField E] {V : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]

private noncomputable def regConj {S T : Sheaf (Scheme.ProEt.topology V)
    AddCommGrpCat.{u + 1}} [MonObj S] [MonObj T]
    (e : S ⟶ T) [IsIso e] [IsMonHom e] (f : Mod.regular S ⟶ Mod.regular S) :
    Mod.regular T ⟶ Mod.regular T :=
  (Mod.regularIsoOfIsIso e).inv ≫ (Mod.comap (inv e)).map f ≫
    (Mod.regularIsoOfIsIso e).hom

private lemma regConj_comp {S T : Sheaf (Scheme.ProEt.topology V)
    AddCommGrpCat.{u + 1}} [MonObj S] [MonObj T]
    (e : S ⟶ T) [IsIso e] [IsMonHom e] (f g : Mod.regular S ⟶ Mod.regular S) :
    regConj e (f ≫ g) = regConj e f ≫ regConj e g := by
  simp [regConj]

private lemma regConj_injective {S T : Sheaf (Scheme.ProEt.topology V)
    AddCommGrpCat.{u + 1}} [MonObj S] [MonObj T]
    (e : S ⟶ T) [IsIso e] [IsMonHom e] : Function.Injective (regConj e) := by
  intro f g h
  apply Mod.hom_ext
  have h' := congrArg (fun k ↦ e ≫ k.hom ≫ inv e) h
  simpa [regConj] using h'

private lemma regConj_inv {S T : Sheaf (Scheme.ProEt.topology V)
    AddCommGrpCat.{u + 1}} [MonObj S] [MonObj T]
    (e : S ⟶ T) [IsIso e] [IsMonHom e] (f : Mod.regular T ⟶ Mod.regular T) :
    regConj e (regConj (inv e) f) = f := by
  apply Mod.hom_ext
  simp [regConj]

private noncomputable def endFun (f : Mod.regular R ⟶ Mod.regular R) : C(V, E) :=
  coeffEndFun (regConj e f).hom

private lemma endFun_injective : Function.Injective (endFun e) := by
  intro f g h
  apply regConj_injective e
  apply Mod.hom_ext
  exact coeff_end_ext (IsModHom.smul_hom (A := coeff E V) (f := (regConj e f).hom))
    (IsModHom.smul_hom (A := coeff E V) (f := (regConj e g).hom)) h

private lemma endFun_comp (f g : Mod.regular R ⟶ Mod.regular R) :
    endFun e (f ≫ g) = endFun e f * endFun e g := by
  unfold endFun
  rw [regConj_comp]
  change (((regConj e g).hom.hom.app _) ((regConj e f).hom.hom.app _ (ULift.up 1))).down = _
  erw [coeff_app_mul E V _ (IsModHom.smul_hom (A := coeff E V) (f := (regConj e g).hom))]
  rfl

private lemma endFun_id : endFun e (𝟙 (Mod.regular R)) = 1 := by
  have h : regConj e (𝟙 (Mod.regular R)) = 𝟙 _ := by simp [regConj]
  rw [endFun, h]
  rfl

private lemma endFun_zero : endFun e (0 : Mod.regular R ⟶ Mod.regular R) = 0 := by
  have h : regConj e (0 : Mod.regular R ⟶ Mod.regular R) = 0 := by simp [regConj]
  rw [endFun, h]
  rfl

private lemma endFun_add (f g : Mod.regular R ⟶ Mod.regular R) :
    endFun e (f + g) = endFun e f + endFun e g := by
  have h : regConj e (f + g) = regConj e f + regConj e g := by simp [regConj]
  rw [endFun, h]
  rfl

private noncomputable def endMul (a : C(V, E)) : Mod.regular R ⟶ Mod.regular R :=
  regConj (inv e) (Mod.homMk (coeffMul a) (coeffMul_linear a))

private lemma endFun_endMul (a : C(V, E)) : endFun e (endMul e a) = a := by
  unfold endFun endMul
  rw [regConj_inv]
  exact coeffEndFun_mul a

private noncomputable def endFunAddHom :
    (Mod.regular R ⟶ Mod.regular R) →+ C(V, E) where
  toFun := endFun e
  map_zero' := endFun_zero e
  map_add' := endFun_add e

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

private noncomputable def freeMatrix
    (f : (⨁ fun _ : ι ↦ Mod.regular R) ⟶ ⨁ fun _ : κ ↦ Mod.regular R) :
    Matrix κ ι C(V, E) :=
  fun i j ↦ endFun e (biproduct.ι (fun _ : ι ↦ Mod.regular R) j ≫ f ≫
    biproduct.π (fun _ : κ ↦ Mod.regular R) i)

private lemma freeMatrix_comp
    (f : (⨁ fun _ : ι ↦ Mod.regular R) ⟶ ⨁ fun _ : κ ↦ Mod.regular R)
    (g : (⨁ fun _ : κ ↦ Mod.regular R) ⟶ ⨁ fun _ : ν ↦ Mod.regular R) :
    freeMatrix e (f ≫ g) = freeMatrix e g * freeMatrix e f := by
  refine Matrix.ext fun i j ↦ ?_
  have h : biproduct.ι (fun _ : ι ↦ Mod.regular R) j ≫ (f ≫ g) ≫
      biproduct.π (fun _ : ν ↦ Mod.regular R) i =
      ∑ k, (biproduct.ι (fun _ : ι ↦ Mod.regular R) j ≫ f ≫
        biproduct.π (fun _ : κ ↦ Mod.regular R) k) ≫
      (biproduct.ι (fun _ : κ ↦ Mod.regular R) k ≫ g ≫
        biproduct.π (fun _ : ν ↦ Mod.regular R) i) := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    congr 2
    conv_lhs => rw [← Category.id_comp (g ≫ _), ← biproduct.total, Preadditive.sum_comp]
    simp only [Category.assoc]
  rw [freeMatrix, h]
  change endFunAddHom e _ = _
  rw [map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  change endFun e _ = _
  rw [endFun_comp, mul_comm]
  rfl

private lemma freeMatrix_id [DecidableEq ι] :
    freeMatrix e (𝟙 (⨁ fun _ : ι ↦ Mod.regular R)) = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [freeMatrix, Matrix.one_apply, Category.id_comp]
  by_cases h : i = j
  · subst h
    rw [biproduct.ι_π_self, ite_eq_left rfl, endFun_id]
  · rw [biproduct.ι_π_ne _ (Ne.symm h), ite_eq_right h, endFun_zero]

private lemma freeMatrix_injective :
    Function.Injective (freeMatrix e (ι := ι) (κ := κ)) := by
  intro f g h
  refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun i ↦ ?_
  have h' := congrFun (congrFun h i) j
  simpa only [Category.assoc] using endFun_injective e h'

private noncomputable def ofFreeMatrix (N : Matrix κ ι C(V, E)) :
    (⨁ fun _ : ι ↦ Mod.regular R) ⟶ ⨁ fun _ : κ ↦ Mod.regular R :=
  biproduct.matrix fun j i ↦ endMul e (N i j)

private lemma freeMatrix_ofFreeMatrix (N : Matrix κ ι C(V, E)) :
    freeMatrix e (ofFreeMatrix e N) = N := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [freeMatrix, ofFreeMatrix, biproduct.matrix_π, biproduct.ι_desc]
  exact endFun_endMul e _

private lemma ofFreeMatrix_mul (N₁ : Matrix ν κ C(V, E)) (N₂ : Matrix κ ι C(V, E)) :
    ofFreeMatrix e (N₁ * N₂) = ofFreeMatrix e N₂ ≫ ofFreeMatrix e N₁ :=
  freeMatrix_injective e (by rw [freeMatrix_comp, freeMatrix_ofFreeMatrix,
    freeMatrix_ofFreeMatrix, freeMatrix_ofFreeMatrix])

private lemma ofFreeMatrix_one [DecidableEq ι] :
    ofFreeMatrix e (1 : Matrix ι ι C(V, E)) = 𝟙 _ :=
  freeMatrix_injective e (by rw [freeMatrix_ofFreeMatrix, freeMatrix_id])

private lemma isIso_ofFreeMatrix [DecidableEq ι] (P : Matrix ι ι C(V, E))
    (hP : IsUnit P.det) : IsIso (ofFreeMatrix e P) :=
  ⟨ofFreeMatrix e P⁻¹,
    by rw [← ofFreeMatrix_mul, Matrix.nonsing_inv_mul _ hP, ofFreeMatrix_one],
    by rw [← ofFreeMatrix_mul, Matrix.mul_nonsing_inv _ hP, ofFreeMatrix_one]⟩

private noncomputable def sumBiprodIso (A : Mod (Sheaf (Scheme.ProEt.topology V)
    AddCommGrpCat.{u + 1}) R) (ι κ : Type) [Fintype ι] [Fintype κ] :
    (⨁ fun _ : ι ⊕ κ ↦ A) ≅ (⨁ fun _ : ι ↦ A) ⊞ (⨁ fun _ : κ ↦ A) where
  hom := biproduct.desc (Sum.elim
    (fun i ↦ biproduct.ι (fun _ : ι ↦ A) i ≫ biprod.inl)
    (fun k ↦ biproduct.ι (fun _ : κ ↦ A) k ≫ biprod.inr))
  inv := biprod.desc
    (biproduct.desc fun i ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ A) (Sum.inl i))
    (biproduct.desc fun k ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ A) (Sum.inr k))
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    cases i <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro i <;> simp

private noncomputable def splitFreeIso (A : Mod (Sheaf (Scheme.ProEt.topology V)
    AddCommGrpCat.{u + 1}) R) (d : ι ≃ κ ⊕ ν) :
    (⨁ fun _ : ι ↦ A) ≅ (⨁ fun _ : κ ↦ A) ⊞ (⨁ fun _ : ν ↦ A) :=
  biproduct.whiskerEquiv d (fun _ ↦ Iso.refl A) ≪≫ sumBiprodIso A κ ν

private lemma freeMatrix_split {r m n : ℕ}
    (dρ : Fin n ≃ Fin r ⊕ κ) (dγ : Fin m ≃ Fin r ⊕ ι) :
    freeMatrix e ((splitFreeIso (Mod.regular R) dγ).hom ≫
      biprod.map (𝟙 _) 0 ≫ (splitFreeIso (Mod.regular R) dρ).inv) =
    (Matrix.fromBlocks 1 0 0 0 : Matrix (Fin r ⊕ κ) (Fin r ⊕ ι) C(V, E)).reindex
      dρ.symm dγ.symm := by
  classical
  refine Matrix.ext fun i j ↦ ?_
  obtain ⟨x, rfl⟩ := dρ.symm.surjective i
  obtain ⟨y, rfl⟩ := dγ.symm.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, freeMatrix, splitFreeIso, Iso.trans_hom, Iso.trans_inv,
    biproduct.whiskerEquiv_hom, sumBiprodIso]
  rw [biproduct.whiskerEquiv_inv_eq_lift]
  simp only [Category.assoc, biproduct.ι_desc_assoc, Iso.refl_inv, Category.id_comp,
    Equiv.apply_symm_apply, biproduct.lift_π]
  cases y with
  | inl b =>
    cases x with
    | inl a =>
      by_cases hab : b = a
      · subst a
        simp [Category.assoc, endFun_id]
      · simp [Category.assoc, hab, Ne.symm hab, endFun_zero]
    | inr a => simp [Category.assoc, endFun_zero]
  | inr b => cases x <;> simp [Category.assoc, endFun_zero]

omit [Fintype ι] [Fintype κ] in
private lemma matrix_normalForm [Finite ι] [Finite κ] {r m n : ℕ}
    (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (dρ : Fin n ≃ Fin r ⊕ κ) (dγ : Fin m ≃ Fin r ⊕ ι)
    (P : Matrix (Fin n) (Fin n) C(V, E)) (Q : Matrix (Fin m) (Fin m) C(V, E))
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : freeMatrix e f = P *
      (Matrix.fromBlocks 1 0 0 0 : Matrix (Fin r ⊕ κ) (Fin r ⊕ ι) C(V, E)).reindex
        dρ.symm dγ.symm * Q) :
    ∃ (s t : ℕ) (a : Mod.finiteFree R m ≅ Mod.finiteFree R r ⊞ Mod.finiteFree R s)
      (b : Mod.finiteFree R n ≅ Mod.finiteFree R r ⊞ Mod.finiteFree R t),
      f = a.hom ≫ biprod.map (𝟙 _) 0 ≫ b.inv := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  have := isIso_ofFreeMatrix e P hP
  have := isIso_ofFreeMatrix e Q hQ
  let cι : (⨁ fun _ : ι ↦ Mod.regular R) ≅ Mod.finiteFree R (Fintype.card ι) :=
    biproduct.whiskerEquiv (Fintype.equivFin ι) (fun _ ↦ Iso.refl (Mod.regular R))
  let cκ : (⨁ fun _ : κ ↦ Mod.regular R) ≅ Mod.finiteFree R (Fintype.card κ) :=
    biproduct.whiskerEquiv (Fintype.equivFin κ) (fun _ ↦ Iso.refl (Mod.regular R))
  refine ⟨Fintype.card ι, Fintype.card κ,
    asIso (ofFreeMatrix e Q) ≪≫ splitFreeIso (Mod.regular R) dγ ≪≫
      biprod.mapIso (Iso.refl (Mod.finiteFree R r)) cι,
    (asIso (ofFreeMatrix e P)).symm ≪≫ splitFreeIso (Mod.regular R) dρ ≪≫
      biprod.mapIso (Iso.refl (Mod.finiteFree R r)) cκ, ?_⟩
  have hf : f = ofFreeMatrix e Q ≫ ((splitFreeIso (Mod.regular R) dγ).hom ≫
      biprod.map (𝟙 _) 0 ≫ (splitFreeIso (Mod.regular R) dρ).inv) ≫ ofFreeMatrix e P := by
    apply freeMatrix_injective e
    simp only [freeMatrix_comp, freeMatrix_ofFreeMatrix, freeMatrix_split, h,
      Matrix.mul_assoc]
  have hc : (biprod.mapIso (Iso.refl (Mod.finiteFree R r)) cι).hom ≫ biprod.map (𝟙 _) 0 ≫
      (biprod.mapIso (Iso.refl (Mod.finiteFree R r)) cκ).inv = biprod.map (𝟙 _) 0 := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc,
    reassoc_of% hc] using hf

end Matrix

private lemma restriction_unit_app {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    (P : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) (U : V.ProEtᵒᵖ) :
    ((sheafToPresheaf _ AddCommGrpCat.{u + 1}).map
      ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g hg).unit.app P)).app
        U = P.obj.map
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g hg trivial).counit.app
        U.unop).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

private lemma restriction_unit_tensor {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    (P Q : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) :
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g hg).unit.app (P ⊗ Q) =
      ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g hg).unit.app P ⊗ₘ
        (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g hg).unit.app Q) ≫
      μ (lowerStar AddCommGrpCat.{u + 1} g) _ _ ≫
      (lowerStar AddCommGrpCat.{u + 1} g).map
        (μ ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)) P Q) := by
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, ← μ_natural_assoc]
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp, Monoidal.tensorHom_app,
    restriction_unit_app]
  erw [← (μ (sheafToPresheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) P Q).naturality]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
  erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ hg)]
  rfl

private lemma restriction_unit_unit {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g) :
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g hg).unit.app (𝟙_ _) =
      ε (lowerStar AddCommGrpCat.{u + 1} g) ≫
      (lowerStar AddCommGrpCat.{u + 1} g).map
        (ε ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (Scheme.ProEt.topology W) (Scheme.ProEt.topology V))) := by
  apply Sheaf.hom_ext_of_ε_comp
  ext U : 2
  simp only [NatTrans.comp_app, Functor.map_comp, restriction_unit_app]
  erw [← (ε (sheafToPresheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})).naturality]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (F := MorphismProperty.Over.map ⊤ hg)]
  erw [Monoidal.tensorUnit_map, Category.id_comp]
  rfl

private noncomputable abbrev restrictionIso {V W : Scheme.{u}}
    (g : W ⟶ V) (hg : WeaklyEtale g) :
    upperStar AddCommGrpCat.{u + 1} g ≅
      (MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Scheme.ProEt.topology W) (Scheme.ProEt.topology V) :=
  upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g hg

private lemma restriction_monoidal {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g) :
    NatTrans.IsMonoidal (restrictionIso g hg).hom where
  unit := by
    rw [← cancel_epi (Functor.OplaxMonoidal.η (upperStar AddCommGrpCat.{u + 1} g))]
    simp only [Functor.Monoidal.η_ε_assoc]
    apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).injective
    dsimp only [restrictionIso, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_app_unit_comp_map_η]
    exact restriction_unit_unit g hg
  tensor P Q := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} g) P Q)]
    simp only [Functor.Monoidal.δ_μ_assoc]
    apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).injective
    dsimp only [restrictionIso, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_app_tensor_comp_map_δ, Category.assoc,
      ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
      Adjunction.unit_leftAdjointUniq_hom_app]
    exact restriction_unit_tensor g hg P Q

private noncomputable def coeffPullbackIso (E : Type u) [NormedField E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g) :
    (upperStar AddCommGrpCat.{u + 1} g).obj (coeff E V) ≅ coeff E W :=
  (restrictionIso g hg).app (coeff E V)

set_option backward.isDefEq.respectTransparency false in
private lemma coeffPullbackIso_mon (E : Type u) [NormedField E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g) :
    IsMonHom (coeffPullbackIso E g hg).hom := by
  have := restriction_monoidal g hg
  have he := CategoryTheory.pushforwardRingMonObj (MorphismProperty.Over.map ⊤ hg)
    (Scheme.ProEt.topology W) (Scheme.ProEt.topology V) (continuousCoefficientRingSheaf V E)
  change @IsMonHom _ _ _ _ _ ((upperStar AddCommGrpCat.{u + 1} g).monObjObj (coeff E V))
    (Sheaf.monObj_sheafCompose_obj (Scheme.ProEt.topology W)
      (continuousCoefficientRingSheaf W E)) ((restrictionIso g hg).hom.app (coeff E V))
  erw [he]
  exact NatTrans.isMonHom_app (restrictionIso g hg).hom (coeff E V)

attribute [local instance] coeffPullbackIso_mon

private noncomputable def pulledRealization (E : Type u) [NormedField E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ coeff E V) :
    (upperStar AddCommGrpCat.{u + 1} g).obj R ⟶ coeff E W :=
  (upperStar AddCommGrpCat.{u + 1} g).map e ≫ (coeffPullbackIso E g hg).hom

private lemma pulledRealization_isIso (E : Type u) [NormedField E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ coeff E V) [IsIso e] : IsIso (pulledRealization E g hg e) := by
  unfold pulledRealization
  infer_instance

attribute [local instance] pulledRealization_isIso

private lemma pulledRealization_isMonHom (E : Type u) [NormedField E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ coeff E V) [IsMonHom e] : IsMonHom (pulledRealization E g hg e) := by
  unfold pulledRealization
  infer_instance

attribute [local instance] pulledRealization_isMonHom

set_option backward.isDefEq.respectTransparency false in
private lemma endFun_pullback {E : Type u} [NormedField E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ coeff E V) [IsIso e] [IsMonHom e]
    (f : Mod.regular R ⟶ Mod.regular R) :
    endFun (pulledRealization E g hg e) (((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f) =
      (endFun e f).comp g.base.hom := by
  let F := upperStar AddCommGrpCat.{u + 1} g
  let G := (MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)
  let a := (regConj e f).hom
  have hc : (regConj (pulledRealization E g hg e) ((F.mapMod R).map f)).hom = G.map a := by
    change inv (F.map e ≫ (restrictionIso g hg).hom.app (coeff E V)) ≫
      F.map f.hom ≫ F.map e ≫ (restrictionIso g hg).hom.app (coeff E V) = _
    rw [IsIso.inv_comp, ← F.map_inv]
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc]
    rw [Category.assoc (inv e) f.hom e]
    change inv ((restrictionIso g hg).hom.app (coeff E V)) ≫ F.map a ≫
      (restrictionIso g hg).hom.app (coeff E V) = G.map a
    erw [(restrictionIso g hg).hom.naturality a, IsIso.inv_hom_id_assoc]
  change coeffEndFun _ = _
  rw [hc]
  change ((a.hom.app _ (ULift.up 1)).down) = _
  erw [coeff_app_one a]
  rfl

private noncomputable def freePullbackIso {V W : Scheme.{u}} (g : W ⟶ V)
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R] (n : ℕ) :
    ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj (Mod.finiteFree R n) ≅
      Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) n :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).mapBiproduct
    (fun _ : Fin n ↦ Mod.regular R)

set_option backward.isDefEq.respectTransparency false in
private lemma freeMatrix_pullback {E : Type u} [NormedField E]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ coeff E V) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    freeMatrix (pulledRealization E g hg e)
      ((freePullbackIso g R m).inv ≫ ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f ≫
        (freePullbackIso g R n).hom) =
      (freeMatrix e f).map (ContinuousMap.compRightAlgHom ℤ E ⟨g.base.hom, g.continuous⟩) := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [freeMatrix, freePullbackIso, Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
    biproduct.ι_desc_assoc, Category.assoc]
  erw [biproduct.lift_π]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  exact endFun_pullback g hg e _

/-- Lift an explicit continuous matrix block factorization along an open immersion.
Source: steps 6--7 of the rank/descent argument accompanying Hemo--Richarz--Scholbach,
Example 3.1 (auxiliary; not a blueprint node).
Proof: for the continuous-function ring, a regular-module endomorphism is multiplication
by its value at one. Linearity gives this on arbitrary sections; naturality along the
unique map to the terminal site object identifies these values with restrictions of
a global continuous function. Conversely multiplication by a global function is a
linear natural transformation. The assignments are inverse and preserve addition and
composition. Biproduct inclusions and projections extend this correspondence to finite
matrices. Thus P and Q give automorphisms. The chosen injections split source and target
indices into the selected r entries and their finite complements. For the open immersion,
the monoidal inverse-image/localization-restriction comparison identifies the component
functions of the restricted map with composition along g. Transport along e and the
finite-biproduct comparisons gives the two changes of basis a and b; enumerate the finite
complements by Fin of their cardinalities. The explicit matrix factorization then gives
the asserted equality. Rank zero, zero-sized matrices and empty opens are permitted. -/
theorem continuousField_matrix_sheaf_normalForm
    (E : Type u) [NormedField E] {V W : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (g : W ⟶ V) [IsOpenImmersion g]
    (r : ℕ) (ρ : Fin r → Fin n) (γ : Fin r → Fin m)
    (hρ : Function.Injective ρ) (hγ : Function.Injective γ)
    (P : Matrix (Fin n) (Fin n) (C(W, E)))
    (Q : Matrix (Fin m) (Fin m) (C(W, E)))
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : (continuousFieldPresentationMatrix E V e f).map
        (ContinuousMap.compRightAlgHom ℤ E ⟨g.base.hom, g.continuous⟩) =
      P * ((Matrix.fromBlocks 1 0 0 0 :
        Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
          (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
            (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q) :
    ∃ (s t : ℕ)
      (a : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R m) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) s)
      (b : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R n) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) t),
      ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f =
        a.hom ≫ biprod.map (𝟙 _) 0 ≫ b.inv := by
  classical
  let hg : WeaklyEtale g := inferInstance
  let eW := pulledRealization E g hg e
  let fW := (freePullbackIso g R m).inv ≫
    ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f ≫ (freePullbackIso g R n).hom
  have hM : freeMatrix eW fW = P *
      (Matrix.fromBlocks 1 0 0 0 :
        Matrix (Fin r ⊕ {i // i ∉ Set.range ρ}) (Fin r ⊕ {j // j ∉ Set.range γ}) C(W, E)).reindex
          (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm * Q :=
    (freeMatrix_pullback g hg e f).trans h
  obtain ⟨s, t, a, b, hab⟩ := matrix_normalForm eW fW (sumComplEquiv ρ hρ)
    (sumComplEquiv γ hγ) P Q hP hQ hM
  refine ⟨s, t, freePullbackIso g R m ≪≫ a, freePullbackIso g R n ≪≫ b, ?_⟩
  have hab' := congrArg (fun k ↦ (freePullbackIso g R m).hom ≫ k ≫
    (freePullbackIso g R n).inv) hab
  simpa [fW, Category.assoc] using hab'

end AlgebraicGeometry.ProEtale
