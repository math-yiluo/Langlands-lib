/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization

/-!
# Matrix calculus for continuous ring coefficients

Source: HRS, Example 3.1, and the finite-biproduct matrix calculus in the existing
continuous field sheaf normal-form proof. No division in the coefficient ring occurs.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal
open scoped CategoryTheory.Obj

attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Profinite.isCommMonObj_continuousMapRingObjOfUniverse

namespace AlgebraicGeometry.ProEtale.ContinuousRingUniverse

/-- Continuous condensed coefficients in the scheme universe.
Source: HRS Example 3.1.
(auxiliary; not a blueprint node) -/
noncomputable abbrev baseRing (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObjOfUniverse T

/-- Pullback of continuous condensed coefficients to a scheme.
Source: HRS Example 3.1; Cartesian coefficients.
(auxiliary; not a blueprint node) -/
noncomputable abbrev baseCoeff (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (X : Scheme.{u}) :=
  condensedRingObj (baseRing T) X

/-- Continuous coefficient matrix calculus. Source: HRS, Example 3.1;
the finite-biproduct calculation in ContinuousFieldMatrixSheafNormalForm.
(auxiliary; not a blueprint node) -/
noncomputable abbrev coeff (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    (V : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology V)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf V E)

/-- Continuous coefficient matrix calculus. Source: HRS, Example 3.1;
the finite-biproduct calculation in ContinuousFieldMatrixSheafNormalForm.
(auxiliary; not a blueprint node) -/
noncomputable def coeffEndFun {E : Type u} [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
    (f : coeff E V ⟶ coeff E V) : C(V, E) :=
  (f.hom.app (op (Scheme.ProEt.mk (𝟙 V))) (ULift.up 1)).down

section Matrix

variable {E : Type u} [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e]

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The matrix of a map of finite free modules in canonical continuous coordinates.
Source: HRS Example 3.1, finite biproduct coordinates.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def freeMatrix
    (f : (⨁ fun _ : ι ↦ Mod.regular R) ⟶ ⨁ fun _ : κ ↦ Mod.regular R) :
    Matrix κ ι C(V, E) :=
  fun i j ↦ coeffEndFun (inv e ≫
    (biproduct.ι (fun _ : ι ↦ Mod.regular R) j ≫ f ≫
      biproduct.π (fun _ : κ ↦ Mod.regular R) i).hom ≫ e)

/-- Entrywise formula for the continuous matrix, without unfolding the coefficient functors.
Source: finite biproduct coordinates, HRS Example 3.1.
(auxiliary; not a blueprint node) -/
theorem freeMatrix_apply
    (f : (⨁ fun _ : ι ↦ Mod.regular R) ⟶ ⨁ fun _ : κ ↦ Mod.regular R)
    (i : κ) (j : ι) :
    freeMatrix e f i j = coeffEndFun (inv e ≫
      (biproduct.ι (fun _ : ι ↦ Mod.regular R) j ≫ f ≫
        biproduct.π (fun _ : κ ↦ Mod.regular R) i).hom ≫ e) := by
  unfold freeMatrix
  rfl

end Matrix

/-- Canonical coefficient pullback with its construction kept folded.
Source: Cartesian coefficients, HRS Example 3.1.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def coefficientComparison (T : Type u) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (upperStar Ab.{u + 1} f).obj (baseCoeff T X) ⟶ baseCoeff T Y :=
  condensedPullbackHom (baseRing T) f

/-- Equation for canonical coefficient pullback.
Source: Cartesian coefficients, HRS Example 3.1.
(auxiliary; not a blueprint node) -/
theorem coefficientComparison_eq (T : Type u) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    coefficientComparison T f = condensedPullbackHom (baseRing T) f := by
  unfold coefficientComparison
  rfl

/-- The canonical coefficient pullback is invertible.
Source: Cartesian coefficients, HRS Example 3.1.
(auxiliary; not a blueprint node) -/
instance coefficientComparison_isIso (T : Type u) [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    IsIso (coefficientComparison T f) := by
  rw [coefficientComparison_eq]
  infer_instance

/-- Canonical continuous realization after scheme pullback. Source: HRS Example 3.1.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def pullbackComparison (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (upperStar Ab.{u + 1} f).obj
      (condensedRingObj (Profinite.continuousMapRingObjOfUniverse T) X) ⟶ coeff T Y :=
  coefficientComparison T f ≫ comparison Y T

/-- Defining equation for the canonical comparison, keeping inverse image folded.
Source: HRS Example 3.1; coefficient functoriality.
(auxiliary; not a blueprint node) -/
theorem pullbackComparison_eq (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    pullbackComparison T f =
      coefficientComparison T f ≫ comparison Y T := by
  unfold pullbackComparison
  rfl

/-- Canonical pullback realization preserves the coefficient structure.
Source: HRS Example 3.1; coefficient functoriality.
(auxiliary; not a blueprint node) -/
theorem pullbackComparison_isIso (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    {X Y : Scheme.{u}} (f : Y ⟶ X) : IsIso (pullbackComparison T f) := by
  have := comparison_isIso Y T
  unfold pullbackComparison
  infer_instance

attribute [instance] pullbackComparison_isIso

/-- The full scalar cokernel class of the evaluated continuous presentation matrix.
This retains torsion. Source: HRS Example 3.1 and the item, steps 2--4.
(auxiliary; not a blueprint node) -/
noncomputable def presentationFiberType (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    {X Y : Scheme.{u}} (f : Y ⟶ X) {m n : ℕ}
    (g : Mod.finiteFree ((upperStar Ab.{u + 1} f).obj
      (baseCoeff T X)) m ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} f).obj
      (baseCoeff T X)) n)
    (y : Y) : Skeleton (ModuleCat.{u} T) :=
  toSkeleton (ModuleCat.of T ((Fin n → T) ⧸ LinearMap.range
    (((freeMatrix (pullbackComparison T f) g).map (fun a ↦ a y)).mulVecLin)))

/-- Continuous entries agree at comparable points, so their cokernels have the same class.
Source: HRS Example 3.1 and the item, step 2.
(auxiliary; not a blueprint node) -/
theorem presentationFiberType_specializes (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [TotallyDisconnectedSpace T] [T2Space T]
    {X Y : Scheme.{u}} (f : Y ⟶ X) {m n : ℕ}
    (g : Mod.finiteFree ((upperStar Ab.{u + 1} f).obj
      (baseCoeff T X)) m ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} f).obj
      (baseCoeff T X)) n)
    {v w : Y} (h : v ⤳ w) :
    presentationFiberType T f g v = presentationFiberType T f g w := by
  have he : (freeMatrix (pullbackComparison T f) g).map (fun a ↦ a v) =
      (freeMatrix (pullbackComparison T f) g).map (fun a ↦ a w) := by
    ext i j
    exact (h.map ((freeMatrix (pullbackComparison T f) g) i j).continuous).eq
  unfold presentationFiberType
  rw [he]

/-- Local constancy of the full scalar cokernel class gives precisely the local
isomorphisms required by continuous Smith reduction. Source: the quotient construction of
`Skeleton`, HRS Example 3.1 and the parent comparison, step 5.
(auxiliary; not a blueprint node) -/
theorem presentationFiberType_local_cokernel_iso
    (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    {X Y : Scheme.{u}} (p : Y ⟶ X) {m n : ℕ}
    (f : Mod.finiteFree ((upperStar Ab.{u + 1} p).obj (baseCoeff T X)) m ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} p).obj (baseCoeff T X)) n)
    (h : IsLocallyConstant (presentationFiberType T p f)) (y : Y) :
    ∃ W : TopologicalSpace.Opens Y, y ∈ W ∧ ∀ z ∈ W, Nonempty
      (((Fin n → T) ⧸ LinearMap.range
          (((freeMatrix (pullbackComparison T p) f).map (fun a ↦ a z)).mulVecLin)) ≃ₗ[T]
        ((Fin n → T) ⧸ LinearMap.range
          (((freeMatrix (pullbackComparison T p) f).map (fun a ↦ a y)).mulVecLin))) := by
  obtain ⟨W, hW, hy, he⟩ := h.exists_open y
  refine ⟨⟨W, hW⟩, hy, fun z hz ↦ ?_⟩
  have hi := (toSkeleton_eq_toSkeleton_iff.mp (he z hz)).some
  exact ⟨hi.toLinearEquiv⟩

namespace MatrixCalculus

private lemma coeff_app_mul (E : Type u) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    (V : Scheme.{u})
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

private lemma coeff_app_one {E : Type u} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
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

private lemma coeff_end_ext {E : Type u} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
    {f g : coeff E V ⟶ coeff E V}
    (hf : (MonObj.mul : coeff E V ⊗ coeff E V ⟶ _) ≫ f =
      coeff E V ◁ f ≫ MonObj.mul)
    (hg : (MonObj.mul : coeff E V ⊗ coeff E V ⟶ _) ≫ g =
      coeff E V ◁ g ≫ MonObj.mul)
    (h : coeffEndFun f = coeffEndFun g) : f = g := by
  apply Sheaf.hom_ext
  ext U s
  rw [coeff_app_mul E V f hf, coeff_app_mul E V g hg, coeff_app_one, coeff_app_one, h]

private noncomputable def coeffMul {E : Type u} [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
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

private lemma coeffMul_linear {E : Type u} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
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

private lemma coeffEndFun_mul {E : Type u} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
    (a : C(V, E)) : coeffEndFun (coeffMul a) = a := by
  change 1 * _ = a
  rw [one_mul]
  rfl

section Matrix

variable {E : Type u} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    {V : Scheme.{u}}
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

private lemma endFun_eq (f : Mod.regular R ⟶ Mod.regular R) :
    endFun e f = coeffEndFun (inv e ≫ f.hom ≫ e) := by
  rfl

end Matrix

end MatrixCalculus

end AlgebraicGeometry.ProEtale.ContinuousRingUniverse
