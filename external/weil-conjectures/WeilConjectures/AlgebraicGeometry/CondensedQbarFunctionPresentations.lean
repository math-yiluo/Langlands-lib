/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Function presentations of finitely presented condensed modules

This isolates coefficient realization and geometric-fibre compatibility. It makes no
local-constancy or finite-freeness assertion. The comparison of condensed coefficients
with the sheafification of bounded functions is supplied as a hypothesis; the parent
proves it using finite-field comparisons and filtered colimits.
-/

@[expose] public section

universe u v w uE

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Evaluation of a finite-extension-valued continuous function at a point.
Source: RefactorInstruction.tex, Section 4, evaluation of coefficient functions
(auxiliary; not a blueprint node). -/
noncomputable def condensedQbarFunctionEval
    {ℓ : ℕ} [Fact ℓ.Prime] {T : Type u} [TopologicalSpace T] (t : T) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ T →+* PadicAlgCl ℓ where
  toFun a := a.1 t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction of bounded continuous functions along a continuous map.
The same finite extension contains all values after restriction.
Source: RefactorInstruction.tex, Section 4, restriction of coefficient functions
(auxiliary; not a blueprint node). -/
noncomputable def condensedQbarFunctionComp
    {ℓ : ℕ} [Fact ℓ.Prime] {T : Type u} [TopologicalSpace T]
    {T' : Type v} [TopologicalSpace T'] (g : C(T', T)) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ T →+*
      PadicAlgCl.finiteIntermediateFieldValued ℓ T' :=
  (((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) g).toRingHom.comp
    (PadicAlgCl.finiteIntermediateFieldValued ℓ T).subtype).codRestrict
      (PadicAlgCl.finiteIntermediateFieldValued ℓ T') (by
        rintro a
        obtain ⟨E, hE, ha⟩ := a.property
        exact ⟨E, hE, fun x ↦ ha (g x)⟩))

attribute [local instance] Abelian.hasFiniteBiproducts

section FiniteFreePullback

variable {C : Type v} [Category.{w} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
  (A : C) (B : D) (F : C ⥤ D) [F.Additive] (e : F.obj A ≅ B)

@[irreducible] private noncomputable def freePullbackIso (n : ℕ) :
    F.obj (⨁ fun _ : Fin n ↦ A) ≅ ⨁ fun _ : Fin n ↦ B :=
  F.mapBiproduct (fun _ : Fin n ↦ A) ≪≫ biproduct.mapIso (fun _ ↦ e)

private lemma freePullbackIso_inv_ι (n : ℕ) (j : Fin n) :
    biproduct.ι (fun _ : Fin n ↦ B) j ≫ (freePullbackIso A B F e n).inv =
      e.inv ≫ F.map (biproduct.ι (fun _ : Fin n ↦ A) j) := by
  simp [freePullbackIso]

private lemma freePullbackIso_hom_π (n : ℕ) (j : Fin n) :
    (freePullbackIso A B F e n).hom ≫ biproduct.π (fun _ : Fin n ↦ B) j =
      F.map (biproduct.π (fun _ : Fin n ↦ A) j) ≫ e.hom := by
  simp [freePullbackIso]

private lemma freePullbackIso_matrix {m n : ℕ}
    (a : Fin m → Fin n → (A ⟶ A)) :
    (freePullbackIso A B F e m).inv ≫ F.map (biproduct.matrix a) ≫
      (freePullbackIso A B F e n).hom =
        biproduct.matrix (fun j k ↦ e.inv ≫ F.map (a j k) ≫ e.hom) := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  simp only [← Category.assoc, freePullbackIso_inv_ι]
  simp only [Category.assoc, freePullbackIso_hom_π]
  simp [← F.map_comp_assoc]

@[irreducible] private noncomputable def freePullbackPresentation
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F]
    {m n : ℕ} {M : C} (ψ : (⨁ fun _ : Fin m ↦ A) ⟶ ⨁ fun _ : Fin n ↦ A)
    (hψ : M ≅ cokernel ψ) :
    F.obj M ≅ cokernel ((freePullbackIso A B F e m).inv ≫ F.map ψ ≫
      (freePullbackIso A B F e n).hom) :=
  F.mapIso hψ ≪≫ PreservesCokernel.iso F ψ ≪≫
    (cokernelEpiComp (freePullbackIso A B F e m).inv
      (F.map ψ ≫ (freePullbackIso A B F e n).hom) ≪≫
        cokernelCompIsIso (F.map ψ) (freePullbackIso A B F e n).hom).symm

@[irreducible] private noncomputable def freePullbackMatrixPresentation
    [HasFiniteColimits C] [HasFiniteColimits D] [PreservesFiniteColimits F]
    {m n : ℕ} {M : C} (a : Fin m → Fin n → (A ⟶ A))
    (hψ : M ≅ cokernel (biproduct.matrix a)) :
    F.obj M ≅ cokernel (biproduct.matrix (fun j k ↦ e.inv ≫ F.map (a j k) ≫ e.hom)) :=
  freePullbackPresentation A B F e (biproduct.matrix a) hψ ≪≫
    cokernelIsoOfEq (freePullbackIso_matrix A B F e a)

end FiniteFreePullback

section FiniteFreeCoordinates

variable {E : Type uE} [Field E]
variable {D : Type v} [Category.{w} D] [Preadditive D] [HasFiniteBiproducts D]
variable (A : D) (F : D ⥤ ModuleCat.{u + 1} E) [F.Additive]
variable (e : F.obj A ≃ₗ[E] E)

/-- Coordinates obtained from the biproduct comparison and the regular-module coordinates. -/
@[irreducible] private noncomputable def finiteFreeEvaluationCoords (k : ℕ) :
    F.obj (⨁ fun _ : Fin k ↦ A) ≃ₗ[E] (Fin k → E) :=
  ((F.mapBiproduct (fun _ : Fin k ↦ A)).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi (fun _ : Fin k ↦ F.obj A)).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ e)

private lemma finiteFreeEvaluationCoords_apply
    {E : Type uE} [Field E]
    {D : Type v} [Category.{w} D] [Preadditive D] [HasFiniteBiproducts D]
    (A : D) (F : D ⥤ ModuleCat.{u + 1} E) [F.Additive] (e : F.obj A ≃ₗ[E] E)
    (k : ℕ) (j : Fin k)
    (x : F.obj (⨁ fun _ : Fin k ↦ A)) :
    finiteFreeEvaluationCoords A F e k x j =
      e ((F.map (biproduct.π (fun _ : Fin k ↦ A) j)) x) := by
  unfold finiteFreeEvaluationCoords
  change e (((ModuleCat.biproductIsoPi _).hom ≫
    ModuleCat.ofHom (LinearMap.proj j)).hom
      ((F.mapBiproduct (fun _ : Fin k ↦ A)).hom x)) = _
  congr 1
  have hp : (ModuleCat.biproductIsoPi (F.obj ∘ (fun _ : Fin k ↦ A))).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π _ j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  have h := F.biproductComparison_π (fun _ : Fin k ↦ A) j
  rw [← hp] at h
  exact congrArg (fun t ↦ t x) h

private lemma finiteFreeEvaluationCoords_symm_single
    {E : Type uE} [Field E]
    {D : Type v} [Category.{w} D] [Preadditive D] [HasFiniteBiproducts D]
    (A : D) (F : D ⥤ ModuleCat.{u + 1} E) [F.Additive] (e : F.obj A ≃ₗ[E] E)
    (k : ℕ) (j : Fin k) (x : E) :
    (finiteFreeEvaluationCoords A F e k).symm (Pi.single j x) =
      F.map (biproduct.ι (fun _ : Fin k ↦ A) j) (e.symm x) := by
  classical
  apply (finiteFreeEvaluationCoords A F e k).injective
  ext i
  rw [LinearEquiv.apply_symm_apply, finiteFreeEvaluationCoords_apply]
  change (Pi.single j x : Fin k → E) i = e ((F.map (biproduct.ι (fun _ : Fin k ↦ A) j) ≫
      F.map (biproduct.π (fun _ : Fin k ↦ A) i))
    (e.symm x))
  rw [← F.map_comp]
  by_cases h : j = i
  · subst i
    simp
  · simp [h]

private lemma finiteFreeEvaluationCoords_matrix
    {E : Type uE} [Field E]
    {D : Type v} [Category.{w} D] [Preadditive D] [HasFiniteBiproducts D]
    (A : D) (F : D ⥤ ModuleCat.{u + 1} E) [F.Additive] (e : F.obj A ≃ₗ[E] E)
    (m n : ℕ)
    (f : (⨁ fun _ : Fin m ↦ A) ⟶ ⨁ fun _ : Fin n ↦ A)
    (M : Matrix (Fin n) (Fin m) E)
    (h : ∀ i j, e (F.map (biproduct.ι _ j ≫ f ≫ biproduct.π _ i) (e.symm 1)) =
      M i j) :
    (finiteFreeEvaluationCoords A F e n).toLinearMap ∘ₗ (F.map f).hom ∘ₗ
      (finiteFreeEvaluationCoords A F e m).symm.toLinearMap = M.mulVecLin := by
  classical
  apply LinearMap.toMatrix'.injective
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change finiteFreeEvaluationCoords A F e n
    (F.map f ((finiteFreeEvaluationCoords A F e m).symm (Pi.single j 1))) i = _
  rw [finiteFreeEvaluationCoords_symm_single, finiteFreeEvaluationCoords_apply]
  simpa only [Functor.map_comp, ModuleCat.comp_apply, LinearMap.toMatrix'_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h i j

end FiniteFreeCoordinates

private lemma finrank_cokernel_of_matrix
    {E : Type uE} [Field E] {A B : ModuleCat.{u + 1} E}
    {m n : ℕ} (a : A ≃ₗ[E] (Fin m → E)) (b : B ≃ₗ[E] (Fin n → E))
    (f : A ⟶ B) (M : Matrix (Fin n) (Fin m) E)
    (hf : b.toLinearMap ∘ₗ f.hom ∘ₗ a.symm.toLinearMap = M.mulVecLin) :
    Module.finrank E (cokernel f : ModuleCat.{u + 1} E) = n - M.rank := by
  have : Module.Finite E B := Module.Finite.of_injective b.toLinearMap b.injective
  have hr : M.rank = Module.finrank E (LinearMap.range f.hom) := by
    change Module.finrank E (LinearMap.range M.mulVecLin) = _
    rw [← hf, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 a.symm.surjective, Submodule.map_top]
    exact b.finrank_map_eq _
  calc
    Module.finrank E (cokernel f : ModuleCat.{u + 1} E) =
        Module.finrank E (B ⧸ LinearMap.range f.hom) :=
      (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv.finrank_eq
    _ = Module.finrank E B - Module.finrank E (LinearMap.range f.hom) :=
      Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank _)
    _ = n - M.rank := by
      rw [b.finrank_eq, Module.finrank_pi, Fintype.card_fin, ← hr]

private theorem matrix_finrank_quotient
    {K : Type uE} [Field K] {n m : ℕ} (M : Matrix (Fin n) (Fin m) K) :
    Module.finrank K ((Fin n → K) ⧸ LinearMap.range M.toLin') = n - M.rank := by
  have hr : M.rank = Module.finrank K (LinearMap.range M.toLin') := by
    simpa only [Matrix.toLin_eq_toLin'] using
      M.rank_eq_finrank_range_toLin (Pi.basisFun K _) (Pi.basisFun K _)
  calc
    _ = Module.finrank K (Fin n → K) - Module.finrank K (LinearMap.range M.toLin') :=
      Nat.eq_sub_of_add_eq (LinearMap.range M.toLin').finrank_quotient_add_finrank
    _ = n - M.rank := by rw [Module.finrank_pi, Fintype.card_fin, ← hr]

private theorem matrix_quotient_equiv_of_finrank_eq
    {K : Type uE} [Field K] {n m : ℕ} (M N : Matrix (Fin n) (Fin m) K)
    (h : Module.finrank K ((Fin n → K) ⧸ LinearMap.range M.toLin') =
      Module.finrank K ((Fin n → K) ⧸ LinearMap.range N.toLin')) :
    Nonempty (((Fin n → K) ⧸ LinearMap.range M.toLin') ≃ₗ[K]
      ((Fin n → K) ⧸ LinearMap.range N.toLin')) :=
  (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq (R := K)).2 h

/-- A fixed presentation has matrices of bounded continuous functions on a refinement,
whose evaluated linear cokernels agree on fibres of the original base, and whose
open restrictions present the module.

Source: RefactorInstruction.tex, Section 4, coefficient realization and geometric-fibre
comparison, steps 1--3 of the finite-matrix refinement argument
(auxiliary; not a blueprint node).
Proof:
1. Unpack the given finite presentation over the coefficient object on Y as the
   cokernel of a map between free modules of fixed ranks m and n. Cover Y by affine
   objects weakly contractible over X.
   Pullback preserves the cokernel and identifies both free modules with their bases.
2. Transport coefficients through the supplied ring-object isomorphism on the original
   noetherian base X. The resulting coefficient sheaf is the sheafification of bounded
   continuous functions. On each weakly contractible affine object, basis evaluation
   identifies sections with bounded continuous functions on its profinite components,
   hence on the scheme. A finite compositum contains all matrix entries. For an empty
   matrix choose the ground field. This realizes B. On every open V the presheaf unit
   gives a ring map from bounded functions to coefficient sections. Localization along
   the weakly etale map V to X, followed by multiplication on the regular module, gives
   the displayed ring homomorphism. The basis calculation and exactness give the
   displayed cokernel isomorphism on V. No noetherianity of a covering object or open
   is used; the global coefficient comparison is applied only on X.
3. At a geometric representative above x in X, evaluate P. Geometric evaluation
   preserves cokernels and finite free modules, so the evaluated presentation is the
   ordinary linear cokernel of the value matrix. This cokernel depends only on x:
   choose an algebraic closure of its residue field and embed it into each algebraically
   closed geometric representative. The extension comparison identifies the evaluated
   modules. Coefficient realization is natural and takes each function to its value
   at the chosen point. Identify a linear cokernel with the quotient by the range to
   obtain the asserted linear equivalence for any two points above x. No dimension or
   rank calculation, local constancy, or local freeness is part of this assertion.
-/
theorem exists_condensedQbar_compatible_function_presentations
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (hcoeff : Nonempty
      (Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        Mon.mk (padicAlgClSheaf X ℓ)))
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj P)) :
    ∃ (C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (n m : ℕ)
      (B : ∀ i : C.I₀,
        Matrix (Fin n) (Fin m) (PadicAlgCl.finiteIntermediateFieldValued ℓ (C.X i))),
      (∀ (i j : C.I₀) (x : C.X i) (y : C.X j),
        (C.f i ≫ f) x = (C.f j ≫ f) y →
        Nonempty
          (((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
            (((B i).map (condensedQbarFunctionEval x)).toLin')) ≃ₗ[PadicAlgCl ℓ]
            ((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
              (((B j).map (condensedQbarFunctionEval y)).toLin')))) ∧
      ∀ (i : C.I₀) (V : (C.X i).Opens),
        ∃ φ : PadicAlgCl.finiteIntermediateFieldValued ℓ V.toScheme →+*
            End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.toScheme)),
          Nonempty
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              ((V.ι ≫ C.f i) ≫ f)).obj P ≅
              cokernel (biproduct.matrix fun j k ↦
                (φ (condensedQbarFunctionComp V.ι.base.hom (B i k j))).asHom)) := by
  classical
  have : WeaklyEtale f := hf
  obtain ⟨q⟩ := exists_condensedQbar_function_coefficients ℓ X hcoeff
  obtain ⟨n, m, ψ, ⟨hψ⟩⟩ := hP
  let A := Y.affineOpenCover
  choose D hD φ hcover hcontract using
    fun j : A.I₀ ↦ Scheme.ProEt.exists_affine_contractible_extension (A.X j)
  let (j : A.I₀) : CommRing (D j) := hD j
  let p (j : A.I₀) := Spec.map (CommRingCat.ofHom (φ j))
  let C₀ := A.openCover.weaken
    (Scheme.zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let E (j : A.I₀) : Scheme.Cover.{0} Scheme.proetalePrecoverage (Spec (A.X j)) :=
    .singleton (p j) (hcover j)
  let C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y := C₀.bind E
  have hC (i : C.I₀) : WeaklyEtale (C.f i) :=
    Scheme.Cover.map_prop (Scheme.Cover.forgetQc C) i
  let U (i : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f i ≫ f)
  have hU (i : C.I₀) : IsAffine (U i).left := by
    change IsAffine (Spec (CommRingCat.of (D i.1)))
    infer_instance
  have wU (i : C.I₀) : PointLanWeaklyContractible
      (U i).left (Scheme.ProEt.mk (𝟙 (U i).left)) := by
    have : WeaklyEtale (𝟙 (C.X i)) := MorphismProperty.id_mem _ _
    intro F G e he
    exact hcontract i.1 (C.X i) (𝟙 (C.X i)) F G e he
  let R (Z : Scheme.{u}) := Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)
  let F (i : C.I₀) := CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i)
  let e (i : C.I₀) := condensedQbarRegularPullbackIso ℓ (C.f i)
  let ψi (i : C.I₀) := (freePullbackIso (R Y) (R (C.X i)) (F i) (e i) m).inv ≫
    (F i).map ψ ≫ (freePullbackIso (R Y) (R (C.X i)) (F i) (e i) n).hom
  have hi (i : C.I₀) : Nonempty
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
        cokernel (ψi i)) := by
    exact ⟨(CondensedRing.upperStarComp _ _ _).app P ≪≫
      freePullbackPresentation (R Y) (R (C.X i)) (F i) (e i) ψ hψ⟩
  choose B₀ hB₀ using fun (i : C.I₀) (k : Fin n) (j : Fin m) ↦
    q.scalar_surjective (U i) (hU i) (wU i)
      (End.of (biproduct.ι (fun _ : Fin m ↦ R (C.X i)) j ≫ ψi i ≫
        biproduct.π (fun _ : Fin n ↦ R (C.X i)) k))
  let B : ∀ i : C.I₀,
      Matrix (Fin n) (Fin m) (PadicAlgCl.finiteIntermediateFieldValued ℓ (C.X i)) := B₀
  have hB (i : C.I₀) (k : Fin n) (j : Fin m) :
      (q.scalar (U i) (B i k j)).asHom =
        biproduct.ι (fun _ : Fin m ↦ R (C.X i)) j ≫ ψi i ≫
          biproduct.π (fun _ : Fin n ↦ R (C.X i)) k := congrArg End.asHom (hB₀ i k j)
  have hmatrix (i : C.I₀) :
      biproduct.matrix (fun j k ↦ (q.scalar (U i) (B i k j)).asHom) = ψi i := by
    simp only [hB]
    exact biproduct.components_matrix _
  have hpres (i : C.I₀) : Nonempty
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
        cokernel (biproduct.matrix (fun j k ↦ (q.scalar (U i) (B i k j)).asHom))) := by
    simpa only [hmatrix] using hi i
  have hd (i : C.I₀) (x : C.X i) :
      Module.finrank (PadicAlgCl ℓ) ((q.fiber (U i) x).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P)) =
      Module.finrank (PadicAlgCl ℓ) ((Fin n → PadicAlgCl ℓ) ⧸
        LinearMap.range ((Matrix.map (B i) (condensedQbarFunctionEval x)).toLin')) := by
    let H := q.fiber (U i) x
    let : H.Additive := q.fiber_additive (U i) x
    let : PreservesFiniteColimits H := q.fiber_colimits (U i) x
    let a := q.fiber_regular (U i) x
    let M := Matrix.map (B i) (condensedQbarFunctionEval x)
    let ψB := biproduct.matrix (fun j k ↦ (q.scalar (U i) (B i k j)).asHom)
    obtain ⟨hp⟩ := hpres i
    let hc := H.mapIso hp ≪≫ PreservesCokernel.iso H ψB
    have hM : (finiteFreeEvaluationCoords (R (C.X i)) H a n).toLinearMap ∘ₗ
        (H.map ψB).hom ∘ₗ
          (finiteFreeEvaluationCoords (R (C.X i)) H a m).symm.toLinearMap = M.mulVecLin := by
      apply finiteFreeEvaluationCoords_matrix
      intro k j
      change a (H.map (biproduct.ι _ j ≫ ψB ≫ biproduct.π _ k) (a.symm 1)) =
        (B i k j).1 x
      dsimp only [ψB]
      rw [biproduct.ι_matrix_assoc, biproduct.lift_π]
      exact q.fiber_scalar (U i) x (B i k j)
    have hfr := finrank_cokernel_of_matrix
      (finiteFreeEvaluationCoords (R (C.X i)) H a m)
      (finiteFreeEvaluationCoords (R (C.X i)) H a n) (H.map ψB) M hM
    exact hc.toLinearEquiv.finrank_eq.trans
      (hfr.trans (matrix_finrank_quotient M).symm)
  refine ⟨C, n, m, B, ?_, ?_⟩
  · intro i j x y hxy
    obtain ⟨eij⟩ := q.fiber_compare_mk (C.f i ≫ f) (C.f j ≫ f) x y hxy
    have he := (eij.app P).toLinearEquiv.finrank_eq
    have hdi := hd i x
    have hdj := hd j y
    have heq := hdi.symm.trans (he.trans hdj)
    exact matrix_quotient_equiv_of_finrank_eq
      (Matrix.map (B i) (condensedQbarFunctionEval x))
      (Matrix.map (B j) (condensedQbarFunctionEval y)) heq
  · intro i V
    have : WeaklyEtale V.ι := inferInstance
    let W : X.ProEt := Scheme.ProEt.mk (V.ι ≫ (C.f i ≫ f))
    obtain ⟨hp⟩ := hpres i
    refine ⟨q.scalar W, ⟨?_⟩⟩
    let G := CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.ι
    let eV := condensedQbarRegularPullbackIso ℓ V.ι
    have heq : (V.ι ≫ C.f i) ≫ f = V.ι ≫ (C.f i ≫ f) := Category.assoc _ _ _
    have hp' := freePullbackMatrixPresentation (R (C.X i)) (R V.toScheme) G eV
      (fun j k ↦ (q.scalar (U i) (B i k j)).asHom) hp
    have hs (j : Fin m) (k : Fin n) := q.scalar_restrict_mk (C.f i ≫ f) V.ι (B i k j)
      (condensedQbarFunctionComp V.ι.base.hom (B i k j)) rfl
    have hc : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
        ((V.ι ≫ C.f i) ≫ f)).obj P ≅ G.obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P) := by
      simpa only [heq, Functor.comp_obj, G] using (CondensedRing.upperStarComp
        (Profinite.padicAlgClRingObj ℓ) V.ι (C.f i ≫ f)).app P
    exact hc ≪≫ hp' ≪≫ cokernelIsoOfEq (by congr 1; funext j k; exact hs j k)

end AlgebraicGeometry.ProEtale
