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

import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Local matrix refinement for one finite presentation

The function-presentation comparison supplies the matrix and geometric-fibre data.
The proofs below establish rank local constancy, bounded Gaussian elimination,
and the resulting cokernel isomorphisms.
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace CondensedQbarMatrixRefinement

attribute [local instance] Abelian.hasFiniteBiproducts

section Bounded
variable {ℓ : ℕ} [Fact ℓ.Prime] {T : Type u} [TopologicalSpace T]
private lemma bounded_isUnit (f : PadicAlgCl.finiteIntermediateFieldValued ℓ T)
    (hf : ∀ t, f.1 t ≠ 0) : IsUnit f := by
  let g : C(T, PadicAlgCl ℓ) := ⟨fun t ↦ (f.1 t)⁻¹, f.1.continuous.inv₀ hf⟩
  have hg : g ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ T := by
    obtain ⟨E, hE, ha⟩ := f.property
    exact ⟨E, hE, fun t ↦ E.inv_mem (ha t)⟩
  have h1 : f * ⟨g, hg⟩ = 1 :=
    Subtype.ext (ContinuousMap.ext fun t ↦ mul_inv_cancel₀ (hf t))
  exact ⟨⟨f, ⟨g, hg⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

private noncomputable def sumComplEquiv {κ : Type*} {r : ℕ}
    (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} := by
  classical
  exact (Equiv.sumCompl (· ∈ Set.range ρ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective ρ hρ).symm (Equiv.refl _))

@[simp] private lemma sumComplEquiv_symm_inl {κ : Type*} {r : ℕ}
    (ρ : Fin r → κ) (hρ : Function.Injective ρ) (a : Fin r) :
    (sumComplEquiv ρ hρ).symm (Sum.inl a) = ρ a := by
  simp [sumComplEquiv]

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

private lemma bounded_exists_isOpen_eq_mul
    (M : Matrix κ ι (PadicAlgCl.finiteIntermediateFieldValued ℓ T)) (r : ℕ)
    (V : Set T) (hV : IsOpen V) (hr : ∀ t ∈ V, (M.map (condensedQbarFunctionEval t)).rank = r)
    (t₀ : T) (ht₀ : t₀ ∈ V) :
    ∃ (U : Set T) (ρ : Fin r → κ) (γ : Fin r → ι) (hρ : Function.Injective ρ)
      (hγ : Function.Injective γ), IsOpen U ∧ t₀ ∈ U ∧
      ∀ {T' : Type w} [TopologicalSpace T'] (g : C(T', T)), Set.range g ⊆ U →
        ∃ (P : Matrix κ κ (PadicAlgCl.finiteIntermediateFieldValued ℓ T'))
          (Q : Matrix ι ι (PadicAlgCl.finiteIntermediateFieldValued ℓ T')),
          IsUnit P.det ∧ IsUnit Q.det ∧
          M.map (condensedQbarFunctionComp g) = P * ((Matrix.fromBlocks 1 0 0 0 :
            Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
              (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
                (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q := by
  obtain ⟨ρ, γ, h⟩ := (M.le_rank_map_iff (condensedQbarFunctionEval t₀) r).1 (hr t₀ ht₀).ge
  have hρ : Function.Injective ρ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_row_eq hne (by ext; simp [hab]), map_zero])
  have hγ : Function.Injective γ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_column_eq hne (by intro; simp [hab]), map_zero])
  let δ := (M.submatrix ρ γ).det
  refine ⟨V ∩ {t | δ.1 t ≠ 0}, ρ, γ, hρ, hγ,
    hV.inter (isOpen_compl_singleton.preimage δ.1.continuous), ⟨ht₀, h⟩,
    fun {T'} _ g hg ↦ ?_⟩
  let M' := M.map (condensedQbarFunctionComp g)
  let N := M'.reindex (sumComplEquiv ρ hρ) (sumComplEquiv γ hγ)
  have hN : N = Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks N).symm
  have hB : N.toBlocks₁₁ = (M.submatrix ρ γ).map (condensedQbarFunctionComp g) := by
    ext a b
    simp [N, M', Matrix.toBlocks₁₁]
  have hBu : IsUnit N.toBlocks₁₁.det := by
    rw [hB]
    erw [← RingHom.map_det (condensedQbarFunctionComp g)]
    refine bounded_isUnit _ fun t' ↦ ?_
    exact (hg ⟨t', rfl⟩).2
  let := N.toBlocks₁₁.invertibleOfIsUnitDet hBu
  have hS := Matrix.schur_eq_zero_of_rank_le (fun t' : T' ↦ condensedQbarFunctionEval t')
    (fun x hx ↦ Subtype.ext (ContinuousMap.ext hx)) N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁
    N.toBlocks₂₂ (fun t' ↦ ?_)
  · rw [Matrix.invOf_eq_nonsing_inv] at hS
    obtain ⟨P, Q, hP, hQ, hPQ⟩ :=
      Matrix.exists_eq_mul_fromBlocks_one_zero _ _ _ _ hBu hS
    refine ⟨P.reindex (sumComplEquiv ρ hρ).symm (sumComplEquiv ρ hρ).symm,
      Q.reindex (sumComplEquiv γ hγ).symm (sumComplEquiv γ hγ).symm,
      by simpa using hP, by simpa using hQ, ?_⟩
    have hM' : M' = N.reindex (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm := by
      simp [N]
    change M' = _
    rw [hM', hN, hPQ]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  · rw [← hN]
    have : N.map (condensedQbarFunctionEval t') =
        (M.map (condensedQbarFunctionEval (g t'))).reindex (sumComplEquiv ρ hρ)
          (sumComplEquiv γ hγ) := by
      ext a b
      rfl
    rw [this, Matrix.rank_reindex, hr _ (hg ⟨t', rfl⟩).1, Fintype.card_fin]
end Bounded

section Categorical
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {R : Type w} [CommRing R] (A : C) (φ : R →+* End A)
variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

private noncomputable def matrixHom (M : Matrix κ ι R) :
    (⨁ fun _ : ι ↦ A) ⟶ ⨁ fun _ : κ ↦ A :=
  biproduct.matrix fun j i ↦ (φ (M i j)).asHom

private lemma matrixHom_mul (M : Matrix ν κ R) (N : Matrix κ ι R) :
    matrixHom A φ (M * N) = matrixHom A φ N ≫ matrixHom A φ M := by
  classical
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, matrixHom, biproduct.ι_matrix_assoc, biproduct.matrix_π,
    biproduct.ι_desc, Matrix.mul_apply, map_sum]
  simp only [biproduct.lift_desc, End.sum_asHom, map_mul, End.mul_asHom]

private lemma matrixHom_one [DecidableEq ι] :
    matrixHom A φ (1 : Matrix ι ι R) = 𝟙 _ := by
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, matrixHom, biproduct.ι_matrix_assoc, biproduct.lift_π,
    Category.id_comp, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private lemma matrixHom_isIso [DecidableEq ι] (M : Matrix ι ι R) (h : IsUnit M.det) :
    IsIso (matrixHom A φ M) := by
  refine ⟨matrixHom A φ M⁻¹, ?_, ?_⟩
  · rw [← matrixHom_mul, Matrix.nonsing_inv_mul _ h, matrixHom_one]
  · rw [← matrixHom_mul, Matrix.mul_nonsing_inv _ h, matrixHom_one]

private noncomputable def freeFinIso (ι : Type) [Fintype ι] :
    (⨁ fun _ : ι ↦ A) ≅ ⨁ fun _ : Fin (Fintype.card ι) ↦ A :=
  biproduct.whiskerEquiv (g := fun _ : Fin (Fintype.card ι) ↦ A) (Fintype.equivFin ι)
    fun _ ↦ Iso.refl A

section Block
variable {r : ℕ}
variable (ρ : Fin r → κ) (γ : Fin r → ι)
  (hρ : Function.Injective ρ) (hγ : Function.Injective γ)

private noncomputable def blockMap : (⨁ fun _ : ι ↦ A) ⟶ ⨁ fun _ : κ ↦ A := by
  classical
  exact biproduct.toSubtype _ (· ∈ Set.range γ) ≫
    (biproduct.whiskerEquiv ((Equiv.ofInjective γ hγ).symm.trans (Equiv.ofInjective ρ hρ))
      (fun _ ↦ Iso.refl A)).hom ≫ biproduct.fromSubtype _ (· ∈ Set.range ρ)

private lemma matrixHom_block :
    matrixHom A φ ((Matrix.fromBlocks 1 0 0 0 :
      Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
        (Fin r ⊕ {j // j ∉ Set.range γ}) R).reindex
          (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) =
        blockMap A ρ γ hρ hγ := by
  classical
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, matrixHom, biproduct.ι_matrix_assoc, biproduct.lift_π]
  obtain ⟨x, rfl⟩ := (sumComplEquiv ρ hρ).symm.surjective i
  obtain ⟨y, rfl⟩ := (sumComplEquiv γ hγ).symm.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]
  rcases y with b | ⟨j, hj⟩
  · have h1 : biproduct.ι (fun _ : ι ↦ A) ((sumComplEquiv γ hγ).symm
        (Sum.inl b)) ≫ blockMap A ρ γ hρ hγ = biproduct.ι (fun _ : κ ↦ A) (ρ b) := by
      rw [sumComplEquiv_symm_inl, blockMap,
        biproduct.ι_toSubtype_subtype_assoc (fun _ : ι ↦ A) (· ∈ Set.range γ) ⟨γ b, b, rfl⟩]
      simp only [biproduct.whiskerEquiv_hom, Equiv.trans_apply, Iso.refl_inv,
        biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_fromSubtype,
        Equiv.ofInjective_symm_apply, Equiv.ofInjective_apply]
      exact Category.id_comp _
    rw [← Category.assoc, h1]
    rcases x with a | ⟨i, hi⟩
    · rw [sumComplEquiv_symm_inl]
      by_cases hab : b = a
      · subst hab
        rw [biproduct.ι_π_self]
        simp
      · rw [biproduct.ι_π_ne _ (hρ.ne hab)]
        simp only [Matrix.fromBlocks_apply₁₁]
        rw [Matrix.one_apply_ne (Ne.symm hab), map_zero, End.zero_asHom]
    · have : (sumComplEquiv ρ hρ).symm (Sum.inr ⟨i, hi⟩) = i := by
        simp [sumComplEquiv]
      rw [this, biproduct.ι_π_ne _ (fun h ↦ hi ⟨b, h⟩)]
      simp
  · have : (sumComplEquiv γ hγ).symm (Sum.inr ⟨j, hj⟩) = j := by
      simp [sumComplEquiv]
    rw [this, blockMap]
    simp only [Category.assoc]
    erw [biproduct.ι_toSubtype_assoc, dite_eq_right hj]
    simp only [Limits.zero_comp]
    rcases x with a | ⟨i, hi⟩ <;> simp

private lemma cokernel_block_free : ∃ n : ℕ,
    Nonempty (cokernel (blockMap A ρ γ hρ hγ) ≅ ⨁ fun _ : Fin n ↦ A) := by
  classical
  have : Epi (biproduct.toSubtype (fun _ : ι ↦ A) (· ∈ Set.range γ)) :=
    epi_of_epi_fac (biproduct.fromSubtype_toSubtype _ _)
  let e : (⨁ fun _ : {j // j ∈ Set.range γ} ↦ A) ≅
      ⨁ fun _ : {i // i ∈ Set.range ρ} ↦ A := biproduct.whiskerEquiv
    ((Equiv.ofInjective γ hγ).symm.trans (Equiv.ofInjective ρ hρ))
      (fun _ ↦ Iso.refl A)
  have : Epi (biproduct.toSubtype (fun _ : ι ↦ A) (· ∈ Set.range γ) ≫ e.hom) :=
    inferInstance
  refine ⟨Fintype.card {i : κ // i ∉ Set.range ρ}, ?_⟩
  apply Nonempty.intro
  exact cokernelIsoOfEq (Category.assoc _ _ _).symm ≪≫ cokernelEpiComp _ _ ≪≫
    cokernelBiproductFromSubtypeIso _ _ ≪≫
    freeFinIso A {i : κ // i ∉ Set.range ρ}
end Block

private lemma cokernel_matrix_free_of_factorization [DecidableEq ι] [DecidableEq κ]
    {r : ℕ} (ρ : Fin r → κ) (γ : Fin r → ι)
    (hρ : Function.Injective ρ) (hγ : Function.Injective γ)
    (M : Matrix κ ι R) (P : Matrix κ κ R) (Q : Matrix ι ι R)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hM : M = P * ((Matrix.fromBlocks 1 0 0 0 :
      Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
        (Fin r ⊕ {j // j ∉ Set.range γ}) R).reindex
          (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q) :
    ∃ n : ℕ, Nonempty (cokernel (matrixHom A φ M) ≅ ⨁ fun _ : Fin n ↦ A) := by
  classical
  let := matrixHom_isIso A φ P hP
  let := matrixHom_isIso A φ Q hQ
  obtain ⟨n, ⟨e⟩⟩ := cokernel_block_free A ρ γ hρ hγ
  refine ⟨n, ⟨?_⟩⟩
  have h : matrixHom A φ M = matrixHom A φ Q ≫
      blockMap A ρ γ hρ hγ ≫ matrixHom A φ P := by
    rw [hM, matrixHom_mul, matrixHom_mul, matrixHom_block]
  exact cokernelIsoOfEq h ≪≫ cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ e
end Categorical

section ChangeOfScalars
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
  (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

private noncomputable def extendFreeOfIso (n : ℕ) :
    (Mod.extendScalars φ).obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
  (Mod.extendScalars φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦
      (Mod.extendScalarsIsoComapInv φ).app (Mod.regular R) ≪≫ Mod.regularIsoOfIsIso φ)

private lemma finitelyPresented_extendIso (M : Mod C R) (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M) := by
  classical
  obtain ⟨n, m, ψ, ⟨e⟩⟩ := hM
  let F := Mod.extendScalars φ
  let en := extendFreeOfIso φ n
  let em := extendFreeOfIso φ m
  let ψ' := em.inv ≫ F.map ψ ≫ en.hom
  refine ⟨n, m, ψ', ⟨?_⟩⟩
  exact F.mapIso e ≪≫ PreservesCokernel.iso F ψ ≪≫
    (cokernelEpiComp em.inv (F.map ψ ≫ en.hom) ≪≫ cokernelCompIsIso (F.map ψ) en.hom).symm
end ChangeOfScalars

section FibreDimensions
variable {K : Type u} [Field K] {n m : ℕ}
private lemma matrix_rank_eq_of_quotient_equiv (A B : Matrix (Fin n) (Fin m) K)
    (e : ((Fin n → K) ⧸ LinearMap.range A.toLin') ≃ₗ[K]
      ((Fin n → K) ⧸ LinearMap.range B.toLin')) : A.rank = B.rank := by
  have hA := (LinearMap.range A.toLin').finrank_quotient_add_finrank
  have hB := (LinearMap.range B.toLin').finrank_quotient_add_finrank
  have he := e.finrank_eq
  have ha : A.rank = Module.finrank K (LinearMap.range A.toLin') := by
    simpa only [Matrix.toLin_eq_toLin'] using
      A.rank_eq_finrank_range_toLin (Pi.basisFun K _) (Pi.basisFun K _)
  have hb : B.rank = Module.finrank K (LinearMap.range B.toLin') := by
    simpa only [Matrix.toLin_eq_toLin'] using
      B.rank_eq_finrank_range_toLin (Pi.basisFun K _) (Pi.basisFun K _)
  omega
end FibreDimensions

section Topological
open Topology TopologicalSpace Set
variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

omit [NoetherianSpace X] in
private lemma quasiSober_of_stableGeneralization (S : Set X)
    (hS : StableUnderGeneralization S) : QuasiSober S where
  sober hZ hZclosed := by
    have hZ' := hZ.image Subtype.val continuous_subtype_val.continuousOn
    obtain ⟨η, hη⟩ := QuasiSober.sober hZ'.closure isClosed_closure
    obtain ⟨z, hz⟩ := hZ.nonempty
    have hηz : η ⤳ (z : X) := hη.specializes (subset_closure ⟨z, hz, rfl⟩)
    have hηS : η ∈ S := hS hηz z.property
    refine ⟨⟨η, hηS⟩, ?_⟩
    rw [isGenericPoint_def,
      IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, image_singleton, hη.def]
    rw [← IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hZclosed.closure_eq]

private lemma locallyConstant_of_specializes {α : Type v} {f : X → α}
    (hf : ∀ ⦃x y : X⦄, x ⤳ y → f x = f y) : IsLocallyConstant f := by
  have closed (S : Set X) (hS : ∀ ⦃x y : X⦄, x ⤳ y → (x ∈ S ↔ y ∈ S)) :
      IsClosed S := by
    have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
    have heq : S = ⋃ C ∈ {C ∈ irreducibleComponents X | (C ∩ S).Nonempty}, C := by
      ext y
      simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
      constructor
      · intro hy
        exact ⟨irreducibleComponent y,
          ⟨irreducibleComponent_mem_irreducibleComponents y, y, mem_irreducibleComponent, hy⟩,
          mem_irreducibleComponent⟩
      · rintro ⟨C, ⟨hC, x, hxC, hxS⟩, hyC⟩
        obtain ⟨η, hη⟩ := QuasiSober.sober hC.1
          (isClosed_of_mem_irreducibleComponents C hC)
        exact (hS (hη.specializes hyC)).1 ((hS (hη.specializes hxC)).2 hxS)
    rw [heq]
    exact (hfin.subset fun C hC ↦ hC.1).isClosed_biUnion fun C hC ↦
      isClosed_of_mem_irreducibleComponents C hC.1
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro a
  apply isClosed_compl_iff.mp
  apply closed
  intro x y hxy
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, hf hxy]

private lemma locallyConstant_family_of_fibres
    {I : Type v} {T : I → Type w} [∀ i, TopologicalSpace (T i)]
    (g : ∀ i, T i → X) (hc : ∀ i, Continuous (g i))
    (hg : ∀ i, GeneralizingMap (g i))
    {α : Type*} (q : ∀ i, T i → α)
    (hq : ∀ i {x y : T i}, x ⤳ y → q i x = q i y)
    (hd : ∀ i j (x : T i) (y : T j), g i x = g j y → q i x = q j y) :
    ∀ i, IsLocallyConstant (q i) := by
  classical
  let S : Set X := {x | ∃ i, x ∈ range (g i)}
  have hS : StableUnderGeneralization S := by
    rintro x y hxy ⟨i, z, rfl⟩
    obtain ⟨z', hz', he⟩ := hg i hxy
    exact ⟨i, z', he⟩
  let : QuasiSober S := quasiSober_of_stableGeneralization S hS
  choose k t ht using fun x : S ↦ x.property
  let r : S → α := fun x ↦ q (k x) (t x)
  have hr (i : I) (x : T i) (hx : g i x ∈ S) : r ⟨g i x, hx⟩ = q i x :=
    hd _ _ _ _ (ht _)
  have hrsp {x y : S} (hxy : x ⤳ y) : r x = r y := by
    have hxy' : (x : X) ⤳ (g (k y)) (t y) := by
      rw [ht y]
      exact hxy.map continuous_subtype_val
    obtain ⟨z, hz, he⟩ := hg (k y) hxy'
    have hqz := hq (k y) hz
    have hh : r x = q (k y) z := hd _ _ _ _ ((ht x).trans he.symm)
    exact hh.trans hqz
  have hlc : IsLocallyConstant r := locallyConstant_of_specializes (fun _ _ h ↦ hrsp h)
  intro i
  let g' : T i → S := fun x ↦ ⟨g i x, i, x, rfl⟩
  have he : q i = r ∘ g' := funext fun x ↦ (hr i x _).symm
  rw [he]
  exact hlc.comp_continuous ((hc i).subtype_mk _)

end Topological

/-- Keep cover refinement abstract in the property Q, so reducing a composite cover
never unfolds the concrete extension-of-scalars construction of module pullback. -/
private lemma cover_of_open_local_property {Y : Scheme.{u}}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (Q : ∀ (Z : Scheme.{u}), (Z ⟶ Y) → Prop)
    (hQ : ∀ (i : C.I₀) (t : C.X i),
      ∃ V : (C.X i).Opens, t ∈ V ∧ Q V.toScheme (V.ι ≫ C.f i)) :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i, Q (D.X i) (D.f i) := by
  classical
  obtain ⟨V, hV⟩ := Classical.axiomOfChoice
    (fun i ↦ Classical.axiomOfChoice (hQ i))
  let D (i : C.I₀) : Scheme.Cover.{u} Scheme.proetalePrecoverage (C.X i) :=
    { I₀ := C.X i
      X := fun t ↦ (V i t).toScheme
      f := fun t ↦ (V i t).ι
      mem₀ := Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2
          ⟨fun x ↦ ⟨x, by simpa using (hV i x).1⟩, fun _ ↦ inferInstance⟩) }
  refine ⟨C.bind D, ?_⟩
  rintro ⟨i, t⟩
  exact (hV i t).2

end CondensedQbarMatrixRefinement

open CondensedQbarMatrixRefinement

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A finite presentation on one pro-etale object admits a finite-free refinement.

Source: RefactorInstruction.tex, Section 4, finite-matrix refinement;
Bhatt--Scholze, Definition 6.8.3
(auxiliary; not a blueprint node).
Proof:
1. Extension of scalars along the coefficient isomorphism identifies the given
   presentation with a finite presentation over the coefficient object on Y. The
   canonical finite-field comparison is transported through ULift, on both condensed
   rings and scheme coefficient sheaves; adjunction naturality preserves its evaluation
   equation. These comparisons form a natural isomorphism of finite-field diagrams.
   Passing to their filtered colimits identifies the condensed Qbar coefficient ring
   with the sheafification of bounded continuous functions. The induced map preserves
   multiplication because tensors preserve these colimits and its composites with all
   finite-field inclusions are ring maps. Supplying this ring isomorphism, the
   function-presentation theorem gives a
   cover C, fixed matrix sizes, bounded
   continuous matrices B, and their cokernel presentations after every open restriction.
   It also identifies the linear cokernels at points with the same image in X.
2. Quotient dimension plus range dimension equals the common target dimension n;
   consequently these fibrewise linear equivalences imply equality of matrix ranks.
3. Each C_i to X is flat. Its image is stable under generalization by going-down.
   For the union S of these images, rank descends by step 2 and is invariant under
   specialization: lift a generalization in X to C_i and use that continuous functions
   into a Hausdorff field agree at comparable points. The subspace S is noetherian.
   It is quasi-sober, since a generic point in X of the closure of an irreducible closed
   subset of S generalizes one of its points and hence belongs to S. Its closure in S
   is the original subset. S has finitely many irreducible components. Any subset
   invariant under both specialization and generalization is the union of the components
   it meets. This is a finite union of closed sets; applying it to rank fibres and their
   complements proves that these fibres are clopen. Their preimages in C_i are open.
4. Near any point, intersect its constant-rank neighborhood with the nonvanishing locus
   of a maximal minor. Invert the determinant in the bounded function ring: inversion
   is continuous and the values stay in the same finite field. Schur elimination yields
   B = L diag(1,0) R with invertible determinants. Pointwise rank forces the Schur
   complement to vanish, and point evaluation is jointly injective on functions.
5. Apply the ring homomorphism from functions to endomorphisms of the regular module.
   Matrix multiplication becomes biproduct-map composition, and invertible matrices
   give isomorphisms. The identity block projects onto selected columns and includes
   selected rows. Its cokernel is the complementary-row biproduct, hence finite free.
   Compose the resulting Zariski covers with C. The same argument covers rank zero,
   empty matrices and the empty scheme. No covering scheme is assumed noetherian. -/
theorem exists_condensedQbar_finiteFree_refinement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (((upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj P)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : C.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X i)) r) := by
  classical
  let : WeaklyEtale f := hf
  have hP' : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj P) :=
    finitelyPresented_extendIso
      (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f) _ hP
  obtain ⟨C, n, m, B, hBcoker, hBpres⟩ :=
    exists_condensedQbar_compatible_function_presentations ℓ X Y f hf
      ⟨CondensedQbarCoefficientRealization.globalCoefficientIso ℓ X⟩ P hP'
  have hBfib (i j : C.I₀) (x : C.X i) (y : C.X j)
      (hxy : (C.f i ≫ f) x = (C.f j ≫ f) y) :
      ((B i).map (condensedQbarFunctionEval x)).rank =
        ((B j).map (condensedQbarFunctionEval y)).rank := by
    obtain ⟨e⟩ := hBcoker i j x y hxy
    exact matrix_rank_eq_of_quotient_equiv _ _ e
  have hlc : ∀ i, IsLocallyConstant
      (fun t : C.X i ↦ ((B i).map (condensedQbarFunctionEval t)).rank) := by
    apply locallyConstant_family_of_fibres
      (fun i ↦ (C.f i ≫ f)) (fun i ↦ (C.f i ≫ f).continuous)
    · intro i
      let : WeaklyEtale (C.f i) := C.forgetQc.map_prop i
      exact Flat.generalizingMap (C.f i ≫ f)
    · intro i x y hxy
      have he : (B i).map (condensedQbarFunctionEval x) =
          (B i).map (condensedQbarFunctionEval y) := by
        ext a b
        exact (hxy.map (B i a b).1.continuous).eq
      rw [he]
    · exact hBfib
  have localFree (i : C.I₀) (t : C.X i) :
      ∃ V : (C.X i).Opens, t ∈ V ∧ ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          ((V.ι ≫ C.f i) ≫ f)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.toScheme) r) := by
    let r := ((B i).map (condensedQbarFunctionEval t)).rank
    let V : Set (C.X i) := {x | ((B i).map (condensedQbarFunctionEval x)).rank = r}
    have hV : IsOpen V := (hlc i).isOpen_fiber r
    obtain ⟨U, ρ, γ, hρ, hγ, hU, ht, hfac⟩ :=
      bounded_exists_isOpen_eq_mul (B i) r V hV (fun x hx ↦ hx) t rfl
    let W : (C.X i).Opens := ⟨U, hU⟩
    obtain ⟨φ, ⟨e⟩⟩ := hBpres i W
    obtain ⟨L, R, hL, hR, hLR⟩ := hfac W.ι.base.hom (by simp [W])
    obtain ⟨k, ⟨ek⟩⟩ := cokernel_matrix_free_of_factorization
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) W.toScheme)) φ
      ρ γ hρ hγ _ L R hL hR hLR
    exact ⟨W, ht, k, ⟨e ≪≫ ek⟩⟩
  exact cover_of_open_local_property C
    (fun Z g ↦ ∃ r : ℕ, Nonempty
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (g ≫ f)).obj P ≅
        Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) r)) localFree

end AlgebraicGeometry.ProEtale
