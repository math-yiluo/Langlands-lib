/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModuleBaseChange

/-!
# The Čech complex of a module flat over an affine base

Let `f : X ⟶ S` be quasi-compact and separated with `S = Spec A` affine, `U` a finite cover of
`X` by affine opens and `ℱ` a quasi-coherent `𝒪_X`-module flat over `S`. The Čech complex
`Č(U, ℱ)` (`AlgebraicGeometry.Scheme.Modules.cechModuleComplex`) is a complex of flat
`A`-modules computing `Rf_* ℱ` over the affine base, and its formation commutes with every base
change `T = Spec B ⟶ S`. Being exact in degrees `≥ #U` after every base change, its modules of
cycles are flat in degrees `≥ #U - 1`
(`AlgebraicGeometry.Scheme.Modules.flat_ker_d_cechModuleComplex`), so that its truncation in
degrees `≤ #U - 1` is a bounded complex of flat `A`-modules quasi-isomorphic to it, compatibly
with every base change (`AlgebraicGeometry.Scheme.Modules.quasiIso_map_baseChange_ιTruncLE`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- The finite intersections of affine opens of a scheme separated over an affine scheme are
affine. -/
lemma isAffineOpen_iInf_of_isSeparated [IsAffine S] [IsSeparated f]
    (hU : ∀ i, IsAffineOpen (U i)) (k : ℕ) (y : Fin (k + 1) → ι) :
    IsAffineOpen (⨅ l, U (y l)) := by
  classical
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  have h := IsAffineOpen.biInf ((Finset.univ.image y : Finset ι) : Set ι)
    (Finset.finite_toSet _) (by simpa using Set.range_nonempty y) (fun i _ ↦ hU i)
  convert h using 1
  refine le_antisymm (le_iInf₂ fun i hi ↦ ?_)
    (le_iInf fun l ↦ iInf₂_le (y l) (by simp))
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hi
  exact iInf_le _ l

/-- Two `A`-modules isomorphic as `A`-modules give the same exactness after tensoring. -/
lemma exact_lTensor_iff_of_linearEquiv {A : Type u} [CommRing A] {P P' M₁ M₂ M₃ : Type u}
    [AddCommGroup P] [Module A P] [AddCommGroup P'] [Module A P'] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃] (e : P ≃ₗ[A] P')
    (d₁ : M₁ →ₗ[A] M₂) (d₂ : M₂ →ₗ[A] M₃) :
    Function.Exact (d₁.lTensor P) (d₂.lTensor P) ↔ Function.Exact (d₁.lTensor P') (d₂.lTensor P') :=
  (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e.rTensor M₁) (e₂ := e.rTensor M₂)
    (e₃ := e.rTensor M₃) (by ext; simp) (by ext; simp)).symm

variable [IsAffine S] [IsSeparated f] [Fintype ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i))
  (hU' : iSup U = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hU hU' in
/-- **The Čech complex is exact in high degrees after any affine base change.** For a cartesian
square with `T = Spec B` affine, `B ⊗[A] Č(U, ℱ) ≅ Č(g'⁻¹ U, g'^* ℱ)` is exact in degrees
`≥ #ι`. -/
lemma exactAt_baseChange_cechModuleComplex {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X}
    {f' : Y ⟶ T} (H : IsPullback g' f' f g) [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)]
    (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) (k : ℤ) (hk : Fintype.card ι ≤ k) :
    (((ModuleCat.baseChange Γ(S, ⊤) Γ(T, ⊤)).mapHomologicalComplex _).obj
      (cechModuleComplex f ℱ U)).ExactAt k := by
  have : IsSeparated f' := MorphismProperty.of_isPullback H ‹IsSeparated f›
  refine HomologicalComplex.ExactAt.of_iso ?_
    (cechModuleComplexBaseChangeIso H ℱ hg U (isAffineOpen_iInf_of_isSeparated f U hU)).symm
  refine exactAt_cechModuleComplex f' _ _
    (fun i ↦ isAffineOpen_preimage_of_isPullback H (isAffineOpen_top S) (by simp) (by simp)
      (hU i)) ?_ k (Or.inr hk)
  rw [← Scheme.Hom.preimage_iSup, hU', Scheme.Hom.preimage_top]

include hU hU' in
/-- **The Čech complex is exact in high degrees modulo any ideal.** For an ideal `I` of
`A = Γ(S, ⊤)`, the complex `A/I ⊗[A] Č(U, ℱ)` is exact in degrees `≥ #ι`: it is the Čech complex
of the restriction of `ℱ` to the closed subscheme `X ×_S Spec (A/I)`. -/
lemma exact_lTensor_quotient_cechModuleComplex (I : Ideal Γ(S, ⊤)) (k : ℤ)
    (hk : Fintype.card ι ≤ k + 1) :
    Function.Exact (((cechModuleComplex f ℱ U).d k (k + 1)).hom.lTensor (Γ(S, ⊤) ⧸ I))
      (((cechModuleComplex f ℱ U).d (k + 1) (k + 1 + 1)).hom.lTensor (Γ(S, ⊤) ⧸ I)) := by
  let φ : Γ(S, ⊤) ⟶ CommRingCat.of (Γ(S, ⊤) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let g : Spec (CommRingCat.of (Γ(S, ⊤) ⧸ I)) ⟶ S := Spec.map φ ≫ S.isoSpec.inv
  let : Algebra Γ(S, ⊤) Γ(Spec (CommRingCat.of (Γ(S, ⊤) ⧸ I)), ⊤) := g.appTop.hom.toAlgebra
  have h := exactAt_baseChange_cechModuleComplex f ℱ U hU hU' (IsPullback.of_hasPullback f g)
    rfl (k + 1) hk
  rw [CochainComplex.exactAt_baseChange_iff] at h
  refine (exact_lTensor_iff_of_linearEquiv ?_ _ _).2 h
  -- `Γ(Spec (A/I), ⊤) ≅ A/I` as `A`-modules
  have h₁ : S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(S, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv]
    rfl
  have h₂ : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso Γ(S, ⊤)).hom ≫ φ ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have hg (a : Γ(S, ⊤)) : g.appTop a = (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk I a) := by
    change (S.isoSpec.inv.appTop ≫ (Spec.map φ).appTop) a = _
    rw [h₂, ← Category.assoc, ← Category.assoc, h₁, Category.id_comp]
    rfl
  exact { (Scheme.ΓSpecIso (CommRingCat.of (Γ(S, ⊤) ⧸ I))).commRingCatIsoToRingEquiv.symm with
    map_smul' a x := by
      change (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk I a * x) =
        g.appTop a * (Scheme.ΓSpecIso _).inv x
      rw [map_mul, hg] }

include hU hU' in
/-- **Flatness of the Čech cycles in high degrees.** If `ℱ` is flat over `S`, the modules of
cycles of the Čech complex `Č(U, ℱ)` are flat in degrees `≥ #ι - 1`. In high degrees this
follows from the exactness of `A/I ⊗[A] Č(U, ℱ)` for every ideal `I`
(`AlgebraicGeometry.Scheme.Modules.exact_lTensor_quotient_cechModuleComplex`), and it propagates
down to degree `#ι - 1` along the exact part of the complex. -/
theorem flat_ker_d_cechModuleComplex (hℱ : ℱ.IsFlatOver f) (k : ℤ)
    (hk : (Fintype.card ι : ℤ) - 1 ≤ k) :
    Module.Flat Γ(S, ⊤) (LinearMap.ker ((cechModuleComplex f ℱ U).d k (k + 1)).hom) := by
  have hC := flat_cechModuleComplex_X f ℱ U hℱ (isAffineOpen_iInf_of_isSeparated f U hU)
  have hex (j : ℤ) (hj : (Fintype.card ι : ℤ) ≤ j) : (cechModuleComplex f ℱ U).ExactAt j :=
    exactAt_cechModuleComplex f ℱ U hU hU' j (Or.inr hj)
  exact CochainComplex.flat_ker_d_of_exactAt hC hex
    (CochainComplex.flat_ker_d_of_exact_lTensor_quotient hC hex fun I j hj ↦
      exact_lTensor_quotient_cechModuleComplex f ℱ U hU hU' I j hj) k hk

/-- The truncation `τ^{≤ #ι - 1} Č(U, ℱ)` of the Čech complex: a bounded complex representing
`Rf_* ℱ` over the affine base. -/
noncomputable abbrev cechModuleComplexTrunc : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ :=
  (cechModuleComplex f ℱ U).truncLE ((Fintype.card ι : ℤ) - 1)

instance : (cechModuleComplexTrunc f ℱ U).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have : (0 : ℤ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    lia
  exact (((cechModuleComplex f ℱ U).truncLEXIso _ i (by lia)).isZero_iff).2
    ((cechModuleComplex f ℱ U).isZero_of_isStrictlyGE 0 i hi)

include hU hU' in
/-- The truncation of the Čech complex is quasi-isomorphic to it. -/
lemma quasiIso_ιTruncLE_cechModuleComplex :
    QuasiIso ((cechModuleComplex f ℱ U).ιTruncLE ((Fintype.card ι : ℤ) - 1)) := by
  have : (cechModuleComplex f ℱ U).IsLE ((Fintype.card ι : ℤ) - 1) :=
    ((cechModuleComplex f ℱ U).isLE_iff _).2 fun i hi ↦
      exactAt_cechModuleComplex f ℱ U hU hU' i (Or.inr (by lia))
  infer_instance

include hU hU' in
/-- The truncation of the Čech complex of a module flat over the base is a complex of flat
modules. -/
lemma flat_cechModuleComplexTrunc_X (hℱ : ℱ.IsFlatOver f) (i : ℤ) :
    Module.Flat Γ(S, ⊤) ((cechModuleComplexTrunc f ℱ U).X i) :=
  CochainComplex.flat_truncLE_X _ _
    (flat_cechModuleComplex_X f ℱ U hℱ (isAffineOpen_iInf_of_isSeparated f U hU))
    (flat_ker_d_cechModuleComplex f ℱ U hU hU' hℱ _ le_rfl) i

include hU hU' in
/-- **Base change of the truncated Čech complex.** If `ℱ` is flat over `S`, the inclusion of the
truncation `τ^{≤ #ι - 1} Č(U, ℱ) ⟶ Č(U, ℱ)` stays a quasi-isomorphism after any base change
`A ⟶ B`. -/
theorem quasiIso_map_baseChange_ιTruncLE_cechModuleComplex (hℱ : ℱ.IsFlatOver f)
    (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] :
    QuasiIso (((ModuleCat.baseChange Γ(S, ⊤) B).mapHomologicalComplex _).map
      ((cechModuleComplex f ℱ U).ιTruncLE ((Fintype.card ι : ℤ) - 1))) :=
  CochainComplex.quasiIso_map_baseChange_ιTruncLE B _ _
    (flat_cechModuleComplex_X f ℱ U hℱ (isAffineOpen_iInf_of_isSeparated f U hU))
    (fun k hk ↦ exactAt_cechModuleComplex f ℱ U hU hU' k (Or.inr (by lia)))
    (flat_ker_d_cechModuleComplex f ℱ U hU hU' hℱ)

end AlgebraicGeometry.Scheme.Modules
