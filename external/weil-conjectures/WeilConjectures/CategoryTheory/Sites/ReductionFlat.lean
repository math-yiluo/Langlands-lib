/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Algebra.Category.ModuleCat.QuotSMulTop
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import WeilConjectures.Mathlib.RingTheory.Ideal.Operations

/-!
# Reduction of flat sheaves of modules modulo an ideal

Let `R` be a Noetherian commutative ring, `I` an ideal and `F` a sheaf of `R`-modules on a site.
Its reduction `F / I F`, the sheafification of `U ↦ F(U) / I F(U)`
(`CategoryTheory.Sheaf.quotSMulTop`), is a sheaf of `R ⧸ I`-modules. If `F` is flat, so is its
reduction (`CategoryTheory.Sheaf.flat_quotSMulTop_obj`): a linear relation between sections of
`F / I F` lifts, after adding the generators of `I` as coefficients, to a linear relation
between sections of `F`, which is locally trivial since `F` is flat. Restricting the scalars of
the reduction back to `R` gives `F ⊗ (R ⧸ I)`
(`CategoryTheory.Sheaf.quotSMulTopCompRestrictScalarsIso`).

## Main results

- `CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp_quotSMulTop`: reduction modulo `I`
  preserves locally trivial relations.
- `CategoryTheory.Sheaf.flat_quotSMulTop_obj`: the reduction of a flat sheaf is flat.
- `CategoryTheory.Sheaf.quotSMulTopCompRestrictScalarsIso`: `ι (F / I F) ≅ F ⊗ (R ⧸ I)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped Pointwise

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Type (u + 1)} [CommRing R]

/-- **Reduction modulo `I` preserves locally trivial relations.** If `P` is a presheaf of modules
over a Noetherian ring `R` with locally trivial relations, so is its reduction
`U ↦ P(U) / I P(U)`, as a presheaf of `R ⧸ I`-modules. A relation between reductions of sections
`yⱼ` lifts to a relation `∑ⱼ eₗⱼ yⱼ = ∑ₖ γₖ wₗₖ` in `P`, with `γ` generators of `I`, which is
locally trivial. -/
theorem Presheaf.HasLocallyTrivialRelations.comp_quotSMulTop [IsNoetherianRing R]
    {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R} (hP : Presheaf.HasLocallyTrivialRelations J P)
    (I : Ideal R) :
    Presheaf.HasLocallyTrivialRelations J (P ⋙ ModuleCat.quotSMulTop I) := by
  classical
  intro V s q x e' he'
  -- generators of `I`, and lifts of the coefficients and of the sections
  obtain ⟨r, γ, hγ⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  choose e he using fun l j ↦ Ideal.Quotient.mk_surjective (e' l j)
  choose y hy using fun j ↦ Submodule.Quotient.mk_surjective _ (x j)
  -- each relation `∑ⱼ eₗⱼ yⱼ` lies in `I • P(V)`, hence is `∑ₖ γₖ wₗₖ`
  have hrel (l : Fin q) : ∑ j, e l j • y j ∈ I • (⊤ : Submodule R (P.obj (op V))) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    have h : (Submodule.Quotient.mk (∑ j, e l j • y j) :
        P.obj (op V) ⧸ I • (⊤ : Submodule R (P.obj (op V)))) = ∑ j, e' l j • x j := by
      simp only [← he, ← hy]
      exact map_sum (Submodule.mkQ _) _ _
    rw [h]
    exact he' l
  choose w hw using fun l ↦ Submodule.exists_eq_sum_smul_of_mem_smul_top hγ (hrel l)
  -- the lifted system of relations on `Fin s ⊕ (Fin q × Fin r)`
  let Y : Fin s ⊕ (Fin q × Fin r) → P.obj (op V) := Sum.elim y fun p ↦ w p.1 p.2
  let E : Matrix (Fin q) (Fin s ⊕ (Fin q × Fin r)) R :=
    fun l ↦ Sum.elim (e l) fun p ↦ if p.1 = l then -γ p.2 else 0
  have hE (l : Fin q) : ∑ n, E l n • Y n = 0 := by
    simp only [E, Y, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      ite_smul, zero_smul, neg_smul]
    rw [Finset.sum_eq_single l (fun l' _ hl' ↦ by simp [hl']) (by simp), hw l]
    simp
  obtain ⟨T, hT, hfac⟩ := hP.exists_of_fintype Y E hE
  refine ⟨T, hT, fun W f hf ↦ ?_⟩
  obtain ⟨t, b, z, heb, hyz⟩ := hfac f hf
  refine ⟨t, fun j m ↦ Ideal.Quotient.mk I (b (Sum.inl j) m),
    fun m ↦ Submodule.Quotient.mk (z m), ?_, fun j ↦ ?_⟩
  · ext l m
    have h₀ := congrFun (congrFun heb l) m
    simp only [Matrix.mul_apply, E, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_prod_type, ite_mul, zero_mul, neg_mul, Matrix.zero_apply] at h₀
    rw [Finset.sum_eq_single l (fun l' _ hl' ↦ by simp [hl']) (by simp)] at h₀
    simp only [ite_true, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at h₀
    simp only [Matrix.mul_apply, Matrix.zero_apply, ← he, ← map_mul, ← map_sum, h₀,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_right _ _ ?_
    rw [← hγ]
    exact Submodule.subset_span ⟨k, rfl⟩
  · rw [← hy j]
    change Submodule.Quotient.mk (P.map f.op (Y (Sum.inl j))) = _
    rw [hyz (Sum.inl j)]
    exact map_sum (Submodule.mkQ _) _ _

section Sheaf

variable [EssentiallySmall.{u + 1} C] [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)] (I : Ideal R)

variable (J) in
/-- Reduction modulo an ideal `I` of sheaves of `R`-modules: the sheafification of
`U ↦ F(U) / I F(U)`, a sheaf of `R ⧸ I`-modules. It is extension of scalars along
`R ⟶ R ⧸ I`. -/
noncomputable abbrev Sheaf.quotSMulTop :
    Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} (R ⧸ I)) :=
  Sheaf.composeAndSheafify J (ModuleCat.quotSMulTop I)

/-- **The reduction of a flat sheaf is flat.** If `F` is a flat sheaf of modules over a Noetherian
ring `R`, its reduction `F / I F` is a flat sheaf of `R ⧸ I`-modules. -/
theorem Sheaf.flat_quotSMulTop_obj [IsNoetherianRing R]
    [J.HasSheafCompose (forget (ModuleCat.{u + 1} (R ⧸ I)))]
    [J.WEqualsLocallyBijective (ModuleCat.{u + 1} (R ⧸ I))]
    {F : Sheaf J (ModuleCat.{u + 1} R)} (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((Sheaf.quotSMulTop J I).obj F) :=
  Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations
    ((Sheaf.hasLocallyTrivialRelations_of_flat hF).comp_quotSMulTop I)

/-- Tensoring a presheaf with a constant presheaf is computed objectwise. -/
noncomputable def whiskeringRightTensorRightIso (X : ModuleCat.{u + 1} R) :
    (Functor.whiskeringRight Cᵒᵖ _ _).obj (tensorRight X) ≅
      tensorRight ((Functor.const Cᵒᵖ).obj X) :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
      simp))
    (fun g ↦ by ext : 2; simp)

-- `HasWeakSheafify` for sheaves of modules over the two rings is slow to synthesize
/-- **Restricting the scalars of the reduction gives the tensor product with `R ⧸ I`.** For a
sheaf `F` of `R`-modules, the reduction `F / I F` with scalars restricted back to `R` is
`F ⊗ (R ⧸ I)_X`, naturally in `F`. -/
noncomputable def Sheaf.quotSMulTopCompRestrictScalarsIso :
    Sheaf.quotSMulTop J I ⋙ Sheaf.restrictScalars J (Ideal.Quotient.mk I) ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (R ⧸ I))) :=
  haveI : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I)) :=
    preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} (R ⧸ I)) := inferInstance
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} R) := inferInstance
  let S := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.quotSMulTop.{u + 1} I)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} (R ⧸ I))
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let ι := Sheaf.restrictScalars J (Ideal.Quotient.mk I)
  let X := (Functor.const Cᵒᵖ).obj (ModuleCat.of R (R ⧸ I))
  Functor.associator S (W ⋙ a') ι ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W a' ι) ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerLeft W
      (sheafComposeNatIso J (ModuleCat.restrictScalars (Ideal.Quotient.mk I))
        (sheafificationAdjunction J (ModuleCat.{u + 1} (R ⧸ I)))
        (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W _ a).symm ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerRight
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight _ _ _).mapIso (ModuleCat.quotSMulTopCompRestrictScalarsIso I) ≪≫
        whiskeringRightTensorRightIso _) a) ≪≫
    Functor.isoWhiskerLeft S (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
    (Functor.associator S a (tensorRight (a.obj X))).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
      (tensorRight (a.obj X)) ≪≫
    Functor.leftUnitor _

end Sheaf

end CategoryTheory
