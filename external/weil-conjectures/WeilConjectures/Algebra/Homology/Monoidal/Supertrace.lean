/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The categorical trace of a chain endomorphism is the supertrace

Let `C` be a braided monoidal preadditive category and `K` a bounded cochain complex in `C`
whose terms have right duals, so that `K` is paired with its termwise dual `K^∨`
(`CochainComplex.exactPairingRightDual`). For the Koszul braiding of cochain complexes, the
categorical trace of a chain endomorphism `v : K ⟶ K` is, in degree `0`, the supertrace
`∑ₚ (-1)ᵖ tr(vᵖ | Kᵖ)` (`CochainComplex.trace_f_zero`): on the summand `Kᵖ ⊗ (K^∨)⁻ᵖ` the
Koszul sign of the braiding is `(-1)^(p · (-p)) = (-1)ᵖ`.

The supertrace only depends on the homotopy class of `v`
(`Homotopy.sum_negOnePow_smul_eq`): this holds for any family of additive cyclic functions
on the endomorphisms of the terms, for instance the categorical traces of `C`
(`Homotopy.sum_negOnePow_smul_trace_eq`) or the traces of linear maps of finite free modules
(`Homotopy.sum_negOnePow_smul_linearMapTrace_eq`). In particular the categorical trace of a
chain endomorphism of a bounded complex only depends on its homotopy class
(`Homotopy.trace_eq`).

This is blueprint `proposition-properties-trace--4`; the fact that the evaluation and coevaluation
are maps of complexes satisfying the triangle identities is `CochainComplex.exactPairingRightDual`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CategoryTheory.MonoidalCategory

section

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]

/-- The categorical trace is additive (used for blueprint `proposition-properties-trace--4`). -/
lemma trace_add {X : C} [HasRightDual X] (f g : X ⟶ X) : trace (f + g) = trace f + trace g := by
  simp [trace]

/-- The categorical trace as an additive map (used for blueprint
`proposition-properties-trace--4`). -/
noncomputable def traceAddMonoidHom (X : C) [HasRightDual X] : (X ⟶ X) →+ (𝟙_ C ⟶ 𝟙_ C) where
  toFun := trace
  map_zero' := by simp [trace]
  map_add' := trace_add

/-- The additive categorical trace is the trace (blueprint `proposition-properties-trace--4`). -/
@[simp]
lemma traceAddMonoidHom_apply {X : C} [HasRightDual X] (f : X ⟶ X) :
    traceAddMonoidHom X f = trace f := rfl

end

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- The trace of `f : Y ⟶ Y` may be computed with the dual of an object `X ≅ Y`
(used for blueprint `proposition-properties-trace--4`). -/
lemma trace_eq_of_iso_rightDual {X Y : C} [HasRightDual X] [HasRightDual Y] (e : X ≅ Y)
    (f : Y ⟶ Y) (g : Y ⟶ X) (hg : g = e.inv) :
    η_ X Xᘁ ≫ e.hom ▷ Xᘁ ≫ f ▷ Xᘁ ≫ (β_ Y Xᘁ).hom ≫ Xᘁ ◁ g ≫ ε_ X Xᘁ = trace f := by
  subst hg
  rw [← BraidedCategory.braiding_naturality_left_assoc, ← comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, assoc]
  rw [← trace, trace_comp_comm, assoc, Iso.inv_hom_id, comp_id]

end CategoryTheory.MonoidalCategory

namespace Homotopy

variable {C : Type*} [Category* C] [Preadditive C] {K : CochainComplex C ℤ} {v v' : K ⟶ K}

/-- Blueprint `proposition-properties-trace--4` (homotopy invariance): let `τ` be a family of
additive functions on the endomorphisms of the terms of a bounded complex `K` which is cyclic,
`τ (g ≫ h) = τ (h ≫ g)`. Then `∑ₚ (-1)ᵖ τ(vᵖ)` only depends on the homotopy class of
`v : K ⟶ K`: if `v - v' = d h + h d`, the terms `τ(dh)` and `τ(hd)` cancel in pairs. -/
theorem sum_negOnePow_smul_eq (ho : Homotopy v v') (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {M : Type*} [AddCommGroup M] (τ : ∀ p, (K.X p ⟶ K.X p) →+ M)
    (hτ : ∀ p q (g : K.X p ⟶ K.X q) (h : K.X q ⟶ K.X p), τ p (g ≫ h) = τ q (h ≫ g)) :
    ∑ p ∈ Finset.Icc a b, p.negOnePow • τ p (v.f p) =
      ∑ p ∈ Finset.Icc a b, p.negOnePow • τ p (v'.f p) := by
  let g : ℤ → M := fun p ↦ p.negOnePow • τ p (prevD p ho.hom)
  have hg (p : ℤ) (hp : p ∉ Finset.Icc a b) : g p = 0 := by
    simp only [g]
    simp only [Finset.mem_Icc, not_and_or, not_le] at hp
    rcases hp with hp | hp
    · rw [(K.isZero_of_isStrictlyGE a p hp).eq_of_src (prevD p ho.hom) 0, map_zero, smul_zero]
    · rw [(K.isZero_of_isStrictlyLE b p hp).eq_of_src (prevD p ho.hom) 0, map_zero, smul_zero]
  have hg' (p : ℤ) (hp : p ∉ Finset.Icc a b) : g (p + 1) = 0 := by
    by_cases hp' : p + 1 ∈ Finset.Icc a b
    · obtain rfl : p = a - 1 := by
        simp only [Finset.mem_Icc] at hp hp'
        omega
      simp only [g]
      rw [prevD_eq _ (rfl : (ComplexShape.up ℤ).Rel (a - 1) (a - 1 + 1)),
        (K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_tgt (ho.hom (a - 1 + 1) (a - 1)) 0,
        zero_comp, map_zero, smul_zero]
    · exact hg _ hp'
  have e (p : ℤ) : p.negOnePow • τ p (v.f p) = p.negOnePow • τ p (v'.f p) + (g p - g (p + 1)) := by
    rw [ho.comm p, map_add, map_add,
      dNext_eq _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1)), hτ,
      ← prevD_eq _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1))]
    simp only [g, Int.negOnePow_succ, Units.neg_smul, smul_add]
    abel
  rw [Finset.sum_congr rfl (fun p _ ↦ e p), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← finsum_eq_sum_of_support_subset g (s := Finset.Icc a b) ?_,
    ← finsum_eq_sum_of_support_subset (fun p ↦ g (p + 1)) (s := Finset.Icc a b) ?_]
  · erw [finsum_comp_equiv (Equiv.addRight 1) (f := g)]
    rw [sub_self, add_zero]
  · intro p hp
    by_contra hp'
    exact hp (hg' p hp')
  · intro p hp
    by_contra hp'
    exact hp (hg p hp')

/-- Blueprint `proposition-properties-trace--4` (homotopy invariance): the alternating sum
`∑ₚ (-1)ᵖ tr(vᵖ | Kᵖ)` of the categorical traces of the components of a chain endomorphism `v` of
a bounded complex only depends on the homotopy class of `v`. -/
theorem sum_negOnePow_smul_trace_eq {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C] {K : CochainComplex C ℤ}
    [∀ n, HasRightDual (K.X n)] {v v' : K ⟶ K} (ho : Homotopy v v') (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    ∑ p ∈ Finset.Icc a b, (p.negOnePow : ℤ) • trace (v.f p) =
      ∑ p ∈ Finset.Icc a b, (p.negOnePow : ℤ) • trace (v'.f p) :=
  ho.sum_negOnePow_smul_eq a b (fun p ↦ traceAddMonoidHom (K.X p))
    (fun _ _ g h ↦ trace_comp_comm g h)

/-- Blueprint `proposition-properties-trace--4` (homotopy invariance): for a bounded complex `P` of
finite free modules over a commutative ring `R`, the supertrace `∑ᵢ (-1)ⁱ Tr(vⁱ | Pⁱ)` of a chain
endomorphism `v` only depends on the homotopy class of `v`. -/
theorem sum_negOnePow_smul_linearMapTrace_eq {R : Type*} [CommRing R]
    {P : CochainComplex (ModuleCat R) ℤ} [∀ n, Module.Free R (P.X n)]
    [∀ n, Module.Finite R (P.X n)] {v v' : P ⟶ P} (ho : Homotopy v v') (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v.f i).hom =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • LinearMap.trace R (P.X i) (v'.f i).hom :=
  ho.sum_negOnePow_smul_eq a b
    (fun i ↦ (LinearMap.trace R (P.X i)).toAddMonoidHom.comp
      (ModuleCat.homAddEquiv (M := P.X i) (N := P.X i)).toAddMonoidHom)
    (fun _ _ g h ↦ LinearMap.trace_comp_comm' g.hom h.hom)


end Homotopy

namespace CochainComplex

section

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] (K : CochainComplex C ℤ) [∀ n, HasRightDual (K.X n)]

/-- Blueprint `proposition-properties-trace--4`: the contribution of the summand `Kᵖ ⊗ (K^∨)⁻ᵖ` to
the trace of `v : K ⟶ K` is the trace of `vᵖ`. -/
lemma rightDual.coevPQ_comp_evalPQ (v : K ⟶ K) (p : ℤ) :
    coevPQ K p (-p) (add_neg_cancel p) ≫ v.f p ▷ K.rightDual.X (-p) ≫
      (β_ (K.X p) (K.rightDual.X (-p))).hom ≫ evalPQ K (-p) p (neg_add_cancel p) =
        trace (v.f p) := by
  simp only [coevPQ, evalPQ, assoc]
  exact trace_eq_of_iso_rightDual (K.XIsoOfEq (neg_neg p)) _ _
    (by simp [HomologicalComplex.XIsoOfEq])

end


variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  (K : CochainComplex C ℤ) [∀ n, HasRightDual (K.X n)] (a b : ℤ) [K.IsStrictlyGE a]
  [K.IsStrictlyLE b]

/-- The right dual `K^∨` of a bounded complex `K` whose terms have right duals, for the exact
pairing `CochainComplex.exactPairingRightDual` (blueprint `proposition-properties-trace--4`). -/
@[instance_reducible]
noncomputable def hasRightDual : HasRightDual K :=
  letI := exactPairingRightDual K a b
  ⟨K.rightDual⟩

/-- The categorical trace of a chain endomorphism of a bounded complex `K`, for the right dual
`CochainComplex.hasRightDual` (blueprint `proposition-properties-trace--4`). -/
lemma trace_eq (v : K ⟶ K) :
    letI := hasRightDual K a b
    trace v = rightDual.coev K a b ≫ v ▷ K.rightDual ≫ (β_ K K.rightDual).hom ≫
      rightDual.eval K := rfl

/-- Blueprint `proposition-properties-trace--4` (c): the categorical trace of a chain endomorphism
`v` of a bounded complex `K`, with respect to the Koszul braiding and the termwise dual `K^∨`, is
the supertrace `∑ₚ (-1)ᵖ tr(vᵖ | Kᵖ)`, as an endomorphism of `(𝟙_).X 0 ≅ 𝟙_ C`. -/
theorem trace_f_zero (v : K ⟶ K) :
    letI := hasRightDual K a b
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫ (trace v).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom =
      ∑ p ∈ Finset.Icc a b, (p.negOnePow : ℤ) • trace (v.f p) := by
  let := hasRightDual K a b
  simp only [trace_eq, HomologicalComplex.comp_f, assoc]
  rw [reassoc_of% rightDual.singleObjXSelf_inv_coev_f, rightDual.coevZero, Preadditive.sum_comp]
  refine Finset.sum_congr rfl (fun p _ ↦ ?_)
  rw [assoc, Monoidal.ι_whiskerRight_assoc]
  erw [Monoidal.ι_braiding_hom_assoc]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  simp only [assoc]
  rw [reassoc_of% rightDual.ι_eval_f, Iso.inv_hom_id, comp_id, mul_neg, Int.negOnePow_neg,
    Int.negOnePow_mul_self, ← rightDual.coevPQ_comp_evalPQ K v p]

/-- Blueprint `proposition-properties-trace--4` (c): the categorical trace of a chain endomorphism
`v` of a bounded complex `K` is the supertrace `∑ₚ (-1)ᵖ tr(vᵖ | Kᵖ)`, placed in degree `0` of the
unit complex. -/
theorem trace_f_zero_eq (v : K ⟶ K) :
    letI := hasRightDual K a b
    (trace v).f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ≫
      (∑ p ∈ Finset.Icc a b, (p.negOnePow : ℤ) • trace (v.f p)) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv := by
  rw [← trace_f_zero]
  simp

end CochainComplex

namespace Homotopy

open CochainComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  {K : CochainComplex C ℤ} [∀ n, HasRightDual (K.X n)]

/-- Blueprint `proposition-properties-trace--4`: the categorical trace of a chain endomorphism of a
bounded complex only depends on its homotopy class. -/
theorem trace_eq {v v' : K ⟶ K} (ho : Homotopy v v') (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] :
    letI := hasRightDual K a b
    trace v = trace v' := by
  let := hasRightDual K a b
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [trace_f_zero_eq K a b v, trace_f_zero_eq K a b v', ho.sum_negOnePow_smul_trace_eq a b]

end Homotopy
