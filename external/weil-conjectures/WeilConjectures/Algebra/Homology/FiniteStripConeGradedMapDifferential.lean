/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FiniteStripConeGradedMap

/-! # Differentials on the surviving diagonal
Source: Stacks Project, Homology, Tag 0133; finite-strip cone refinement, step 3.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem filtrationLift_arrow
    (M : CochainComplex C ℤ) (F : DecreasingFiltration M) (p n : ℤ)
    {V : C} (t : V ⟶ M.X n) (ht : (F.complexStep p n).Factors t) :
    letI := finiteStripStep_image_isIso M F p n
    (F.complexStep p n).factorThru t ht ≫
      inv (factorThruImageSubobject ((F.step p).arrow.f n)) ≫
      (F.step p).arrow.f n = t := by
  let := finiteStripStep_image_isIso M F p n
  dsimp only [DecreasingFiltration.complexStep] at ht ⊢
  calc
    _ = (imageSubobject ((F.step p).arrow.f n)).factorThru t ht ≫
        inv (factorThruImageSubobject ((F.step p).arrow.f n)) ≫
        factorThruImageSubobject ((F.step p).arrow.f n) ≫
        (imageSubobject ((F.step p).arrow.f n)).arrow := by
      rw [imageSubobject_arrow_comp]
    _ = t := by rw [IsIso.inv_hom_id_assoc, Subobject.factorThru_arrow]

private theorem filtrationLift_quotient_zero
    (M : CochainComplex C ℤ) (F : DecreasingFiltration M) (p n : ℤ)
    {V : C} (t : V ⟶ (F.step p : CochainComplex C ℤ).X n)
    (ht : (F.complexStep (p + 1) n).Factors (t ≫ (F.step p).arrow.f n)) :
    t ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n = 0 := by
  let := finiteStripStep_image_isIso M F (p + 1) n
  let l := (F.complexStep (p + 1) n).factorThru
    (t ≫ (F.step p).arrow.f n) ht ≫
      inv (factorThruImageSubobject ((F.step (p + 1)).arrow.f n))
  have hl : l ≫ (F.step (p + 1)).arrow.f n = t ≫ (F.step p).arrow.f n :=
    by simpa only [l, Category.assoc] using filtrationLift_arrow M F (p + 1) n _ ht
  have ht' : t = l ≫
      (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))).f n := by
    apply (cancel_mono ((F.step p).arrow.f n)).1
    simpa only [Category.assoc, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow] using hl.symm
  rw [ht', Category.assoc]
  have h := HomologicalComplex.congr_hom
    (cokernel.condition (Subobject.ofLE (F.step (p + 1)) (F.step p)
      (F.antitone_step (by omega)))) n
  change _ ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n = 0 at h
  rw [h, comp_zero]


private theorem nextTarget_factors
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p i j m : ℤ) (hm : i + j = m) (hj : p + 1 ≤ j) :
    (F.complexStep (p + 1) m).Factors
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j m ≫
        (CochainComplex.mappingCone.inr b).f m) := by
  by_cases hi : i ∈ Finset.Ico (0 : ℤ) (r : ℤ)
  · have heq : m - i = j := by omega
    apply Subobject.factors_of_le _ (show imageSubobject
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j m ≫
        (CochainComplex.mappingCone.inr b).f m) ≤ F.complexStep (p + 1) m by
      rw [hsteps]
      apply le_trans _ le_sup_right
      apply le_trans _ (Finset.le_sup (f := fun k ↦
        if p + 1 ≤ m - k then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) k (m - k) m ≫
            (CochainComplex.mappingCone.inr b).f m) else ⊥) hi)
      rw [heq, ite_eq_left hj])
    simpa using imageSubobject_factors_comp_self
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j m ≫
        (CochainComplex.mappingCone.inr b).f m) (𝟙 _)
  · have hz := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
      (hsupport i (by
        simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
        exact hi))
    rw [hz.eq_zero_of_src (K.ιTotalOrZero (ComplexShape.up ℤ) i j m)]
    simp only [zero_comp, Subobject.factors_zero]

private theorem nextSource_factors
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (r : ℕ)
    (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p m : ℤ) (hp : p ≤ m) :
    (F.complexStep (p + 1) m).Factors
      ((CochainComplex.mappingCone.inl b).v (m + 1) m (by omega)) := by
  apply Subobject.factors_of_le _ (show imageSubobject
    ((CochainComplex.mappingCone.inl b).v (m + 1) m (by omega)) ≤
      F.complexStep (p + 1) m by
    rw [hsteps, ite_eq_left (by omega)]
    exact le_sup_left)
  simpa using imageSubobject_factors_comp_self
    ((CochainComplex.mappingCone.inl b).v (m + 1) m (by omega)) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rowInr_inclusion
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (p n : ℤ) :
    (CochainComplex.mappingCone.inr (f p)).f (n - p) ≫
      finiteStripRowInclusion K A b f p n =
    K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ≫
      (CochainComplex.mappingCone.inr b).f n := by
  simp only [finiteStripRowInclusion, CochainComplex.mappingCone.inr,
    CochainComplex.mappingCone, HomologicalComplex.homotopyCofiber.inr_f,
    HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc, biprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rowInl_inclusion
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (p n : ℤ) :
    (CochainComplex.mappingCone.inl (f p)).v (n - p + 1) (n - p) (by omega) ≫
      finiteStripRowInclusion K A b f p n = finiteStripSourceInclusion K A b p n := by
  change HomologicalComplex.homotopyCofiber.inlX (f p) (n - p + 1) (n - p) rfl ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p) (n - p) (n - p + 1) rfl).hom ≫
    biprod.desc _ _ = _
  rw [HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc, biprod.inl_desc]

set_option backward.isDefEq.respectTransparency false in
private theorem rowTarget_defect_factors
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) :
    (F.complexStep (p + 1) (n + 1)).Factors
      ((CochainComplex.mappingCone.inr (f p)).f (n - p) ≫
          finiteStripRowInclusion K A b f p n ≫
          (CochainComplex.mappingCone b).d n (n + 1) -
        (CochainComplex.mappingCone.inr (f p)).f (n - p) ≫
          (CochainComplex.mappingCone (f p)).d (n - p) (n + 1 - p) ≫
          finiteStripRowInclusion K A b f p (n + 1)) := by
  rw [rowInr_inclusion_assoc, CochainComplex.mappingCone.inr_f_d,
    CochainComplex.mappingCone.inr_f_d_assoc, rowInr_inclusion]
  rw [K.ιTotalOrZero_eq _ _ _ _ (by dsimp; omega), total_d]
  simp only [Preadditive.comp_add, Preadditive.add_comp]
  rw [
    ι_D₁_assoc, ι_D₂_assoc, d₁_eq' _ _ (show (ComplexShape.up ℤ).Rel (n - p) (n + 1 - p) by
      change n - p + 1 = n + 1 - p
      omega), d₂_eq' _ _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)]
  dsimp only [ComplexShape.ε₁, TotalComplexShape.ε₁]
  simp only [one_smul, Category.assoc]
  rw [← Linear.units_smul_comp, flip_X_d]
  rw [add_sub_cancel_left, Category.assoc]
  apply Subobject.factors_of_factors_right
  exact nextTarget_factors K r hsupport A b F hsteps p (n - p) (p + 1) (n + 1)
    (by omega) le_rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sourceBlock_defect_factors
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (r : ℕ)
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n s t : ℤ)
    (hn : n + 1 = p) (hs : s + 1 = 0) (ht : t = 0) :
    (F.complexStep (p + 1) (n + 1)).Factors
      ((HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (A.X p)
        (s + 1) hs).hom ≫ (A.XIsoOfEq hn.symm).hom ≫
        (CochainComplex.mappingCone.inl b).v (n + 1) n (by omega) ≫
        (CochainComplex.mappingCone b).d n (n + 1) -
      (CochainComplex.mappingCone.inl (f p)).v (s + 1) s (by omega) ≫
        (CochainComplex.mappingCone (f p)).d s t ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p) t (t + 1) rfl).hom ≫
        biprod.desc 0 (K.ιTotalOrZero (ComplexShape.up ℤ) t p (n + 1) ≫
          (CochainComplex.mappingCone.inr b).f (n + 1))) := by
  subst p t
  have hs' : s = -1 := by omega
  subst s
  change (F.complexStep (n + 1 + 1) (n + 1)).Factors
    ((HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (A.X (n + 1))
      0 rfl).hom ≫ (A.XIsoOfEq rfl).hom ≫
      (CochainComplex.mappingCone.inl b).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone b).d n (n + 1) -
      (CochainComplex.mappingCone.inl (f (n + 1))).v 0 (-1) (by omega) ≫
      (CochainComplex.mappingCone (f (n + 1))).d (-1) 0 ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (f (n + 1)) 0 1 rfl).hom ≫
      biprod.desc 0 (K.ιTotalOrZero (ComplexShape.up ℤ) 0 (n + 1) (n + 1) ≫
        (CochainComplex.mappingCone.inr b).f (n + 1)))
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  rw [CochainComplex.mappingCone.inl_v_d b (n + 1) n (n + 1 + 1) (by omega) (by omega),
    CochainComplex.mappingCone.inl_v_d_assoc (f (n + 1)) 0 (-1) 1 (by omega) (by omega),
    HomologicalComplex.single_obj_d, zero_comp, sub_zero]
  simp only [CochainComplex.mappingCone.inr, CochainComplex.mappingCone,
    HomologicalComplex.homotopyCofiber.inr_f, Category.assoc,
    HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc, biprod.inr_desc]
  rw [hb, hf, K.ιTotalOrZero_eq _ 0 (n + 1) (n + 1) (by dsimp; omega)]
  simp only [HomologicalComplex.singleObjXSelf, Preadditive.comp_sub, Category.assoc]
  rw [sub_sub_cancel_left]
  rw [← Preadditive.neg_comp]
  apply Subobject.factors_of_factors_right
  apply Subobject.factors_of_factors_right
  exact nextSource_factors K r A b F hsteps (n + 1) (n + 1) le_rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rowSource_defect_factors
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (r : ℕ)
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) :
    (F.complexStep (p + 1) (n + 1)).Factors
      ((CochainComplex.mappingCone.inl (f p)).v (n - p + 1) (n - p) (by omega) ≫
          finiteStripRowInclusion K A b f p n ≫
          (CochainComplex.mappingCone b).d n (n + 1) -
        (CochainComplex.mappingCone.inl (f p)).v (n - p + 1) (n - p) (by omega) ≫
          (CochainComplex.mappingCone (f p)).d (n - p) (n + 1 - p) ≫
          finiteStripRowInclusion K A b f p (n + 1)) := by
  by_cases hn : n + 1 = p
  · rw [rowInl_inclusion_assoc]
    simp only [finiteStripRowInclusion, finiteStripSourceInclusion, dite_eq_left hn,
      dite_eq_right (show ¬ (n + 1 + 1 = p) by omega)]
    simp only [Category.assoc]
    exact sourceBlock_defect_factors K r A a b hb f hf F hsteps p n (n - p)
      (n + 1 - p) hn (by omega) (by omega)
  · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (A.X p) (n - p + 1) (by omega)
    have heq : ((CochainComplex.mappingCone.inl (f p)).v (n - p + 1) (n - p)
      (by omega) ≫ finiteStripRowInclusion K A b f p n ≫
      (CochainComplex.mappingCone b).d n (n + 1) -
      (CochainComplex.mappingCone.inl (f p)).v (n - p + 1) (n - p) (by omega) ≫
        (CochainComplex.mappingCone (f p)).d (n - p) (n + 1 - p) ≫
        finiteStripRowInclusion K A b f p (n + 1)) = 0 := hz.eq_zero_of_src _
    rw [heq]
    exact Subobject.factors_zero


/-- The surviving diagonal maps commute with the adjacent differentials.
Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133), second-variable variant;
explicit diagonal quotient argument of lem-sc-finite-strip-cone-filtration, step 3.
(blueprint: lem-sc-finite-strip-cone-graded-map-differential)

Proof: use the biproduct decomposition of the row cone and check on its source
and target inclusions. For the target `(n-p,p)` summand, the horizontal total
term is the row differential with coefficient one. The vertical term has index
`p+1`, hence factors through the next tail and is killed by the quotient
projection. For the source summand, which is nonzero only at `n=p-1`, the cone
formula has the negative source differential and the augmentation block. The
source differential raises the vertical index and vanishes modulo the next tail.
The augmentation block equals `a p` followed by the `(0,p)` total inclusion by
`hb`; its row-cone counterpart equals the same map under the single-object
identification by `hf`. Away from this source degree its domain is zero. Finally
use the filtration inclusion and quotient projection being chain maps to identify
the resulting ambient-cone calculation with the graded differential. This proves
commutation without assuming the diagonal maps are invertible. -/
theorem finiteStripGradedMap_differential
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) :
    finiteStripGradedMap K r hsupport A b f F hsteps p n ≫
      (F.gradedPiece p).d n (n + 1) =
    (CochainComplex.mappingCone (f p)).d (n - p) (n + 1 - p) ≫
      finiteStripGradedMap K r hsupport A b f F hsteps p (n + 1) := by
  let M := CochainComplex.mappingCone b
  let l (m : ℤ) :=
    letI := finiteStripStep_image_isIso M F p m
    (F.complexStep p m).factorThru (finiteStripRowInclusion K A b f p m)
      (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p m) ≫
      inv (factorThruImageSubobject ((F.step p).arrow.f m))
  have hl (m : ℤ) : l m ≫ (F.step p).arrow.f m =
      finiteStripRowInclusion K A b f p m := by
    simpa only [l, Category.assoc] using filtrationLift_arrow M F p m _
      (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p m)
  let e := finiteStripRowInclusion K A b f p n ≫ M.d n (n + 1) -
    (CochainComplex.mappingCone (f p)).d (n - p) (n + 1 - p) ≫
      finiteStripRowInclusion K A b f p (n + 1)
  have hsrc : (F.complexStep (p + 1) (n + 1)).Factors
      ((CochainComplex.mappingCone.inl (f p)).v (n - p + 1) (n - p) (by omega) ≫ e) := by
    simpa only [e, M, Preadditive.comp_sub] using
      rowSource_defect_factors K r A a b hb f hf F hsteps p n
  have htgt : (F.complexStep (p + 1) (n + 1)).Factors
      ((CochainComplex.mappingCone.inr (f p)).f (n - p) ≫ e) := by
    simpa only [e, M, Preadditive.comp_sub] using
      rowTarget_defect_factors K r hsupport A b f F hsteps p n
  have he : (F.complexStep (p + 1) (n + 1)).Factors e := by
    rw [← Category.id_comp e, ← CochainComplex.mappingCone.id_X (f p) (n - p)
      (n - p + 1) rfl, Preadditive.add_comp, Category.assoc, Category.assoc]
    exact Subobject.factors_add _ _
      (Subobject.factors_of_factors_right _ hsrc)
      (Subobject.factors_of_factors_right _ htgt)
  have hdef : (F.complexStep (p + 1) (n + 1)).Factors
      ((l n ≫ (F.step p : CochainComplex C ℤ).d n (n + 1) -
        (CochainComplex.mappingCone (f p)).d (n - p) (n + 1 - p) ≫ l (n + 1)) ≫
          (F.step p).arrow.f (n + 1)) := by
    rw [Preadditive.sub_comp, Category.assoc, ← (F.step p).arrow.comm n (n + 1),
      ← Category.assoc, hl, Category.assoc, hl]
    exact he
  have hzero := filtrationLift_quotient_zero M F p (n + 1) _ hdef
  rw [Preadditive.sub_comp, sub_eq_zero] at hzero
  calc
    _ = (l n ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n) ≫
        (F.gradedPiece p).d n (n + 1) := by
      simp only [finiteStripGradedMap, l, Category.assoc]
    _ = (l n ≫ (F.step p : CochainComplex C ℤ).d n (n + 1)) ≫
        (F.complexQuotientπ p (p + 1) (by omega)).f (n + 1) := by
      simpa only [Category.assoc, DecreasingFiltration.gradedPiece,
        DecreasingFiltration.gr, DecreasingFiltration.complexQuotient] using
        congrArg (fun t ↦ l n ≫ t)
        ((F.complexQuotientπ p (p + 1) (by omega)).comm n (n + 1))
    _ = _ := by
      rw [hzero]
      simp only [finiteStripGradedMap, l, Category.assoc]

end HomologicalComplex₂
