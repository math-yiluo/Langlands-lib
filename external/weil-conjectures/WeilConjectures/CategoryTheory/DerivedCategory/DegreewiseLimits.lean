/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Coproducts and products of homological complexes

We collect facts about coproducts and products in categories of homological complexes, which
are computed degreewise.

* The evaluation functor `HomologicalComplex.eval C c i₁` is a left adjoint as soon as there is
  `i₀ ≠ i₁` with `c.Rel i₀ i₁`: the functor `K ↦ (K.X i₁ ⟶ X)` is represented by
  `double (𝟙 X) hi₀₁`. In particular, for cochain complexes indexed by `ℤ`, colimits are
  computed degreewise without any assumption on `C`.
* If colimits (resp. limits) of shape `J` are exact in an abelian category `C`, then the homology
  functors preserve them.
* If in each degree at most one summand is nonzero, a coproduct of complexes is also a product.
* Homotopies can be glued along coproducts, so that the quotient functor to the homotopy
  category preserves coproducts. (For products, see `HomotopyCategory.isLimitFanQuotient`.)

## Main statements

- `HomologicalComplex.isColimitCofanHomology`: homology commutes with exact coproducts.
- `HomologicalComplex.isLimitFanHomology`: homology commutes with exact products.
- `HomologicalComplex.isLimitFanMkProjOfIsColimit`: a coproduct of complexes with at most one
  nonzero summand in each degree is also a product.
- `CochainComplex.eq_of_not_isZero_singleFunctor_obj_shift_X`: the complexes `F[0]⟦n⟧` for
  `n : ℕ` satisfy this support condition.
- `HomotopyCategory.isColimitCofanQuotient`: the quotient functor to the homotopy category
  preserves coproducts which are computed degreewise.
-/

@[expose] public section

open CategoryTheory Limits Category Opposite

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] {J : Type*} [Category* J]

/-- The natural transformation `(evaluation J C).obj j ⟶ colim` given by the colimit
injections. -/
@[simps]
noncomputable def evaluationToColim [HasColimitsOfShape J C] (j : J) :
    (evaluation J C).obj j ⟶ colim where
  app F := colimit.ι F j

/-- The natural transformation `lim ⟶ (evaluation J C).obj j` given by the limit
projections. -/
@[simps]
noncomputable def limToEvaluation [HasLimitsOfShape J C] (j : J) :
    lim ⟶ (evaluation J C).obj j where
  app F := limit.π F j

/-- The homology of a short complex in a functor category is computed pointwise. -/
noncomputable def homologyFunctorEvaluationIso (F : J ⥤ ShortComplex C) :
    F ⋙ homologyFunctor C ≅ ((functorEquivalence J C).inverse.obj F).homology :=
  NatIso.ofComponents
    (fun j ↦ ((functorEquivalence J C).inverse.obj F).mapHomologyIso ((evaluation J C).obj j))
    (fun {j j'} f ↦ by
      have h := NatTrans.app_homology ((evaluation J C).map f)
        ((functorEquivalence J C).inverse.obj F)
      rw [Iso.eq_inv_comp] at h
      exact h.symm)

/-- If colimits of shape `J` are exact in `C`, the homology functor `ShortComplex C ⥤ C`
preserves them. -/
instance [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    PreservesColimitsOfShape J (homologyFunctor C) where
  preservesColimit {F} := by
    let S := (functorEquivalence J C).inverse.obj F
    refine preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
      (IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv
        (homologyFunctorEvaluationIso F) _).symm (colimit.isColimit S.homology))
        (Cocone.ext (S.mapHomologyIso colim).symm (fun j ↦ ?_)))
    have h : (S.mapHomologyIso ((evaluation J C).obj j)).hom ≫ colimit.ι S.homology j ≫
        (S.mapHomologyIso colim).inv = homologyMap (S.mapNatTrans (evaluationToColim j)) := by
      rw [← evaluationToColim_app, NatTrans.app_homology]
      simp
    exact (assoc _ _ _).trans h

/-- If limits of shape `J` are exact in `C`, the homology functor `ShortComplex C ⥤ C`
preserves them. -/
instance [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    PreservesLimitsOfShape J (homologyFunctor C) where
  preservesLimit {F} := by
    let S := (functorEquivalence J C).inverse.obj F
    refine preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
      (IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv
        (homologyFunctorEvaluationIso F) _).symm (limit.isLimit S.homology))
        (Cone.ext (S.mapHomologyIso lim).symm (fun j ↦ ?_)))
    have h : limit.π S.homology j ≫ (S.mapHomologyIso ((evaluation J C).obj j)).inv =
        (S.mapHomologyIso lim).inv ≫ homologyMap (S.mapNatTrans (limToEvaluation j)) := by
      rw [← limToEvaluation_app, NatTrans.app_homology]
      simp
    exact h

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C : Type*} [Category* C] {J : Type*} [Category* J] {ι : Type*} {c : ComplexShape ι}

section

variable [HasZeroMorphisms C]

instance [HasColimitsOfShape J C] (i j k : ι) :
    PreservesColimitsOfShape J (shortComplexFunctor' C c i j k) where
  preservesColimit := ⟨fun hs ↦ ⟨ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves (eval C c i) hs) (isColimitOfPreserves (eval C c j) hs)
    (isColimitOfPreserves (eval C c k) hs)⟩⟩

instance [HasLimitsOfShape J C] (i j k : ι) :
    PreservesLimitsOfShape J (shortComplexFunctor' C c i j k) where
  preservesLimit := ⟨fun hs ↦ ⟨ShortComplex.isLimitOfIsLimitπ _
    (isLimitOfPreserves (eval C c i) hs) (isLimitOfPreserves (eval C c j) hs)
    (isLimitOfPreserves (eval C c k) hs)⟩⟩

instance [HasColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (shortComplexFunctor C c i) :=
  inferInstanceAs (PreservesColimitsOfShape J (shortComplexFunctor' C c _ i _))

instance [HasLimitsOfShape J C] (i : ι) :
    PreservesLimitsOfShape J (shortComplexFunctor C c i) :=
  inferInstanceAs (PreservesLimitsOfShape J (shortComplexFunctor' C c _ i _))

end

variable [Abelian C]

instance [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (homologyFunctor C c i) :=
  preservesColimitsOfShape_of_natIso (homologyFunctorIso C c i).symm

instance [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] (i : ι) :
    PreservesLimitsOfShape J (homologyFunctor C c i) :=
  preservesLimitsOfShape_of_natIso (homologyFunctorIso C c i).symm

/-- Homology commutes with coproducts when coproducts are exact: if `s` is a coproduct of
a family `K` of homological complexes, then `Hⁱ(s.pt)` is the coproduct of the `Hⁱ(K j)`. -/
noncomputable def isColimitCofanHomology {β : Type*} [HasColimitsOfShape (Discrete β) C]
    [HasExactColimitsOfShape (Discrete β) C] {K : β → HomologicalComplex C c} {s : Cofan K}
    (hs : IsColimit s) (i : ι) :
    IsColimit (Cofan.mk (s.pt.homology i) fun j ↦ homologyMap (s.inj j) i) :=
  isColimitCofanMkObjOfIsColimit (homologyFunctor C c i) K s.inj
    (hs.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp)))

/-- Homology commutes with products when products are exact: if `s` is a product of
a family `K` of homological complexes, then `Hⁱ(s.pt)` is the product of the `Hⁱ(K j)`. -/
noncomputable def isLimitFanHomology {β : Type*} [HasLimitsOfShape (Discrete β) C]
    [HasExactLimitsOfShape (Discrete β) C] {K : β → HomologicalComplex C c} {s : Fan K}
    (hs : IsLimit s) (i : ι) :
    IsLimit (Fan.mk (s.pt.homology i) fun j ↦ homologyMap (s.proj j) i) :=
  isLimitFanMkObjOfIsLimit (homologyFunctor C c i) K s.proj
    (hs.ofIsoLimit (Fan.ext (Iso.refl _) (by simp)))

end HomologicalComplex

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {β : Type*} {X : β → C}

/-- If at most one of the objects `X j` is nonzero, a coproduct `s` of the `X j` is also
a product, with projections any retractions `p j` of the coprojections. -/
noncomputable def Cofan.IsColimit.isLimitFanMk {s : Cofan X} (hs : IsColimit s)
    (hX : ∀ i j, ¬ IsZero (X i) → ¬ IsZero (X j) → i = j) (p : ∀ j, s.pt ⟶ X j)
    (hp : ∀ j, s.inj j ≫ p j = 𝟙 _) : IsLimit (Fan.mk s.pt p) := by
  by_cases h : ∃ j, ¬ IsZero (X j)
  · let j₀ := h.choose
    have hj₀ : ¬ IsZero (X j₀) := h.choose_spec
    have hX' (j : β) (hj : j ≠ j₀) : IsZero (X j) := by
      by_contra h
      exact hj (hX _ _ h hj₀)
    have hp₀ : p j₀ ≫ s.inj j₀ = 𝟙 _ := Cofan.IsColimit.hom_ext hs _ _ fun j ↦ by
      by_cases hj : j = j₀
      · subst hj
        simp [reassoc_of% (hp j₀)]
      · exact (hX' j hj).eq_of_src _ _
    refine Fan.IsLimit.mk _ (fun t ↦ t.proj j₀ ≫ s.inj j₀) (fun t j ↦ ?_) (fun t m hm ↦ ?_)
    · by_cases hj : j = j₀
      · subst hj
        simp [hp]
      · exact (hX' j hj).eq_of_tgt _ _
    · rw [← hm j₀]
      simp [hp₀]
  · simp only [not_exists, not_not] at h
    have hpt : IsZero s.pt := (IsZero.iff_id_eq_zero _).2
      (Cofan.IsColimit.hom_ext hs _ _ fun j ↦ (h j).eq_of_src _ _)
    exact Fan.IsLimit.mk _ (fun _ ↦ 0) (fun _ j ↦ (h j).eq_of_tgt _ _)
      (fun _ _ _ ↦ hpt.eq_of_tgt _ _)

variable [DecidableEq β]

/-- The projection from a coproduct onto one of its summands, which is the identity on this
summand and zero on the other summands. -/
noncomputable def Cofan.IsColimit.proj {s : Cofan X} (hs : IsColimit s) (j : β) : s.pt ⟶ X j :=
  Cofan.IsColimit.desc hs fun i ↦ if h : i = j then eqToHom (by rw [h]) else 0

@[reassoc (attr := simp)]
lemma Cofan.IsColimit.inj_proj_self {s : Cofan X} (hs : IsColimit s) (j : β) :
    s.inj j ≫ proj hs j = 𝟙 _ := by
  simp [proj]

@[reassoc]
lemma Cofan.IsColimit.inj_proj_of_ne {s : Cofan X} (hs : IsColimit s) {i j : β} (h : i ≠ j) :
    s.inj i ≫ proj hs j = 0 := by
  simp [proj, h]

/-- If at most one of the objects `X j` is nonzero, a coproduct `s` of the `X j` is also
a product, with projections `Cofan.IsColimit.proj hs`. -/
noncomputable def Cofan.IsColimit.isLimitFanMkProj {s : Cofan X} (hs : IsColimit s)
    (hX : ∀ i j, ¬ IsZero (X i) → ¬ IsZero (X j) → i = j) :
    IsLimit (Fan.mk s.pt (proj hs)) :=
  isLimitFanMk hs hX _ (inj_proj_self hs)

end CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  {β : Type*} {K : β → HomologicalComplex C c}

/-- If in each degree at most one of the complexes `K j` is nonzero, a coproduct `s` of the
`K j` is also a product, with projections any retractions `p j` of the coprojections. -/
noncomputable def isLimitFanMkOfIsColimit
    [∀ i, PreservesColimit (Discrete.functor K) (eval C c i)]
    (hK : ∀ (i : ι) (j j' : β), ¬ IsZero ((K j).X i) → ¬ IsZero ((K j').X i) → j = j')
    {s : Cofan K} (hs : IsColimit s) (p : ∀ j, s.pt ⟶ K j) (hp : ∀ j, s.inj j ≫ p j = 𝟙 _) :
    IsLimit (Fan.mk s.pt p) :=
  isLimitOfEval _ _ fun i ↦ (isLimitMapConeFanMkEquiv (eval C c i) K p).symm
    (Cofan.IsColimit.isLimitFanMk (isColimitCofanMkX hs i) (hK i) _
      (fun j ↦ by simpa using congr_hom (hp j) i))

/-- If in each degree at most one of the complexes `K j` is nonzero, a coproduct `s` of the
`K j` is also a product, with projections `Cofan.IsColimit.proj hs`. -/
noncomputable def isLimitFanMkProjOfIsColimit [DecidableEq β]
    [∀ i, PreservesColimit (Discrete.functor K) (eval C c i)]
    (hK : ∀ (i : ι) (j j' : β), ¬ IsZero ((K j).X i) → ¬ IsZero ((K j').X i) → j = j')
    {s : Cofan K} (hs : IsColimit s) :
    IsLimit (Fan.mk s.pt (Cofan.IsColimit.proj hs)) :=
  isLimitFanMkOfIsColimit hK hs _ (Cofan.IsColimit.inj_proj_self hs)

end HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- In each degree, at most one of the complexes `F[0]⟦n⟧` for `n : ℕ` is nonzero. -/
lemma eq_of_not_isZero_singleFunctor_obj_shift_X (F : C) (d : ℤ) (m n : ℕ)
    (hm : ¬ IsZero (((singleFunctor C 0).obj F)⟦(m : ℤ)⟧.X d))
    (hn : ¬ IsZero (((singleFunctor C 0).obj F)⟦(n : ℤ)⟧.X d)) : m = n := by
  have h (k : ℕ) (hk : ¬ IsZero (((singleFunctor C 0).obj F)⟦(k : ℤ)⟧.X d)) : d + k = 0 := by
    by_contra h
    exact hk (HomologicalComplex.isZero_single_obj_X (.up ℤ) _ _ _ h)
  have := h m hm
  have := h n hn
  omega

/-- The coproduct of the complexes `F[0]⟦n⟧` for `n : ℕ` is also their product. -/
noncomputable def isLimitFanMkProjSingleFunctorObjShift (F : C)
    {s : Cofan fun n : ℕ ↦ ((singleFunctor C 0).obj F)⟦(n : ℤ)⟧} (hs : IsColimit s) :
    IsLimit (Fan.mk s.pt (Cofan.IsColimit.proj hs)) :=
  HomologicalComplex.isLimitFanMkProjOfIsColimit
    (fun d m n ↦ eq_of_not_isZero_singleFunctor_obj_shift_X F d m n) hs

end CochainComplex

namespace Homotopy

open HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {β : Type*} {K : β → HomologicalComplex C c}

/-- Homotopies between morphisms out of a coproduct of complexes (computed degreewise) can be
glued from homotopies on the summands. -/
noncomputable def ofIsColimitCofan [∀ i, PreservesColimit (Discrete.functor K) (eval C c i)]
    {s : Cofan K} (hs : IsColimit s) {L : HomologicalComplex C c} {f g : s.pt ⟶ L}
    (h : ∀ j, Homotopy (s.inj j ≫ f) (s.inj j ≫ g)) : Homotopy f g where
  hom p q := Cofan.IsColimit.desc (isColimitCofanMkX hs p) fun j ↦ (h j).hom p q
  zero p q hpq := Cofan.IsColimit.hom_ext (isColimitCofanMkX hs p) _ _ fun j ↦ by
    simpa using (h j).zero p q hpq
  comm p := Cofan.IsColimit.hom_ext (isColimitCofanMkX hs p) _ _ fun j ↦ by
    have := (h j).comm p
    simp only [comp_f] at this
    simp [dNext, prevD, this]

end Homotopy

namespace HomotopyCategory

open HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {β : Type*} {K : β → HomologicalComplex C c}

/-- The quotient functor to the homotopy category preserves coproducts of complexes which are
computed degreewise. -/
noncomputable def isColimitCofanQuotient
    [∀ i, PreservesColimit (Discrete.functor K) (eval C c i)] {s : Cofan K} (hs : IsColimit s) :
    IsColimit (Cofan.mk ((quotient C c).obj s.pt) fun j ↦ (quotient C c).map (s.inj j)) :=
  have fac (t : Cofan fun j ↦ (quotient C c).obj (K j)) (j : β) :
      (quotient C c).map (s.inj j ≫ Cofan.IsColimit.desc hs fun j ↦ (t.inj j).out) = t.inj j :=
    (congrArg (quotient C c).map (Cofan.IsColimit.fac hs _ j)).trans (quotient_map_out _)
  Cofan.IsColimit.mk _
    (fun t ↦ (quotient C c).map (Cofan.IsColimit.desc hs fun j ↦ (t.inj j).out))
    (fun t j ↦ ((quotient C c).map_comp _ _).symm.trans (fac t j))
    (fun t m hm ↦ by
      rw [← quotient_map_out m]
      refine eq_of_homotopy _ _ (Homotopy.ofIsColimitCofan hs fun j ↦ homotopyOfEq _ _ ?_)
      exact ((quotient C c).map_comp _ _).trans
        ((congrArg (_ ≫ ·) (quotient_map_out m)).trans ((hm j).trans (fac t j).symm)))

end HomotopyCategory
