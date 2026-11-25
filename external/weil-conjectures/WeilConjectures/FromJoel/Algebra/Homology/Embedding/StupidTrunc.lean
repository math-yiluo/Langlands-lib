/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.CategoryTheory.Retract

/-!
# The inclusion and projection of the stupid truncation

Supplement to `Mathlib.Algebra.Homology.Embedding.StupidTrunc`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

section

variable (K L : HomologicalComplex C c') (φ : K ⟶ L)
  (e : c.Embedding c')

open Classical in
noncomputable def ιStupidTruncf [e.IsRelIff] (i' : ι') : (K.stupidTrunc e).X i' ⟶ K.X i' :=
  if h : ∃ (i : ι), e.f i = i'
  then (K.stupidTruncXIso e h.choose_spec).hom
  else 0

set_option backward.isDefEq.respectTransparency false in
lemma ιStupidTruncf_eq [e.IsRelIff] (i : ι) :
    K.ιStupidTruncf e (e.f i) = ((K.restriction e).extendXIso e rfl).hom := by
  dsimp [ιStupidTruncf]
  rw [dite_eq_left ⟨i, rfl⟩]
  simp [extendXIso, extend.XIso, stupidTruncXIso]

set_option backward.defeqAttrib.useBackward true in
lemma ιStupidTruncf'_eq [e.IsRelIff] {i : ι} {i' : ι'} (h : e.f i = i') :
    K.ιStupidTruncf e i' = ((K.restriction e).extendXIso e h).hom ≫
      (K.restrictionXIso e h).hom := by
  subst h
  simp [ιStupidTruncf_eq, restrictionXIso]

variable [e.IsTruncGE]

set_option backward.defeqAttrib.useBackward true in
noncomputable def ιStupidTrunc : K.stupidTrunc e ⟶ K where
  f := K.ιStupidTruncf e
  comm' i' j' hij' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      obtain ⟨j, rfl⟩ := e.mem_next hij'
      simp [ιStupidTruncf_eq, stupidTrunc, (K.restriction e).extend_d_eq e rfl rfl]
    · apply (K.isZero_stupidTrunc_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

lemma isIso_ιStupidTrunc_f {i' : ι'} {i : ι} (h : e.f i = i') :
    IsIso ((K.ιStupidTrunc e).f i') := by
  subst h
  dsimp [ιStupidTrunc]
  rw [ιStupidTruncf_eq]
  infer_instance

instance (i : ι) : IsIso ((K.ιStupidTrunc e).f (e.f i)) :=
  K.isIso_ιStupidTrunc_f e rfl

instance (i' : ι') : Mono ((K.ιStupidTrunc e).f i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    infer_instance
  · constructor
    intros
    apply IsZero.eq_of_tgt
    apply HomologicalComplex.isZero_extend_X
    simpa using hi'

instance : Mono (K.ιStupidTrunc e) := mono_of_mono_f _ inferInstance

lemma isIso_ιStupidTrunc_iff :
    IsIso (K.ιStupidTrunc e) ↔ K.IsStrictlySupported e := by
  constructor
  · intro
    apply isStrictlySupported_of_iso (asIso (K.ιStupidTrunc e))
  · intro
    have : ∀ i', IsIso ((K.ιStupidTrunc e).f i') := fun i' => by
      by_cases hi' : ∃ i, e.f i = i'
      · obtain ⟨i, rfl⟩ := hi'
        infer_instance
      · refine ⟨0, ?_, ?_⟩
        all_goals
          apply IsZero.eq_of_src
          apply isZero_X_of_isStrictlySupported _ e
          simpa using hi'
    apply Hom.isIso_of_components

instance [K.IsStrictlySupported e] : IsIso (K.ιStupidTrunc e) := by
  rw [isIso_ιStupidTrunc_iff]
  infer_instance

variable {K L}

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ιStupidTrunc_naturality :
    stupidTruncMap φ e ≫ L.ιStupidTrunc e = K.ιStupidTrunc e ≫ φ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [ιStupidTrunc, ιStupidTruncf_eq, stupidTruncMap, extendMap_f _ e rfl]
  · apply (K.isZero_stupidTrunc_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[reassoc (attr := simp)]
lemma ιStupidTrunc_f_naturality (i' : ι') :
    (stupidTruncMap φ e).f i' ≫ (L.ιStupidTrunc e).f i' = (K.ιStupidTrunc e).f i' ≫ φ.f i' := by
  simp only [← comp_f, ιStupidTrunc_naturality]

end

section

variable (K L : HomologicalComplex C c') (φ : K ⟶ L)
  (e : c.Embedding c')

open Classical in
noncomputable def πStupidTruncf [e.IsRelIff] (i' : ι') : K.X i' ⟶ (K.stupidTrunc e).X i' :=
  if h : ∃ (i : ι), e.f i = i'
  then (K.stupidTruncXIso e h.choose_spec).inv
  else 0

set_option backward.isDefEq.respectTransparency false in
lemma πStupidTruncf_eq [e.IsRelIff] (i : ι) :
    K.πStupidTruncf e (e.f i) = ((K.restriction e).extendXIso e rfl).inv := by
  dsimp [πStupidTruncf]
  rw [dite_eq_left ⟨i, rfl⟩]
  simp [extendXIso, extend.XIso, stupidTruncXIso]

set_option backward.defeqAttrib.useBackward true in
/-- Variant of `πStupidTruncf_eq`. -/
lemma πStupidTruncf_eq' [e.IsRelIff] {i : ι} {i' : ι'} (h : e.f i = i') :
    K.πStupidTruncf e i' = (K.restrictionXIso e h).inv ≫
      ((K.restriction e).extendXIso e h).inv := by
  subst h
  simp [πStupidTruncf_eq, restrictionXIso]

variable [e.IsTruncLE]

set_option backward.defeqAttrib.useBackward true in
noncomputable def πStupidTrunc : K ⟶ K.stupidTrunc e where
  f := K.πStupidTruncf e
  comm' i' j' hij' := by
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      obtain ⟨i, rfl⟩ := e.mem_prev hij'
      simp [πStupidTruncf_eq, stupidTrunc, (K.restriction e).extend_d_eq e rfl rfl]
    · apply (K.isZero_stupidTrunc_X e j' (fun j hj => hj' ⟨j, hj⟩)).eq_of_tgt

lemma isIso_πStupidTrunc_f {i' : ι'} {i : ι} (h : e.f i = i') :
    IsIso ((K.πStupidTrunc e).f i') := by
  subst h
  dsimp [πStupidTrunc]
  rw [πStupidTruncf_eq]
  infer_instance

instance (i : ι) : IsIso ((K.πStupidTrunc e).f (e.f i)) :=
  K.isIso_πStupidTrunc_f e rfl

instance (i' : ι') : Epi ((K.πStupidTrunc e).f i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    infer_instance
  · constructor
    intros
    apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    simpa using hi'

instance : Epi (K.πStupidTrunc e) := epi_of_epi_f _ inferInstance

lemma isIso_πStupidTrunc_iff :
    IsIso (K.πStupidTrunc e) ↔ K.IsStrictlySupported e := by
  constructor
  · intro
    apply isStrictlySupported_of_iso (asIso (K.πStupidTrunc e)).symm
  · intro
    have : ∀ i', IsIso ((K.πStupidTrunc e).f i') := fun i' => by
      by_cases hi' : ∃ i, e.f i = i'
      · obtain ⟨i, rfl⟩ := hi'
        infer_instance
      · refine ⟨0, ?_, ?_⟩
        all_goals
          apply IsZero.eq_of_src
          apply isZero_X_of_isStrictlySupported _ e
          simpa using hi'
    apply Hom.isIso_of_components

instance [K.IsStrictlySupported e] : IsIso (K.πStupidTrunc e) := by
  rw [isIso_πStupidTrunc_iff]
  infer_instance

variable {K L}

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma πStupidTrunc_naturality :
    K.πStupidTrunc e ≫ stupidTruncMap φ e = φ ≫ L.πStupidTrunc e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [πStupidTrunc, πStupidTruncf_eq, stupidTruncMap, extendMap_f _ e rfl]
  · apply (L.isZero_stupidTrunc_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_tgt

@[reassoc (attr := simp)]
lemma πStupidTrunc_f_naturality (i' : ι') :
    (K.πStupidTrunc e).f i' ≫ (stupidTruncMap φ e).f i' = φ.f i' ≫ (L.πStupidTrunc e).f i' := by
  simp only [← comp_f, πStupidTrunc_naturality]

end

section

variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] (i' : ι')

@[reassoc (attr := simp)]
lemma ιStupidTruncf_πStupidTruncf :
    K.ιStupidTruncf e i' ≫ K.πStupidTruncf e i' = 𝟙 _ := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    rw [ιStupidTruncf_eq, πStupidTruncf_eq, Iso.hom_inv_id]
  · apply IsZero.eq_of_src
    apply isZero_stupidTrunc_X
    simpa using hi'

noncomputable def stupidTruncRetract :
    Retract ((K.stupidTrunc e).X i') (K.X i') where
  i := K.ιStupidTruncf e i'
  r := K.πStupidTruncf e i'

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def ιStupidTruncNatTrans [e.IsTruncGE] :
    e.stupidTruncFunctor C ⟶ 𝟭 _ where
  app K := K.ιStupidTrunc e

set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def πStupidTruncNatTrans [e.IsTruncLE] :
    𝟭 _ ⟶ e.stupidTruncFunctor C  where
  app K := K.πStupidTrunc e

end ComplexShape.Embedding
