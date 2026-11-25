/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-!
# Relations between `extend` and `restriction`: the `descExtend` API

Supplement to `Mathlib.Algebra.Homology.Embedding.HomEquiv`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

Given an embedding `e : Embedding c c'` of complex shapes satisfying `e.IsRelIff`,
we obtain a bijection `e.homEquiv'` between the type of morphisms
`L.extend e ⟶ K` (with `K : HomologicalComplex C c'` and `L : HomologicalComplex C c`)
and the subtype of morphisms `φ : L ⟶ K.restriction e` which satisfy a certain
condition `e.HasDesc φ`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace ComplexShape

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

namespace Embedding

open HomologicalComplex

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

section

def HasDesc (φ : L ⟶ K.restriction e) : Prop :=
  ∀ (i : ι) (_ : e.BoundaryLE i) (j' : ι')
    (_ : c'.Rel (e.f i) j' ), φ.f i ≫ K.d _ j' = 0

namespace descExtend

variable (φ : L ⟶ K.restriction e) (hφ : e.HasDesc φ)

variable {e}

open Classical in
noncomputable def f (i' : ι') : (L.extend e).X i' ⟶ K.X i' :=
  if hi' : ∃ i, e.f i = i'
  then (L.extendXIso e hi'.choose_spec).hom ≫ φ.f hi'.choose ≫
    (K.restrictionXIso e hi'.choose_spec).hom
  else 0

lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f φ i' = (L.extendXIso e hi).hom ≫ φ.f i ≫ (K.restrictionXIso e hi).hom := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  dsimp [f]
  rw [dite_eq_left ⟨i, hi⟩]
  subst this
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hφ in
@[reassoc (attr := simp)]
lemma comm (i' j' : ι') : f φ i' ≫ K.d i' j' = (L.extend e).d i' j' ≫ f φ j' := by
  by_cases hij' : c'.Rel i' j'
  · by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj'
      rw [f_eq φ hj]
      by_cases hi' : ∃ i, e.f i = i'
      · obtain ⟨i, hi⟩ := hi'
        rw [f_eq φ hi, L.extend_d_eq e hi hj]
        subst hi hj
        simpa [HomologicalComplex.restrictionXIso] using φ.comm i j
      · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
      rw [this, zero_comp]
      by_cases hi' : ∃ i, e.f i = i'
      · obtain ⟨i, rfl⟩ := hi'
        rw [f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [comp_id, assoc, hφ i (e.boundaryLE hij' (by simpa using hj')) j' hij', comp_zero]
      · have : f φ i' = 0 := by
          apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
        rw [this, zero_comp]
  · simp [HomologicalComplex.shape _ _ _ hij']

end descExtend

variable (φ : L ⟶ K.restriction e) (hφ : e.HasDesc φ)

noncomputable def descExtend :
    L.extend e ⟶ K where
  f i' := descExtend.f φ i'
  comm' _ _ _ := descExtend.comm φ hφ _ _

variable {i' : ι'} {i : ι} (hi : e.f i = i')

lemma descExtend_f :
    (e.descExtend φ hφ).f i' = (L.extendXIso e hi).hom ≫ φ.f i ≫(K.restrictionXIso e hi).hom := by
  apply descExtend.f_eq

set_option backward.defeqAttrib.useBackward true in
noncomputable def descExtendfArrowIso :
    Arrow.mk ((e.descExtend φ hφ).f i') ≅ Arrow.mk (φ.f i) :=
  Arrow.isoMk (L.extendXIso e hi) (K.restrictionXIso e hi).symm
    (by simp [e.descExtend_f φ hφ hi])

include hi

lemma isIso_descExtend_f_iff :
    IsIso ((e.descExtend φ hφ).f i') ↔ IsIso (φ.f i) :=
  (MorphismProperty.isomorphisms C).arrow_mk_iso_iff (e.descExtendfArrowIso φ hφ hi)

lemma mono_descExtend_f_iff :
    Mono ((e.descExtend φ hφ).f i') ↔ Mono (φ.f i) :=
  (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (e.descExtendfArrowIso φ hφ hi)

lemma epi_descExtend_f_iff :
    Epi ((e.descExtend φ hφ).f i') ↔ Epi (φ.f i) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff (e.descExtendfArrowIso φ hφ hi)


end

namespace homRestrict'

variable {e}
variable (ψ : L.extend e ⟶ K)

noncomputable def f (i : ι) : L.X i ⟶ (K.restriction e).X i :=
  (L.extendXIso e rfl).inv ≫ ψ.f (e.f i)

set_option backward.defeqAttrib.useBackward true in
lemma f_eq {i : ι} {i' : ι'} (h : e.f i = i') :
    f ψ i = (L.extendXIso e h).inv ≫ ψ.f i' ≫ (K.restrictionXIso e h).inv := by
  subst h
  simp [f, restrictionXIso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma comm (i j : ι) :
    f ψ i ≫ K.d (e.f i) (e.f j) = L.d i j ≫ f ψ j := by
  dsimp [f]
  rw [assoc, Hom.comm, L.extend_d_eq e rfl rfl, assoc, assoc, Iso.inv_hom_id_assoc]

end homRestrict'

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `L ⟶ K.restriction e` induced by a morphism `L.extend e ⟶ K`. -/
noncomputable def homRestrict' (ψ : L.extend e ⟶ K) : L ⟶ K.restriction e where
  f i := homRestrict'.f ψ i

lemma homRestrict'_f (ψ : L.extend e ⟶ K) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.homRestrict' ψ).f i = (L.extendXIso e h).inv ≫ ψ.f i'≫ (K.restrictionXIso e h).inv :=
  homRestrict'.f_eq ψ h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma homRestrict'_hasDesc (ψ : L.extend e ⟶ K) :
    e.HasDesc (e.homRestrict' ψ) := by
  intro i hi j' hij'
  have : (L.extend e).d (e.f i) j' = 0 := by
    apply (L.isZero_extend_X e j' (hi.notMem hij')).eq_of_tgt
  dsimp [homRestrict']
  rw [homRestrict'.f_eq ψ rfl, restrictionXIso, eqToIso_refl, Iso.refl_inv, assoc, assoc]
  dsimp
  rw [id_comp, ψ.comm, this, zero_comp, comp_zero]

/-- `e.descExtend (e.homRestrict' ψ) (e.homRestrict'_hasDesc ψ) = ψ`. -/
@[simp]
lemma descExtend_homRestrict' (ψ : L.extend e ⟶ K) :
    e.descExtend (e.homRestrict' ψ) (e.homRestrict'_hasDesc ψ) = ψ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [e.homRestrict'_f _ rfl, e.descExtend_f _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src

@[simp]
lemma homRestrict'_descExtend (φ : L ⟶ K.restriction e) (hφ : e.HasDesc φ) :
    e.homRestrict' (e.descExtend φ hφ) = φ := by
  ext i
  simp [e.homRestrict'_f _ rfl, e.descExtend_f _ _ rfl]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma homRestrict'_postcomp (α : K ⟶ K') (ψ : L.extend e ⟶ K) :
    e.homRestrict' (ψ ≫ α) = e.homRestrict' ψ ≫ restrictionMap α e:= by
  ext i
  simp [homRestrict'_f _ _ rfl, restrictionXIso]

/-- `e.homRestrict' (extendMap β e ≫ ψ) = β ≫ e.homRestrict' ψ`. -/
@[reassoc]
lemma extend_comp_homRestrict' (ψ : L.extend e ⟶ K) (β : L' ⟶ L) :
    e.homRestrict' (extendMap β e ≫ ψ) =
      β ≫ e.homRestrict' ψ := by
  ext i
  simp [homRestrict'_f _ _ rfl, extendMap_f β e rfl]

/-- The bijection between `L ⟶ K.extend e` and the subtype of `L ⟶ K.restriction e`
consisting of morphisms `φ` such that `e.HasDesc φ`. -/
@[simps]
noncomputable def homEquiv' (L : HomologicalComplex C c) (K : HomologicalComplex C c') :
    (L.extend e ⟶ K) ≃ { φ : L ⟶ K.restriction e // e.HasDesc φ } where
  toFun ψ := ⟨e.homRestrict' ψ, e.homRestrict'_hasDesc ψ⟩
  invFun φ := e.descExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

end Embedding

end ComplexShape
