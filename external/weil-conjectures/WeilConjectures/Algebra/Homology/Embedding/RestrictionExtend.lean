/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# Complexes supported on an embedding are extensions of their restrictions

Let `e : c.Embedding c'` be an embedding of complex shapes and `K` a complex for `c'` which is
strictly supported on `e`. Then `K` is isomorphic to the extension of its restriction
(`HomologicalComplex.isoExtendRestriction`), and a morphism `φ : K ⟶ L.extend e` is a
quasi-isomorphism if and only if the corresponding morphism `K.restriction e ⟶ L` is
(`HomologicalComplex.quasiIso_iff_quasiIso_homRestrict`).
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  [e.IsRelIff] {C : Type*} [Category* C]

section HasZero

variable [HasZeroMorphisms C] [HasZeroObject C]

omit [HasZeroObject C] in
lemma hasLift_id_restriction (K : HomologicalComplex C c') [K.IsStrictlySupported e] :
    e.HasLift (𝟙 (K.restriction e)) := fun _ hj i' hi' ↦
  (K.isZero_X_of_isStrictlySupported e i' (hj.notMem hi')).eq_of_src _ _

instance isIso_liftExtend_id_restriction (K : HomologicalComplex C c')
    [K.IsStrictlySupported e] :
    IsIso (e.liftExtend (𝟙 (K.restriction e)) (hasLift_id_restriction e K)) := by
  have (i' : ι') :
      IsIso ((e.liftExtend (𝟙 (K.restriction e)) (hasLift_id_restriction e K)).f i') := by
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi
      rw [e.isIso_liftExtend_f_iff _ _ rfl]
      infer_instance
    · have h₁ := K.isZero_X_of_isStrictlySupported e i' (by simpa using hi)
      have h₂ := (K.restriction e).isZero_extend_X e i' (by simpa using hi)
      exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  exact Hom.isIso_of_components _

/-- A complex strictly supported on an embedding is the extension of its restriction. -/
noncomputable def isoExtendRestriction (K : HomologicalComplex C c') [K.IsStrictlySupported e] :
    K ≅ (K.restriction e).extend e :=
  asIso (e.liftExtend (𝟙 (K.restriction e)) (hasLift_id_restriction e K))

lemma eq_isoExtendRestriction_hom_comp {K : HomologicalComplex C c'} [K.IsStrictlySupported e]
    {L : HomologicalComplex C c} (φ : K ⟶ L.extend e) :
    φ = (isoExtendRestriction e K).hom ≫ extendMap (e.homRestrict φ) e := by
  apply (e.homEquiv K L).injective
  ext1
  simp only [ComplexShape.Embedding.homEquiv_apply_coe, isoExtendRestriction, asIso_hom,
    ComplexShape.Embedding.homRestrict_comp_extendMap,
    ComplexShape.Embedding.homRestrict_liftExtend, Category.id_comp]

/-- Restriction commutes with applying a functor, on morphisms into an extension. -/
lemma homRestrict_map_comp_mapExtendIso_hom {D : Type*} [Category* D] [HasZeroMorphisms D]
    [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {K : HomologicalComplex C c'}
    {L : HomologicalComplex C c} (φ : K ⟶ L.extend e) :
    e.homRestrict ((F.mapHomologicalComplex c').map φ ≫ (L.mapExtendIso e F).hom) =
      ((F.mapHomologicalComplex c).map (e.homRestrict φ) :
        (F.mapHomologicalComplex c).obj (K.restriction e) ⟶ _) := by
  ext i
  simp [e.homRestrict_f _ rfl, mapExtendIso, mapExtendX_hom_eq _ _ (e.r_f i),
    restrictionXIso, extendXIso, extend.XIso, eqToHom_map]

end HasZero

section Abelian

variable [Abelian C]

/-- A morphism `φ : K ⟶ L.extend e` from a complex strictly supported on `e` is a
quasi-isomorphism if and only if the corresponding morphism `K.restriction e ⟶ L` is. -/
lemma quasiIso_iff_quasiIso_homRestrict {K : HomologicalComplex C c'} [K.IsStrictlySupported e]
    {L : HomologicalComplex C c} (φ : K ⟶ L.extend e) :
    QuasiIso φ ↔ QuasiIso (e.homRestrict φ) := by
  conv_lhs => rw [eq_isoExtendRestriction_hom_comp e φ]
  rw [quasiIso_iff_comp_left, quasiIso_extendMap_iff]

end Abelian

end HomologicalComplex
