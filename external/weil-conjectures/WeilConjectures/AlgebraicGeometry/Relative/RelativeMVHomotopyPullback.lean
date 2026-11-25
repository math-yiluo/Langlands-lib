/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! Generic exact rows and homotopy-pullback projections.

## References

* Stacks Project, Cohomology of Sheaves, Tags 08BV and 08HY
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CochainComplex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry

universe u w
variable {C : Type u} [Category C] [Abelian C]

local instance : (ShortComplex.π₁ : ShortComplex C ⥤ C).Additive where
local instance : (ShortComplex.π₂ : ShortComplex C ⥤ C).Additive where
local instance : (ShortComplex.π₃ : ShortComplex C ⥤ C).Additive where

private def additiveBiprodIso {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (X Y : C)
    [HasBinaryBiproduct (F.obj X) (F.obj Y)] : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y where
  hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total,
      F.map_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [← F.map_comp]

private lemma row_biprod_shortExact (S T : ShortComplex C) (hS : S.ShortExact)
    (hT : T.ShortExact) : (S ⊞ T).ShortExact := by
  let e₁ : (S ⊞ T).X₁ ≅ S.X₁ ⊞ T.X₁ := additiveBiprodIso ShortComplex.π₁ S T
  let e₂ : (S ⊞ T).X₂ ≅ S.X₂ ⊞ T.X₂ := additiveBiprodIso ShortComplex.π₂ S T
  let e₃ : (S ⊞ T).X₃ ≅ S.X₃ ⊞ T.X₃ := additiveBiprodIso ShortComplex.π₃ S T
  have hf : e₁.hom ≫ biprod.map S.f T.f =
      (S ⊞ T).f ≫ e₂.hom := by
    dsimp only [e₁, e₂, e₃, additiveBiprodIso, ShortComplex.π₁,
      ShortComplex.π₂, ShortComplex.π₃]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst,
        biprod.lift_fst_assoc]
      exact (biprod.fst : S ⊞ T ⟶ S).comm₁₂
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd,
        biprod.lift_snd_assoc]
      exact (biprod.snd : S ⊞ T ⟶ T).comm₁₂
  have hg : e₂.hom ≫ biprod.map S.g T.g =
      (S ⊞ T).g ≫ e₃.hom := by
    dsimp only [e₁, e₂, e₃, additiveBiprodIso, ShortComplex.π₁,
      ShortComplex.π₂, ShortComplex.π₃]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst,
        biprod.lift_fst_assoc]
      exact (biprod.fst : S ⊞ T ⟶ S).comm₂₃
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd,
        biprod.lift_snd_assoc]
      exact (biprod.snd : S ⊞ T ⟶ T).comm₂₃
  have := hS.mono_f
  have := hT.mono_f
  have := hS.epi_g
  have := hT.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.exact_iff_isZero_homology _).2
    have hz : IsZero (S.homology ⊞ T.homology) := (biprod_isZero_iff _ _).2
      ⟨(S.exact_iff_isZero_homology).1 hS.exact,
        (T.exact_iff_isZero_homology).1 hT.exact⟩
    exact hz.of_iso (additiveBiprodIso (ShortComplex.homologyFunctor C) S T)
  · have : Mono ((S ⊞ T).f ≫ e₂.hom) := by
      rw [← hf]
      infer_instance
    exact mono_of_mono _ e₂.hom
  · have : Epi ((S ⊞ T).g ≫ e₃.hom) := by
      rw [← hg]
      infer_instance
    exact (epi_comp_iff_of_isIso _ e₃.hom).1 this

private def complexOfRow (S : ShortComplex (CochainComplex C ℤ)) :
    CochainComplex (ShortComplex C) ℤ where
  X n := S.map (HomologicalComplex.eval C (.up ℤ) n)
  d n m :=
    { τ₁ := S.X₁.d n m
      τ₂ := S.X₂.d n m
      τ₃ := S.X₃.d n m
      comm₁₂ := (S.f.comm n m).symm
      comm₂₃ := (S.g.comm n m).symm }
  shape n m h := by ext <;> exact HomologicalComplex.shape _ n m h
  d_comp_d' n m k hn hk := by ext <;> exact HomologicalComplex.d_comp_d _ n m k

private def rowOfComplex (K : CochainComplex (ShortComplex C) ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    ((ShortComplex.π₁Toπ₂.mapHomologicalComplex (.up ℤ)).app K)
    ((ShortComplex.π₂Toπ₃.mapHomologicalComplex (.up ℤ)).app K)
    (by ext n; exact (K.X n).zero)

private def rowOfComplexMap {K L : CochainComplex (ShortComplex C) ℤ} (f : K ⟶ L) :
    rowOfComplex K ⟶ rowOfComplex L where
  τ₁ := (ShortComplex.π₁.mapHomologicalComplex (.up ℤ)).map f
  τ₂ := (ShortComplex.π₂.mapHomologicalComplex (.up ℤ)).map f
  τ₃ := (ShortComplex.π₃.mapHomologicalComplex (.up ℤ)).map f
  comm₁₂ := by ext n; exact (f.f n).comm₁₂
  comm₂₃ := by ext n; exact (f.f n).comm₂₃

private def complexOfRowMap {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T) :
    complexOfRow S ⟶ complexOfRow T where
  f n :=
    { τ₁ := f.τ₁.f n
      τ₂ := f.τ₂.f n
      τ₃ := f.τ₃.f n
      comm₁₂ := congrArg (fun t ↦ t.f n) f.comm₁₂
      comm₂₃ := congrArg (fun t ↦ t.f n) f.comm₂₃ }
  comm' n m h := by
    ext
    · exact f.τ₁.comm n m
    · exact f.τ₂.comm n m
    · exact f.τ₃.comm n m

private lemma rowOfComplex_shortExact (K : CochainComplex (ShortComplex C) ℤ)
    (hK : ∀ n, (K.X n).ShortExact) : (rowOfComplex K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  exact hK

private lemma complexOfRow_shortExact (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (n : ℤ) : ((complexOfRow S).X n).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n

private lemma coneRow_shortExact {K L : CochainComplex (ShortComplex C) ℤ} (f : K ⟶ L)
    (hK : ∀ n, (K.X n).ShortExact) (hL : ∀ n, (L.X n).ShortExact) :
    (rowOfComplex (mappingCone f)).ShortExact := by
  apply rowOfComplex_shortExact
  intro n
  exact ShortComplex.shortExact_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
    (row_biprod_shortExact _ _ (hK (n + 1)) (hL n))

private lemma coconeRow_shortExact {K L : CochainComplex (ShortComplex C) ℤ} (f : K ⟶ L)
    (hK : ∀ n, (K.X n).ShortExact) (hL : ∀ n, (L.X n).ShortExact) :
    (rowOfComplex (mappingCocone f)).ShortExact := by
  apply rowOfComplex_shortExact
  intro n
  change ((mappingCone f).X (n + -1)).ShortExact
  exact (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (rowOfComplex (mappingCone f))).1 (coneRow_shortExact f hK hL) (n + -1)

section
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]
open Pretriangulated

private lemma triangle_pullback_fst_isIso (T : Triangle D) (hT : T ∈ distTriang D)
    {A B : D} (e : T.obj₂ ≅ A ⊞ B) (u : A ⟶ T.obj₃) (v : B ⟶ T.obj₃)
    [IsIso v] (hf : e.inv ≫ T.mor₂ = biprod.desc u (-v)) :
    IsIso (T.mor₁ ≫ e.hom ≫ biprod.fst) := by
  have he : Epi (biprod.desc u (-v)) := by
    have : Epi ((biprod.inr : B ⟶ A ⊞ B) ≫ biprod.desc u (-v)) := by
      rw [biprod.inr_desc]
      infer_instance
    exact epi_of_epi (biprod.inr : B ⟶ A ⊞ B) _
  have : Epi T.mor₂ := by
    have : Epi (e.inv ≫ T.mor₂) := by rw [hf]; exact he
    exact epi_of_epi e.inv _
  have hz : T.mor₃ = 0 := by
    rw [← cancel_epi T.mor₂, comp_distTriang_mor_zero₂₃ _ hT, comp_zero]
  have hm : Mono T.mor₁ := T.mono₁ hT hz
  let j : A ⟶ T.obj₂ := biprod.lift (𝟙 A) (u ≫ inv v) ≫ e.inv
  have hj : j ≫ T.mor₂ = 0 := by
    simp [j, Category.assoc, hf, biprod.lift_desc]
  obtain ⟨s, hs⟩ := T.coyoneda_exact₂ hT j hj
  have hsp : s ≫ (T.mor₁ ≫ e.hom ≫ biprod.fst) = 𝟙 A := by
    rw [← Category.assoc, ← hs]
    simp [j]
  have hzero : T.mor₁ ≫ e.hom ≫ biprod.fst ≫ u =
      T.mor₁ ≫ e.hom ≫ biprod.snd ≫ v := by
    have h := comp_distTriang_mor_zero₁₂ T hT
    have hf' : T.mor₂ = e.hom ≫ biprod.desc u (-v) := by
      rw [← hf, Iso.hom_inv_id_assoc]
    rw [hf', ← Category.assoc, biprod.desc_eq, Preadditive.comp_add,
      Preadditive.comp_neg, Preadditive.comp_neg, add_neg_eq_zero] at h
    simpa only [Category.assoc] using h
  have : Mono (T.mor₁ ≫ e.hom ≫ biprod.fst) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro Z x hx
    have hxs : x ≫ T.mor₁ ≫ e.hom ≫ biprod.snd = 0 := by
      rw [← cancel_mono v, zero_comp]
      simp only [Category.assoc]
      rw [← hzero]
      simpa only [Category.assoc, zero_comp] using congrArg (fun k ↦ k ≫ u) hx
    have hxh : x ≫ T.mor₁ = 0 := by
      rw [← cancel_mono e.hom, zero_comp]
      apply biprod.hom_ext
      · simpa only [Category.assoc, zero_comp] using hx
      · simpa only [Category.assoc, zero_comp] using hxs
    exact (cancel_mono T.mor₁).1 (by simpa using hxh)
  refine ⟨s, ?_, hsp⟩
  rw [← cancel_mono (T.mor₁ ≫ e.hom ≫ biprod.fst)]
  simp only [Category.assoc, hsp, Category.comp_id, Category.id_comp]
end

section
variable [HasDerivedCategory.{w} C]
variable {E : Type*} [Category E] [Abelian E]
open Pretriangulated

private lemma map_cocone_triangle_distinguished {K L : CochainComplex E ℤ} (f : K ⟶ L)
    (F : E ⥤ C) [F.Additive] :
    DerivedCategory.Q.mapTriangle.obj
      ((F.mapHomologicalComplex (.up ℤ)).mapTriangle.obj (mappingCocone.triangle f)) ∈
      distTriang (DerivedCategory C) := by
  let H := F.mapHomologicalComplex (.up ℤ)
  rw [rotate_distinguished_triangle]
  let e : (DerivedCategory.Q.mapTriangle.obj
      (H.mapTriangle.obj (mappingCocone.triangle f))).rotate ≅
      DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (H.map f)) :=
    DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
      DerivedCategory.Q.mapTriangle.mapIso (H.mapTriangleRotateIso.app _) ≪≫
      DerivedCategory.Q.mapTriangle.mapIso
        (H.mapTriangle.mapIso (mappingCocone.rotateTriangleIso f)) ≪≫
      DerivedCategory.Q.mapTriangle.mapIso (mappingCone.mapTriangleIso f F)
  exact isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished
    (H.map f)) _ e

private lemma map_cocone_pullback_isIso (F : E ⥤ C) [F.Additive]
    {K L M : CochainComplex E ℤ} (u : K ⟶ M) (v : L ⟶ M)
    [IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map v))] :
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      (mappingCocone.fst (biprod.desc u (-v)) ≫ biprod.fst))) := by
  let H := F.mapHomologicalComplex (.up ℤ)
  let T := DerivedCategory.Q.mapTriangle.obj
    (H.mapTriangle.obj (mappingCocone.triangle (biprod.desc u (-v))))
  let e := additiveBiprodIso (H ⋙ DerivedCategory.Q) K L
  have hf : e.inv ≫ T.mor₂ = biprod.desc (DerivedCategory.Q.map (H.map u))
      (-DerivedCategory.Q.map (H.map v)) := by
    change biprod.desc (DerivedCategory.Q.map (H.map biprod.inl))
      (DerivedCategory.Q.map (H.map biprod.inr)) ≫
      DerivedCategory.Q.map (H.map (biprod.desc u (-v))) = _
    apply biprod.hom_ext' <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, ← Functor.map_comp,
        biprod.inl_desc, biprod.inr_desc, Functor.map_neg]
  have hi := triangle_pullback_fst_isIso T
    (map_cocone_triangle_distinguished (biprod.desc u (-v)) F) e
    (DerivedCategory.Q.map (H.map u)) (DerivedCategory.Q.map (H.map v)) hf
  have ha : T.mor₁ ≫ e.hom ≫ biprod.fst =
      DerivedCategory.Q.map (H.map (mappingCocone.fst (biprod.desc u (-v)) ≫ biprod.fst)) := by
    dsimp only [T, Functor.mapTriangle, mappingCocone.triangle, Triangle.mk,
      e, additiveBiprodIso, Functor.comp_map]
    simp only [biprod.lift_fst, Functor.map_comp]
  rw [← ha]
  exact hi
end

section
variable [HasDerivedCategory.{w} C]
variable {E : Type*} [Category E] [Abelian E]
open Pretriangulated

private lemma map_cocone_span_eq (F : E ⥤ C) [F.Additive]
    {K L M : CochainComplex E ℤ} (u : K ⟶ M) (v : L ⟶ M) :
    let H := F.mapHomologicalComplex (.up ℤ)
    DerivedCategory.Q.map (H.map (mappingCocone.fst (biprod.desc u (-v)) ≫ biprod.fst)) ≫
        DerivedCategory.Q.map (H.map u) =
      DerivedCategory.Q.map (H.map
          (mappingCocone.fst (biprod.desc u (-v)) ≫ biprod.snd)) ≫
        DerivedCategory.Q.map (H.map v) := by
  dsimp only
  let H := F.mapHomologicalComplex (.up ℤ)
  have hz := comp_distTriang_mor_zero₁₂ _
    (map_cocone_triangle_distinguished (biprod.desc u (-v)) F)
  change DerivedCategory.Q.map (H.map (mappingCocone.fst (biprod.desc u (-v)))) ≫
    DerivedCategory.Q.map (H.map (biprod.desc u (-v))) = 0 at hz
  rw [biprod.desc_eq] at hz
  simp only [Functor.map_add, Functor.map_comp, Functor.map_neg,
    Preadditive.comp_add, Preadditive.comp_neg, add_neg_eq_zero] at hz
  simp only [Functor.map_comp, Category.assoc]
  rw [biprod.desc_eq]
  exact hz

/-- Strictify a pair of row maps whose second map is a derived isomorphism componentwise.
The mapping-cocone row is short exact degreewise, its projection to the source row is a
localized isomorphism, and the two projections satisfy the span equations. -/
theorem relativeMV_homotopyPullback_row_strictify
    (S T R : ShortComplex (CochainComplex C ℤ)) (u : S ⟶ R) (v : T ⟶ R)
    (hS : S.ShortExact) (hT : T.ShortExact) (hR : R.ShortExact)
    [IsIso (DerivedCategory.Q.map v.τ₁)]
    [IsIso (DerivedCategory.Q.map v.τ₂)]
    [IsIso (DerivedCategory.Q.map v.τ₃)] :
    ∃ (P : ShortComplex (CochainComplex C ℤ)) (p : P ⟶ S) (m : P ⟶ T),
      P.ShortExact ∧ IsIso (DerivedCategory.Q.map p.τ₁) ∧
      IsIso (DerivedCategory.Q.map p.τ₂) ∧ IsIso (DerivedCategory.Q.map p.τ₃) ∧
      DerivedCategory.Q.map p.τ₁ ≫ DerivedCategory.Q.map u.τ₁ =
        DerivedCategory.Q.map m.τ₁ ≫ DerivedCategory.Q.map v.τ₁ ∧
      DerivedCategory.Q.map p.τ₂ ≫ DerivedCategory.Q.map u.τ₂ =
        DerivedCategory.Q.map m.τ₂ ≫ DerivedCategory.Q.map v.τ₂ ∧
      DerivedCategory.Q.map p.τ₃ ≫ DerivedCategory.Q.map u.τ₃ =
        DerivedCategory.Q.map m.τ₃ ≫ DerivedCategory.Q.map v.τ₃ := by
  let K := complexOfRow S
  let L := complexOfRow T
  let M := complexOfRow R
  let a := complexOfRowMap u
  let b := complexOfRowMap v
  let δ : K ⊞ L ⟶ M := biprod.desc a (-b)
  let P := rowOfComplex (mappingCocone δ)
  let p : P ⟶ S := rowOfComplexMap (mappingCocone.fst δ ≫ biprod.fst)
  let m : P ⟶ T := rowOfComplexMap (mappingCocone.fst δ ≫ biprod.snd)
  have hp : P.ShortExact := by
    apply coconeRow_shortExact δ
    · intro n
      exact ShortComplex.shortExact_of_iso
        (additiveBiprodIso (HomologicalComplex.eval _ _ n) K L).symm
        (row_biprod_shortExact _ _ (complexOfRow_shortExact S hS n)
          (complexOfRow_shortExact T hT n))
    · exact complexOfRow_shortExact R hR
  have hb₁ : IsIso (DerivedCategory.Q.map
      ((ShortComplex.π₁.mapHomologicalComplex (.up ℤ)).map b)) := by
    change IsIso (DerivedCategory.Q.map v.τ₁)
    infer_instance
  have hb₂ : IsIso (DerivedCategory.Q.map
      ((ShortComplex.π₂.mapHomologicalComplex (.up ℤ)).map b)) := by
    change IsIso (DerivedCategory.Q.map v.τ₂)
    infer_instance
  have hb₃ : IsIso (DerivedCategory.Q.map
      ((ShortComplex.π₃.mapHomologicalComplex (.up ℤ)).map b)) := by
    change IsIso (DerivedCategory.Q.map v.τ₃)
    infer_instance
  refine ⟨P, p, m, hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact map_cocone_pullback_isIso ShortComplex.π₁ a b
  · exact map_cocone_pullback_isIso ShortComplex.π₂ a b
  · exact map_cocone_pullback_isIso ShortComplex.π₃ a b
  · exact map_cocone_span_eq ShortComplex.π₁ a b
  · exact map_cocone_span_eq ShortComplex.π₂ a b
  · exact map_cocone_span_eq ShortComplex.π₃ a b
end
end AlgebraicGeometry
end
