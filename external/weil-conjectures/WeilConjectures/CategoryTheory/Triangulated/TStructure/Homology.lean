/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The cohomology functor of a t-structure is homological

Let `t` be a t-structure on a triangulated category `C`. The functor
`H⁰ = τ_{≥ 0} τ_{≤ 0} : C ⥤ t.heart.FullSubcategory` to the (abelian) heart is a homological
functor (blueprint `lemma-perverse-sheaves-curve--1` (5)). Combined with the shift, a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` thus induces a long exact sequence
`⋯ ⟶ Hⁱ X ⟶ Hⁱ Y ⟶ Hⁱ Z ⟶ Hⁱ⁺¹ X ⟶ ⋯` in the heart.

The proof follows [BBD, Théorème 1.3.6]: the sequence `H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z` is left exact if
`X, Y, Z ≥ 0` and right exact if `X, Y, Z ≤ 0`, by adjunction; the general case is reduced to
these by the octahedral axiom.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

/-- The heart of a t-structure, as a full subcategory, is an abelian category. -/
noncomputable instance abelianHeartFullSubcategory : Abelian t.heart.FullSubcategory :=
  letI := t.hasHeartFullSubcategory
  t.abelianHeart t.heart.FullSubcategory

/-- Blueprint `lemma-perverse-sheaves-curve--1` (1): the cohomology functor
`H⁰ = τ_{≥ 0} τ_{≤ 0}`, with values in the heart. -/
noncomputable def homology₀ : C ⥤ t.heart.FullSubcategory :=
  t.heart.lift (t.truncGELE 0 0) (fun _ ↦ (t.mem_heart_iff _).2 ⟨inferInstance, inferInstance⟩)

@[simp]
lemma homology₀_obj_obj (X : C) :
    (t.homology₀.obj X).obj = (t.truncGE 0).obj ((t.truncLE 0).obj X) :=
  rfl

@[simp]
lemma homology₀_map_hom {X Y : C} (φ : X ⟶ Y) :
    (t.homology₀.map φ).hom = (t.truncGE 0).map ((t.truncLE 0).map φ) :=
  rfl

instance : t.homology₀.Additive where
  map_add {X Y f g} := t.heart.ι.map_injective (by
    rw [t.heart.ι.map_add, ObjectProperty.ι_map, ObjectProperty.ι_map, ObjectProperty.ι_map,
      homology₀_map_hom, homology₀_map_hom, homology₀_map_hom, (t.truncLE 0).map_add,
      (t.truncGE 0).map_add])

lemma isIso_homology₀_map_iff {X Y : C} (φ : X ⟶ Y) :
    IsIso (t.homology₀.map φ) ↔ IsIso ((t.truncGE 0).map ((t.truncLE 0).map φ)) := by
  rw [← homology₀_map_hom, ← ObjectProperty.ι_map]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ isIso_of_fully_faithful t.heart.ι _⟩

instance (X : C) : IsIso (t.homology₀.map ((t.truncLEι 0).app X)) := by
  rw [isIso_homology₀_map_iff]
  infer_instance

instance (X : C) : IsIso (t.homology₀.map ((t.truncGEπ 0).app X)) := by
  rw [isIso_homology₀_map_iff]
  have := t.isIso_truncGE_map_truncGEπ_app 0 0 le_rfl X
  change IsIso ((t.truncGELE 0 0).map ((t.truncGEπ 0).app X))
  rw [NatIso.isIso_map_iff (t.truncGELEIsoLEGE 0 0)]
  dsimp
  infer_instance

section Adjunction

/-- For `K ≥ 0`, the canonical morphism `H⁰ K = τ_{≥ 0} τ_{≤ 0} K ≅ τ_{≤ 0} K ⟶ K`. -/
noncomputable def homology₀ε (K : C) [t.IsGE K 0] : (t.homology₀.obj K).obj ⟶ K :=
  inv ((t.truncGEπ 0).app ((t.truncLE 0).obj K)) ≫ (t.truncLEι 0).app K

lemma homology₀ε_naturality {K K' : C} [t.IsGE K 0] [t.IsGE K' 0] (φ : K ⟶ K') :
    (t.homology₀.map φ).hom ≫ t.homology₀ε K' = t.homology₀ε K ≫ φ := by
  dsimp [homology₀ε]
  rw [← cancel_epi ((t.truncGEπ 0).app ((t.truncLE 0).obj K))]
  simp only [assoc, IsIso.hom_inv_id_assoc]
  erw [← (t.truncGEπ 0).naturality_assoc]
  simp

/-- For `A` in the heart and `K ≥ 0`, morphisms `A ⟶ H⁰ K` are morphisms `A ⟶ K`. -/
noncomputable def homology₀εEquiv (A : t.heart.FullSubcategory) (K : C) [t.IsGE K 0] :
    (A ⟶ t.homology₀.obj K) ≃ (A.obj ⟶ K) :=
  have : t.IsLE A.obj 0 := ⟨A.property.1⟩
  { toFun x := x.hom ≫ t.homology₀ε K
    invFun y := ObjectProperty.homMk (t.liftTruncLE y 0 ≫ (t.truncGEπ 0).app _)
    left_inv x := by
      refine ObjectProperty.hom_ext _ ?_
      dsimp [homology₀ε]
      rw [← cancel_mono (inv ((t.truncGEπ 0).app ((t.truncLE 0).obj K))), assoc,
        IsIso.hom_inv_id, comp_id]
      exact t.to_truncLE_obj_ext (by simp)
    right_inv y := by simp [homology₀ε] }

lemma homology₀εEquiv_comp {A : t.heart.FullSubcategory} {K K' : C} [t.IsGE K 0]
    [t.IsGE K' 0] (x : A ⟶ t.homology₀.obj K) (φ : K ⟶ K') :
    t.homology₀εEquiv A K' (x ≫ t.homology₀.map φ) = t.homology₀εEquiv A K x ≫ φ := by
  simp only [homology₀εEquiv, Equiv.coe_fn_mk, ObjectProperty.FullSubcategory.comp_hom, assoc,
    homology₀ε_naturality]

/-- For `K ≤ 0`, the canonical morphism `K ≅ τ_{≤ 0} K ⟶ τ_{≥ 0} τ_{≤ 0} K = H⁰ K`. -/
noncomputable def homology₀η (K : C) [t.IsLE K 0] : K ⟶ (t.homology₀.obj K).obj :=
  inv ((t.truncLEι 0).app K) ≫ (t.truncGEπ 0).app ((t.truncLE 0).obj K)

lemma homology₀η_naturality {K K' : C} [t.IsLE K 0] [t.IsLE K' 0] (φ : K ⟶ K') :
    t.homology₀η K ≫ (t.homology₀.map φ).hom = φ ≫ t.homology₀η K' := by
  dsimp [homology₀η]
  have h₁ : inv ((t.truncLEι 0).app K) ≫ (t.truncLE 0).map φ =
      φ ≫ inv ((t.truncLEι 0).app K') := by
    rw [IsIso.inv_comp_eq, ← assoc, IsIso.eq_comp_inv]
    exact ((t.truncLEι 0).naturality φ)
  rw [assoc]
  erw [← (t.truncGEπ 0).naturality]
  rw [Functor.id_map, reassoc_of% h₁]

/-- For `K ≤ 0` and `B` in the heart, morphisms `H⁰ K ⟶ B` are morphisms `K ⟶ B`. -/
noncomputable def homology₀ηEquiv (K : C) [t.IsLE K 0] (B : t.heart.FullSubcategory) :
    (t.homology₀.obj K ⟶ B) ≃ (K ⟶ B.obj) :=
  have : t.IsGE B.obj 0 := ⟨B.property.2⟩
  { toFun x := t.homology₀η K ≫ x.hom
    invFun y := ObjectProperty.homMk (t.descTruncGE ((t.truncLEι 0).app K ≫ y) 0)
    left_inv x := by
      refine ObjectProperty.hom_ext _ (t.from_truncGE_obj_ext ?_)
      simp [homology₀η]
    right_inv y := by simp [homology₀η] }

lemma homology₀ηEquiv_comp {K K' : C} [t.IsLE K 0] [t.IsLE K' 0]
    {B : t.heart.FullSubcategory} (φ : K ⟶ K') (x : t.homology₀.obj K' ⟶ B) :
    t.homology₀ηEquiv K B (t.homology₀.map φ ≫ x) = φ ≫ t.homology₀ηEquiv K' B x := by
  simp only [homology₀ηEquiv, Equiv.coe_fn_mk, ObjectProperty.FullSubcategory.comp_hom,
    ← assoc, homology₀η_naturality]

lemma homology₀εEquiv_zero (A : t.heart.FullSubcategory) (K : C) [t.IsGE K 0] :
    t.homology₀εEquiv A K 0 = 0 := by
  simp [homology₀εEquiv]

lemma homology₀ηEquiv_zero (K : C) [t.IsLE K 0] (B : t.heart.FullSubcategory) :
    t.homology₀ηEquiv K B 0 = 0 := by
  simp [homology₀ηEquiv]

end Adjunction

/-- The short complex `H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z` attached to a distinguished triangle. -/
noncomputable abbrev homology₀ShortComplex (T : Triangle C) (hT : T ∈ distTriang C) :
    ShortComplex t.heart.FullSubcategory :=
  ShortComplex.mk (t.homology₀.map T.mor₁) (t.homology₀.map T.mor₂) (by
    rw [← t.homology₀.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])

/-- Step (a), left exactness: if `X, Y, Z ≥ 0`, then `0 ⟶ H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z` is exact. -/
lemma homology₀_exact_mono_of_isGE (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : t.IsGE T.obj₁ 0) (h₂ : t.IsGE T.obj₂ 0) (h₃ : t.IsGE T.obj₃ 0) :
    (t.homology₀ShortComplex T hT).Exact ∧ Mono (t.homology₀.map T.mor₁) := by
  have hmono : Mono (t.homology₀.map T.mor₁) := by
    rw [mono_iff_cancel_zero]
    intro A x hx
    have : t.IsLE A.obj 0 := ⟨A.property.1⟩
    apply (t.homology₀εEquiv A T.obj₁).injective
    rw [homology₀εEquiv_zero]
    have hu : t.homology₀εEquiv A T.obj₁ x ≫ T.mor₁ = 0 := by
      rw [← homology₀εEquiv_comp, hx, homology₀εEquiv_zero]
    refine eq_zero_of_shift_map_eq_zero _ 1 ?_
    obtain ⟨w, hw⟩ := Triangle.coyoneda_exact₁ T hT
      ((t.homology₀εEquiv A T.obj₁ x)⟦(1 : ℤ)⟧') (by rw [← Functor.map_comp, hu, Functor.map_zero])
    have : t.IsLE (A.obj⟦(1 : ℤ)⟧) (-1) := t.isLE_shift _ 0 1 (-1) (by lia)
    rw [hw, t.zero w (-1) 0 (by lia), zero_comp]
  refine ⟨?_, hmono⟩
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  have : t.IsLE A.obj 0 := ⟨A.property.1⟩
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ T hT (t.homology₀εEquiv A T.obj₂ x₂) (by
    rw [← homology₀εEquiv_comp, hx₂, homology₀εEquiv_zero])
  refine ⟨A, 𝟙 _, inferInstance, (t.homology₀εEquiv A T.obj₁).symm y, ?_⟩
  apply (t.homology₀εEquiv A T.obj₂).injective
  dsimp
  rw [id_comp, homology₀εEquiv_comp, Equiv.apply_symm_apply, hy]

/-- Step (a), right exactness: if `X, Y, Z ≤ 0`, then `H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z ⟶ 0` is exact. -/
lemma homology₀_exact_epi_of_isLE (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : t.IsLE T.obj₁ 0) (h₂ : t.IsLE T.obj₂ 0) (h₃ : t.IsLE T.obj₃ 0) :
    (t.homology₀ShortComplex T hT).Exact ∧ Epi (t.homology₀.map T.mor₂) := by
  have hepi : Epi (t.homology₀.map T.mor₂) := by
    rw [epi_iff_cancel_zero]
    intro B x hx
    have : t.IsGE B.obj 0 := ⟨B.property.2⟩
    apply (t.homology₀ηEquiv T.obj₃ B).injective
    rw [homology₀ηEquiv_zero]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₃ T hT (t.homology₀ηEquiv T.obj₃ B x) (by
      rw [← homology₀ηEquiv_comp, hx, homology₀ηEquiv_zero])
    have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) := t.isLE_shift _ 0 1 (-1) (by lia)
    rw [hw, t.zero w (-1) 0 (by lia), comp_zero]
  have key : ∀ {B : t.heart.FullSubcategory} (x : t.homology₀.obj T.obj₂ ⟶ B),
      t.homology₀.map T.mor₁ ≫ x = 0 → ∃ y, t.homology₀.map T.mor₂ ≫ y = x := by
    intro B x hx
    have : t.IsGE B.obj 0 := ⟨B.property.2⟩
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ T hT (t.homology₀ηEquiv T.obj₂ B x) (by
      rw [← homology₀ηEquiv_comp, hx, homology₀ηEquiv_zero])
    refine ⟨(t.homology₀ηEquiv T.obj₃ B).symm y, (t.homology₀ηEquiv T.obj₂ B).injective ?_⟩
    rw [homology₀ηEquiv_comp, Equiv.apply_symm_apply, hy]
  refine ⟨ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ _ _
    (fun x hx ↦ (key x hx).choose) (fun x hx ↦ (key x hx).choose_spec)
    (fun x hx m hm ↦ ?_)), hepi⟩
  rw [← cancel_epi (t.homology₀.map T.mor₂)]
  exact hm.trans (key x hx).choose_spec.symm

/-- Step (b), left exactness: if `Z ≥ 0`, then `0 ⟶ H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z` is exact. -/
lemma homology₀_exact_mono_of_isGE₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₃ : t.IsGE T.obj₃ 0) :
    (t.homology₀ShortComplex T hT).Exact ∧ Mono (t.homology₀.map T.mor₁) := by
  have h₁₂ : Triangle.mk ((t.truncLEι (-1)).app T.obj₁) ((t.truncGEπ 0).app T.obj₁)
      ((t.truncGEδLE (-1) 0 (by lia)).app T.obj₁) ∈ distTriang C :=
    t.triangleLEGE_distinguished (-1) 0 (by lia) T.obj₁
  obtain ⟨Y'', v, w, h₁₃⟩ := distinguished_cocone_triangle ((t.truncLEι (-1)).app T.obj₁ ≫ T.mor₁)
  let O := Triangulated.someOctahedron rfl h₁₂ hT h₁₃
  have hY'' : t.IsGE Y'' 0 := t.isGE₂ _ O.mem 0
    (inferInstanceAs (t.IsGE ((t.truncGE 0).obj T.obj₁) 0)) h₃
  obtain ⟨e, he⟩ := t.exists_iso_truncGE_of_distTriang _ _ _ h₁₃ (-1) 0 (by lia)
    (inferInstanceAs (t.IsLE ((t.truncLE (-1)).obj T.obj₁) (-1))) hY''
  have : IsIso (t.homology₀.map v) := by
    have : IsIso (t.homology₀.map v ≫ t.homology₀.map e.hom) := by
      rw [← Functor.map_comp, he]; infer_instance
    exact IsIso.of_isIso_comp_right _ (t.homology₀.map e.hom)
  obtain ⟨hex, hmono⟩ := t.homology₀_exact_mono_of_isGE _ O.mem
    (inferInstanceAs (t.IsGE ((t.truncGE 0).obj T.obj₁) 0)) hY'' h₃
  have hmono' : Mono (t.homology₀.map O.m₁) := hmono
  have e' : t.homology₀ShortComplex T hT ≅ t.homology₀ShortComplex _ O.mem :=
    ShortComplex.isoMk (asIso (t.homology₀.map ((t.truncGEπ 0).app T.obj₁)))
      (asIso (t.homology₀.map v)) (Iso.refl _)
      (by dsimp; rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ O.comm₁)
      (by dsimp; rw [comp_id, ← Functor.map_comp]; exact congrArg t.homology₀.map O.comm₃)
  refine ⟨(ShortComplex.exact_iff_of_iso e').2 hex, ?_⟩
  have : Mono (t.homology₀.map T.mor₁ ≫ t.homology₀.map v) := by
    rw [← Functor.map_comp, ← O.comm₁, Functor.map_comp]
    infer_instance
  exact mono_of_mono _ (t.homology₀.map v)

/-- Step (b), right exactness: if `X ≤ 0`, then `H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z ⟶ 0` is exact. -/
lemma homology₀_exact_epi_of_isLE₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : t.IsLE T.obj₁ 0) :
    (t.homology₀ShortComplex T hT).Exact ∧ Epi (t.homology₀.map T.mor₂) := by
  have h₂₃ : Triangle.mk ((t.truncLEι 0).app T.obj₃) ((t.truncGEπ 1).app T.obj₃)
      ((t.truncGEδLE 0 1 rfl).app T.obj₃) ∈ distTriang C :=
    t.triangleLEGE_distinguished 0 1 rfl T.obj₃
  obtain ⟨Y', v, w, h₁₃⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ 1).app T.obj₃)
  let O := Triangulated.someOctahedron' rfl hT h₂₃ h₁₃
  have hY' : t.IsLE Y' 0 := t.isLE₂ _ O.mem 0 h₁
    (inferInstanceAs (t.IsLE ((t.truncLE 0).obj T.obj₃) 0))
  obtain ⟨e, he⟩ := t.exists_iso_truncLE_of_distTriang _ _ _ h₁₃ 0 1 rfl hY'
    (inferInstanceAs (t.IsGE ((t.truncGE 1).obj T.obj₃) 1))
  have : IsIso (t.homology₀.map v) := by
    rw [he, Functor.map_comp]
    infer_instance
  obtain ⟨hex, hepi⟩ := t.homology₀_exact_epi_of_isLE _ O.mem h₁ hY'
    (inferInstanceAs (t.IsLE ((t.truncLE 0).obj T.obj₃) 0))
  have hepi' : Epi (t.homology₀.map O.m₃) := hepi
  have e' : t.homology₀ShortComplex _ O.mem ≅ t.homology₀ShortComplex T hT :=
    ShortComplex.isoMk (Iso.refl _) (asIso (t.homology₀.map v))
      (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₃)))
      (by dsimp; rw [id_comp, ← Functor.map_comp]; exact (congrArg _ O.comm₁).symm)
      (by dsimp; rw [← Functor.map_comp, ← Functor.map_comp]; exact (congrArg _ O.comm₄).symm)
  refine ⟨(ShortComplex.exact_iff_of_iso e').1 hex, ?_⟩
  have : Epi (t.homology₀.map v ≫ t.homology₀.map T.mor₂) := by
    rw [← Functor.map_comp, ← O.comm₄, Functor.map_comp]
    infer_instance
  exact epi_of_epi (t.homology₀.map v) _

/-- Blueprint `lemma-perverse-sheaves-curve--1` (5): for a distinguished triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧`, the sequence `H⁰ X ⟶ H⁰ Y ⟶ H⁰ Z` is exact. -/
lemma homology₀_exact (T : Triangle C) (hT : T ∈ distTriang C) :
    (t.homology₀ShortComplex T hT).Exact := by
  have h₁₂ : Triangle.mk ((t.truncLEι 0).app T.obj₁) ((t.truncGEπ 1).app T.obj₁)
      ((t.truncGEδLE 0 1 rfl).app T.obj₁) ∈ distTriang C :=
    t.triangleLEGE_distinguished 0 1 rfl T.obj₁
  obtain ⟨W, v, w, h₁₃⟩ := distinguished_cocone_triangle ((t.truncLEι 0).app T.obj₁ ≫ T.mor₁)
  let O := Triangulated.someOctahedron rfl h₁₂ hT h₁₃
  have hex := (t.homology₀_exact_epi_of_isLE₁ _ h₁₃
    (inferInstanceAs (t.IsLE ((t.truncLE 0).obj T.obj₁) 0))).1
  have hmono : Mono (t.homology₀.map O.m₃) :=
    (t.homology₀_exact_mono_of_isGE₃ _ (rot_of_distTriang _ O.mem)
      (t.isGE_shift ((t.truncGE 1).obj T.obj₁) 1 1 0 (by lia))).2
  let φ : t.homology₀ShortComplex _ h₁₃ ⟶ t.homology₀ShortComplex T hT :=
    { τ₁ := t.homology₀.map ((t.truncLEι 0).app T.obj₁)
      τ₂ := 𝟙 _
      τ₃ := t.homology₀.map O.m₃
      comm₁₂ := by dsimp; rw [comp_id, ← Functor.map_comp]
      comm₂₃ := by
        dsimp; rw [id_comp, ← Functor.map_comp]; exact (congrArg t.homology₀.map O.comm₃).symm }
  have : Mono φ.τ₃ := hmono
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex

/-- Blueprint `lemma-perverse-sheaves-curve--1` (5): the cohomology functor
`H⁰ : C ⥤ t.heart.FullSubcategory` is homological. -/
instance isHomological_homology₀ : t.homology₀.IsHomological where
  exact T hT := t.homology₀_exact T hT

end CategoryTheory.Triangulated.TStructure
