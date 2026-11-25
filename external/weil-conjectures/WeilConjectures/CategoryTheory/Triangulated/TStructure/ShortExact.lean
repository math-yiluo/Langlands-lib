/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Short exact sequences in the heart of a t-structure

Let `t` be a t-structure on a triangulated category `C`, with heart `H`, which is abelian
(`CategoryTheory.Triangulated.TStructure.abelianHeart`). This file records the basic dictionary
between the triangulated structure of `C` and the abelian structure of `H`
(blueprint `lemma-perverse-sheaves-curve--1`):

1. truncation triangles are unique up to unique isomorphism
   (`CategoryTheory.Triangulated.TStructure.triangle_hom_ext_of_isLE_of_isGE`,
   `CategoryTheory.Triangulated.TStructure.exists_iso_triangleLEGE`), and the truncation
   functors are adjoint to the inclusions
   (`CategoryTheory.Triangulated.TStructure.truncLEAdjunction`,
   `CategoryTheory.Triangulated.TStructure.truncGEAdjunction`); the commutation
   `τ_{≥ 0} τ_{≤ 0} ≅ τ_{≤ 0} τ_{≥ 0}` is `CategoryTheory.Triangulated.TStructure.truncGELEIsoLEGE`;
2. the subcategories `t.le n`, `t.ge n` (`CategoryTheory.Triangulated.TStructure.isLE₂`,
   `CategoryTheory.Triangulated.TStructure.isGE₂`) and the heart
   (`CategoryTheory.Triangulated.TStructure.heart₂`) are closed under extensions;
3. kernels and cokernels in `H` are computed by truncating a cone
   (`CategoryTheory.Triangulated.TStructure.exists_isLimit_kernelFork_of_distTriang`,
   `CategoryTheory.Triangulated.TStructure.exists_isColimit_cokernelCofork_of_distTriang`);
4. a sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` in `H` is short exact if and only if it extends to a
   distinguished triangle, and then the connecting morphism is unique
   (`CategoryTheory.Triangulated.TStructure.shortExact_iff_exists_distTriang`,
   `CategoryTheory.Triangulated.TStructure.eq_of_distTriang_of_heart`).

The fact that `H⁰` is a homological functor is in
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

section Truncation

omit [HasZeroObject C] [Pretriangulated C] in
/-- A morphism which becomes zero after a shift is zero. -/
lemma eq_zero_of_shift_map_eq_zero {X Y : C} (f : X ⟶ Y) (a : ℤ) (h : f⟦a⟧' = 0) : f = 0 :=
  (shiftFunctor C a).map_injective (by rw [h, Functor.map_zero])

/-- Blueprint `lemma-perverse-sheaves-curve--1` (1): two morphisms between distinguished
triangles of the form `A ⟶ K ⟶ B ⟶ A⟦1⟧` with `A ≤ n` and `B ≥ n + 1` which agree on the
middle term agree. In particular truncation triangles have no nontrivial automorphisms which are
the identity on the middle term. -/
lemma triangle_hom_ext_of_isLE_of_isGE {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (n : ℤ) (h₁ : t.IsLE T.obj₁ n) (h₃ : t.IsGE T'.obj₃ (n + 1))
    {f g : T ⟶ T'} (h : f.hom₂ = g.hom₂) : f = g := by
  have h₁' : f.hom₁ = g.hom₁ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_shift_map_eq_zero _ 1 ?_
    obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₁ T' hT' ((f.hom₁ - g.hom₁)⟦(1 : ℤ)⟧') (by
      rw [← Functor.map_comp, sub_comp, ← f.comm₁, ← g.comm₁, h, sub_self, Functor.map_zero])
    have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (n - 1) := t.isLE_shift _ n 1 (n - 1) (by lia)
    rw [hu, t.zero u (n - 1) (n + 1) (by lia), zero_comp]
  have h₃' : f.hom₃ = g.hom₃ := by
    rw [← sub_eq_zero]
    obtain ⟨u, hu⟩ := Triangle.yoneda_exact₃ T hT (f.hom₃ - g.hom₃) (by
      rw [comp_sub, f.comm₂, g.comm₂, h, sub_self])
    have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (n - 1) := t.isLE_shift _ n 1 (n - 1) (by lia)
    rw [hu, t.zero u (n - 1) (n + 1) (by lia), comp_zero]
  exact Triangle.hom_ext _ _ h₁' h h₃'

/-- Blueprint `lemma-perverse-sheaves-curve--1` (1): a distinguished triangle
`A ⟶ K ⟶ B ⟶ A⟦1⟧` with `A ≤ n` and `B ≥ n + 1` is isomorphic to the truncation triangle of `K`
by an isomorphism which is the identity on `K`. -/
lemma exists_iso_triangleLEGE (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ)
    (h₁ : t.IsLE T.obj₁ n) (h₃ : t.IsGE T.obj₃ (n + 1)) :
    ∃ (e : T ≅ (t.triangleLEGE n (n + 1) rfl).obj T.obj₂), e.hom.hom₂ = 𝟙 _ := by
  have hT₀ := t.triangleLEGE_distinguished n (n + 1) rfl T.obj₂
  have h₁₀ : t.IsLE ((t.triangleLEGE n (n + 1) rfl).obj T.obj₂).obj₁ n :=
    inferInstanceAs (t.IsLE ((t.truncLE n).obj T.obj₂) n)
  have h₃₀ : t.IsGE ((t.triangleLEGE n (n + 1) rfl).obj T.obj₂).obj₃ (n + 1) :=
    inferInstanceAs (t.IsGE ((t.truncGE (n + 1)).obj T.obj₂) (n + 1))
  -- the morphism `T ⟶ T₀`
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism _ _ hT hT₀
    (t.liftTruncLE T.mor₁ n) (𝟙 _) (by simp)
  let φ : T ⟶ (t.triangleLEGE n (n + 1) rfl).obj T.obj₂ :=
    Triangle.homMk _ _ (t.liftTruncLE T.mor₁ n) (𝟙 _) c (by simp) hc₁ hc₂
  -- the morphism `T₀ ⟶ T`
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ T hT ((t.truncLEι n).app T.obj₂)
    (t.zero _ n (n + 1) (by lia))
  obtain ⟨c', hc'₁, hc'₂⟩ := complete_distinguished_triangle_morphism _ _ hT₀ hT a (𝟙 _)
    (by simpa using ha)
  let ψ : (t.triangleLEGE n (n + 1) rfl).obj T.obj₂ ⟶ T :=
    Triangle.homMk _ _ a (𝟙 _) c' (by simpa using ha) hc'₁ hc'₂
  refine ⟨⟨φ, ψ, ?_, ?_⟩, rfl⟩
  · exact t.triangle_hom_ext_of_isLE_of_isGE hT hT n h₁ h₃ (by simp [φ, ψ])
  · exact t.triangle_hom_ext_of_isLE_of_isGE hT₀ hT₀ n h₁₀ h₃₀ (by simp [φ, ψ])

/-- In a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with `X ≤ n` and `Z ≥ n + 1`, the object `Z`
is `τ_{≥ n + 1} Y`. -/
lemma exists_iso_truncGE_of_distTriang {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang C) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)
    (h₁ : t.IsLE X n₀) (h₃ : t.IsGE Z n₁) :
    ∃ (e : Z ≅ (t.truncGE n₁).obj Y), g ≫ e.hom = (t.truncGEπ n₁).app Y := by
  subst hn
  obtain ⟨e, he⟩ := t.exists_iso_triangleLEGE _ hT n₀ h₁ h₃
  refine ⟨Triangle.π₃.mapIso e, ?_⟩
  have h' := e.hom.comm₂
  rw [he] at h'
  exact h'.trans (id_comp _)

/-- In a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with `X ≤ n` and `Z ≥ n + 1`, the object `X`
is `τ_{≤ n} Y`. -/
lemma exists_iso_truncLE_of_distTriang {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang C) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)
    (h₁ : t.IsLE X n₀) (h₃ : t.IsGE Z n₁) :
    ∃ (e : X ≅ (t.truncLE n₀).obj Y), f = e.hom ≫ (t.truncLEι n₀).app Y := by
  subst hn
  obtain ⟨e, he⟩ := t.exists_iso_triangleLEGE _ hT n₀ h₁ h₃
  refine ⟨Triangle.π₁.mapIso e, ?_⟩
  have h' := e.hom.comm₁
  rw [he] at h'
  exact (comp_id _).symm.trans h'

/-- Blueprint `lemma-perverse-sheaves-curve--1` (1): the truncation `τ_{≤ n}`, as a functor
to the subcategory `t.le n`. -/
noncomputable def truncLEFunctor (n : ℤ) : C ⥤ (t.le n).FullSubcategory :=
  (t.le n).lift (t.truncLE n) (fun _ ↦ t.le_of_isLE _ n)

/-- Blueprint `lemma-perverse-sheaves-curve--1` (1): the truncation `τ_{≥ n}`, as a functor
to the subcategory `t.ge n`. -/
noncomputable def truncGEFunctor (n : ℤ) : C ⥤ (t.ge n).FullSubcategory :=
  (t.ge n).lift (t.truncGE n) (fun _ ↦ t.ge_of_isGE _ n)

/-- Blueprint `lemma-perverse-sheaves-curve--1` (1): the truncation `τ_{≤ n}` is right adjoint
to the inclusion of `t.le n`. -/
noncomputable def truncLEAdjunction (n : ℤ) : (t.le n).ι ⊣ t.truncLEFunctor n :=
  Adjunction.mkOfHomEquiv
    { homEquiv A K :=
        have : t.IsLE ((t.le n).ι.obj A) n := ⟨A.property⟩
        have : t.IsLE A.obj n := ⟨A.property⟩
        { toFun f := ObjectProperty.homMk (t.liftTruncLE f n)
          invFun g := g.hom ≫ (t.truncLEι n).app K
          left_inv f := by simp
          right_inv g := by
            ext
            exact t.to_truncLE_obj_ext (by simp) }
      homEquiv_naturality_left_symm _ _ := by simp
      homEquiv_naturality_right {A K K'} f g := by
        have : t.IsLE ((t.le n).ι.obj A) n := ⟨A.property⟩
        have : t.IsLE A.obj n := ⟨A.property⟩
        ext
        exact t.to_truncLE_obj_ext (by simp [truncLEFunctor]) }

/-- Blueprint `lemma-perverse-sheaves-curve--1` (1): the truncation `τ_{≥ n}` is left adjoint
to the inclusion of `t.ge n`. -/
noncomputable def truncGEAdjunction (n : ℤ) : t.truncGEFunctor n ⊣ (t.ge n).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv K B :=
        have : t.IsGE ((t.ge n).ι.obj B) n := ⟨B.property⟩
        have : t.IsGE B.obj n := ⟨B.property⟩
        { toFun g := (t.truncGEπ n).app K ≫ g.hom
          invFun f := ObjectProperty.homMk (t.descTruncGE f n)
          left_inv g := by
            ext
            exact t.from_truncGE_obj_ext (by simp)
          right_inv f := by simp }
      homEquiv_naturality_left_symm {K K' B} f g := by
        have : t.IsGE ((t.ge n).ι.obj B) n := ⟨B.property⟩
        have : t.IsGE B.obj n := ⟨B.property⟩
        ext
        exact t.from_truncGE_obj_ext (by simp [truncGEFunctor])
      homEquiv_naturality_right _ _ := by simp }

end Truncation

section Extensions

/-- Blueprint `lemma-perverse-sheaves-curve--1` (2): the heart is closed under
extensions. -/
lemma heart₂ (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : t.heart T.obj₁)
    (h₃ : t.heart T.obj₃) : t.heart T.obj₂ := by
  rw [mem_heart_iff] at h₁ h₃ ⊢
  exact ⟨t.isLE₂ T hT 0 h₁.1 h₃.1, t.isGE₂ T hT 0 h₁.2 h₃.2⟩

end Extensions

section Heart

variable [IsTriangulated C] (H : Type u') [Category.{v'} H] [Preadditive H] [t.Heart H]

variable {H}

/-- An object `S ∈ [-1, 0]` sits in a distinguished triangle
`(ι K)⟦1⟧ ⟶ S ⟶ ι Q ⟶ (ι K)⟦2⟧` with `K, Q` in the heart: the truncation triangle of `S`. -/
lemma exists_distTriang_truncLE_truncGE (S : C) [t.IsLE S 0] [t.IsGE S (-1)] :
    ∃ (K Q : H) (e₁ : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLE (-1)).obj S)
      (eQ : t.ιHeart.obj Q ≅ (t.truncGE 0).obj S),
      Triangle.mk (e₁.hom ≫ (t.truncLEι (-1)).app S) ((t.truncGEπ 0).app S ≫ eQ.inv)
        (eQ.hom ≫ (t.truncGEδLE (-1) 0 (by lia)).app S ≫ e₁.inv⟦(1 : ℤ)⟧') ∈ distTriang C := by
  have hK : t.heart (((t.truncLE (-1)).obj S)⟦(-1 : ℤ)⟧) := by
    rw [mem_heart_iff]
    exact ⟨t.isLE_shift _ (-1) (-1) 0 (by lia), t.isGE_shift _ (-1) (-1) 0 (by lia)⟩
  have hQ : t.heart ((t.truncGE 0).obj S) := by
    rw [mem_heart_iff]
    constructor <;> infer_instance
  obtain ⟨K, ⟨eK⟩⟩ := t.exists_ιHeart_obj_iso (H := H) hK
  obtain ⟨Q, ⟨eQ⟩⟩ := t.exists_ιHeart_obj_iso (H := H) hQ
  let e₁ : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLE (-1)).obj S :=
    (shiftFunctor C (1 : ℤ)).mapIso eK ≪≫ (shiftFunctorCompIsoId C (-1) 1 (by lia)).app _
  refine ⟨K, Q, e₁, eQ, isomorphic_distinguished _
    (t.triangleLEGE_distinguished (-1) 0 (by lia) S) _
    (Triangle.isoMk _ _ e₁ (Iso.refl _) eQ ?_ ?_ ?_)⟩
  · dsimp; simp
  · dsimp; simp
  · dsimp; simp [← Functor.map_comp]

omit [IsTriangulated C] in
/-- The cone of a morphism of the heart lies in `[-1, 0]`. -/
lemma isLE_isGE_of_distTriang {X Y : H} (f : X ⟶ Y) {S : C} (g : t.ιHeart.obj Y ⟶ S)
    (δ : S ⟶ (t.ιHeart.obj X)⟦(1 : ℤ)⟧) (hT : Triangle.mk (t.ιHeart.map f) g δ ∈ distTriang C) :
    t.IsLE S 0 ∧ t.IsGE S (-1) := by
  have := t.isLE_shift (t.ιHeart.obj X) 0 1 (-1) (by lia)
  exact ⟨t.isLE₂ _ (rot_of_distTriang _ hT) 0 (inferInstanceAs (t.IsLE (t.ιHeart.obj Y) 0))
      (t.isLE_of_le ((t.ιHeart.obj X)⟦(1 : ℤ)⟧) (-1) 0),
    t.isGE₂ _ (rot_of_distTriang _ hT) (-1) (t.isGE_of_ge (t.ιHeart.obj Y) (-1) 0)
      (t.isGE_shift (t.ιHeart.obj X) 0 1 (-1) (by lia))⟩

/-- Blueprint `lemma-perverse-sheaves-curve--1` (3): let `f : X ⟶ Y` be a morphism of the
heart and `X ⟶ Y ⟶ S ⟶ X⟦1⟧` a distinguished triangle. Then `S ∈ [-1, 0]`, and the kernel of
`f` is `(τ_{≤ -1} S)⟦-1⟧`, with kernel map induced by `τ_{≤ -1} S ⟶ S ⟶ X⟦1⟧`. -/
lemma exists_isLimit_kernelFork_of_distTriang {X Y : H} (f : X ⟶ Y) {S : C}
    (g : t.ιHeart.obj Y ⟶ S) (δ : S ⟶ (t.ιHeart.obj X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (t.ιHeart.map f) g δ ∈ distTriang C) :
    ∃ (K : H) (i : K ⟶ X) (hi : i ≫ f = 0) (_ : IsLimit (KernelFork.ofι i hi))
      (e : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLE (-1)).obj S),
      (t.ιHeart.map i)⟦(1 : ℤ)⟧' = e.hom ≫ (t.truncLEι (-1)).app S ≫ δ := by
  obtain ⟨_, _⟩ := t.isLE_isGE_of_distTriang f g δ hT
  obtain ⟨K, Q, e₁, eQ, hT'⟩ := t.exists_distTriang_truncLE_truncGE (H := H) S
  have hι := fun ⦃X Y : H⦄ ⦃n : ℤ⦄ (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧) hn ↦
    t.ιHeart_hom_shift_eq_zero f hn
  exact ⟨K, _, _, AbelianSubcategory.isLimitKernelFork hι hT hT', e₁,
    by rw [AbelianSubcategory.shift_ι_map_ιK, assoc]⟩

/-- Blueprint `lemma-perverse-sheaves-curve--1` (3): let `f : X ⟶ Y` be a morphism of the
heart and `X ⟶ Y ⟶ S ⟶ X⟦1⟧` a distinguished triangle. Then the cokernel of `f` is
`τ_{≥ 0} S`, with cokernel map `Y ⟶ S ⟶ τ_{≥ 0} S`. -/
lemma exists_isColimit_cokernelCofork_of_distTriang {X Y : H} (f : X ⟶ Y) {S : C}
    (g : t.ιHeart.obj Y ⟶ S) (δ : S ⟶ (t.ιHeart.obj X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (t.ιHeart.map f) g δ ∈ distTriang C) :
    ∃ (Q : H) (p : Y ⟶ Q) (hp : f ≫ p = 0) (_ : IsColimit (CokernelCofork.ofπ p hp))
      (e : t.ιHeart.obj Q ≅ (t.truncGE 0).obj S),
      t.ιHeart.map p ≫ e.hom = g ≫ (t.truncGEπ 0).app S := by
  obtain ⟨_, _⟩ := t.isLE_isGE_of_distTriang f g δ hT
  obtain ⟨K, Q, e₁, eQ, hT'⟩ := t.exists_distTriang_truncLE_truncGE (H := H) S
  have hι := fun ⦃X Y : H⦄ ⦃n : ℤ⦄ (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧) hn ↦
    t.ιHeart_hom_shift_eq_zero f hn
  exact ⟨Q, _, _, AbelianSubcategory.isColimitCokernelCofork hι hT hT', eQ,
    by rw [AbelianSubcategory.ι_map_πQ]; simp⟩

omit [IsTriangulated C] in
/-- Blueprint `lemma-perverse-sheaves-curve--1` (4): the connecting morphism of a
distinguished triangle whose terms lie in the heart is determined by the first two morphisms. -/
lemma eq_of_distTriang_of_heart {X Y Z : H} (f : X ⟶ Y) (g : Y ⟶ Z)
    (δ δ' : t.ιHeart.obj Z ⟶ (t.ιHeart.obj X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (t.ιHeart.map f) (t.ιHeart.map g) δ ∈ distTriang C)
    (hT' : Triangle.mk (t.ιHeart.map f) (t.ιHeart.map g) δ' ∈ distTriang C) : δ = δ' := by
  obtain ⟨(c : t.ιHeart.obj Z ⟶ t.ιHeart.obj Z), hc₁, hc₂⟩ :=
    complete_distinguished_triangle_morphism _ _ hT hT' (𝟙 _) (𝟙 _) (by simp)
  have hc₁' : t.ιHeart.map g ≫ c = t.ιHeart.map g := by simpa using hc₁
  have hc₂' : δ = c ≫ δ' := by simpa using hc₂
  have : c = 𝟙 _ := by
    rw [← sub_eq_zero]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₃ _ hT (c - 𝟙 _) (by
      change t.ιHeart.map g ≫ (c - 𝟙 _) = 0
      rw [comp_sub, hc₁', comp_id, sub_self])
    have h : t.IsLE ((Triangle.mk (t.ιHeart.map f) (t.ιHeart.map g) δ).obj₁⟦(1 : ℤ)⟧) (-1) :=
      t.isLE_shift (t.ιHeart.obj X) 0 1 (-1) (by lia)
    rw [hw, t.zero_of_isLE_of_isGE w (-1) 0 (by lia) h
      (inferInstanceAs (t.IsGE (t.ιHeart.obj Z) 0)), comp_zero]
  rw [hc₂', this, id_comp]

/-- Blueprint `lemma-perverse-sheaves-curve--1` (4): a sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` of the
heart is short exact if and only if it extends to a distinguished triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧`. -/
lemma shortExact_iff_exists_distTriang (S : ShortComplex H) :
    S.ShortExact ↔ ∃ (δ : t.ιHeart.obj S.X₃ ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧),
      Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) δ ∈ distTriang C := by
  have := t.hasFiniteProducts_heart H
  have hι := fun ⦃X Y : H⦄ ⦃n : ℤ⦄ (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧) hn ↦
    t.ιHeart_hom_shift_eq_zero f hn
  constructor
  · intro hS
    let := t.abelianHeart H
    have := hS.epi_g
    obtain ⟨X₁, i, δ, hT⟩ := AbelianSubcategory.exists_distinguished_triangle_of_epi hι
      (t.admissibleMorphism_ιHeart_eq_top H) S.g
    let hi := AbelianSubcategory.isLimitKernelForkOfDistTriang hι _ _ _ hT
    let u : S.X₁ ≅ X₁ := IsLimit.conePointUniqueUpToIso hS.fIsKernel hi
    have hu : u.hom ≫ i = S.f :=
      IsLimit.conePointUniqueUpToIso_hom_comp hS.fIsKernel hi WalkingParallelPair.zero
    refine ⟨δ ≫ (t.ιHeart.map u.inv)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _ ?_⟩
    refine Triangle.isoMk _ _ (t.ιHeart.mapIso u) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [← Functor.map_comp, hu]
    · simp
    · simp [← Functor.map_comp]
  · rintro ⟨δ, hT⟩
    let := t.abelianHeart H
    have hf := AbelianSubcategory.isLimitKernelForkOfDistTriang hι _ _ _ hT
    have hg := AbelianSubcategory.isColimitCokernelCoforkOfDistTriang hι _ _ _ hT
    have : Mono S.f := mono_of_isLimit_fork hf
    have : Epi S.g := epi_of_isColimit_cofork hg
    exact ⟨S.exact_of_f_is_kernel hf⟩

end Heart

end CategoryTheory.Triangulated.TStructure
