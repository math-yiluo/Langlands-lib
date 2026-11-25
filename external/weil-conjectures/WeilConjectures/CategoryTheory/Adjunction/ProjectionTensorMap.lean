/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The tensor map of a right adjoint with an invertible projection formula

Let `C` and `D` be monoidal categories, `F : D ⥤ C` a functor (a pullback `f^*`), `adj : L ⊣ R`
an adjunction with `L : C ⥤ D` (a compactly supported direct image `f_!` and its right adjoint
`f^!`), and let
`π M N : L M ⊗ N ⟶ L (M ⊗ F N)` be isomorphisms (a projection formula). The *tensor map*
(`CategoryTheory.Adjunction.projectionTensorMap`)

`τ M N : R M ⊗ F N ⟶ R (M ⊗ N)`

is the transpose along `L ⊣ R` of `L (R M ⊗ F N) ≅ L R M ⊗ N ⟶ M ⊗ N`, the inverse of the
projection map followed by the counit. For `M = 𝟙_ D` it is the canonical map
`θ_{f,N} : ω_f ⊗ f^* N ⟶ f^! N` of a cohomologically smooth morphism.

This file proves the formal properties of `τ` used for cohomologically smooth morphisms:

* `τ M N` is an isomorphism when `N` and `F N` are invertible
  (`CategoryTheory.Adjunction.isIso_projectionTensorMap_of_isInvertible`);
* `τ` is associative when the projection maps are
  (`CategoryTheory.Adjunction.projectionTensorMap_assoc`);
* `τ` is compatible with composition of adjunctions when the projection maps are
  (`CategoryTheory.Adjunction.projectionTensorMap_comp`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

/-- A 2-square whose mate along two adjunctions with invertible units and counits is an
isomorphism is an isomorphism. -/
lemma isIso_of_isIso_mateEquiv {A B C D : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [IsIso adj₁.unit] [IsIso adj₁.counit] [IsIso adj₂.unit]
    [IsIso adj₂.counit] (γ : TwoSquare G L₁ L₂ H) [IsIso (mateEquiv adj₁ adj₂ γ)] :
    IsIso γ := by
  rw [← (mateEquiv adj₁ adj₂).symm_apply_apply γ]
  simp only [mateEquiv_symm_apply]
  infer_instance

section

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

/-- The **tensor map** `R M ⊗ F N ⟶ R (M ⊗ N)` of an adjunction `L ⊣ R` with an invertible
projection map `π : L M ⊗ N ⟶ L (M ⊗ F N)`: the transpose along `L ⊣ R` of
`L (R M ⊗ F N) ≅ L R M ⊗ N ⟶ M ⊗ N`, the inverse of the projection map followed by the counit
of `L ⊣ R` tensored with `N`. -/
noncomputable def projectionTensorMap (M N : D) : R.obj M ⊗ F.obj N ⟶ R.obj (M ⊗ N) :=
  adj.homEquiv _ _ (inv (π (R.obj M) N) ≫ adj.counit.app M ▷ N)

lemma homEquiv_symm_projectionTensorMap (M N : D) :
    (adj.homEquiv _ _).symm (adj.projectionTensorMap π M N) =
      inv (π (R.obj M) N) ≫ adj.counit.app M ▷ N :=
  Equiv.symm_apply_apply _ _


/-- The transpose of the tensor map along `L ⊣ R`. -/
@[reassoc]
lemma map_projectionTensorMap_comp_counit (M N : D) :
    L.map (adj.projectionTensorMap π M N) ≫ adj.counit.app _ =
      inv (π (R.obj M) N) ≫ adj.counit.app M ▷ N := by
  rw [projectionTensorMap, homEquiv_unit, Functor.map_comp, Category.assoc]
  erw [counit_naturality]
  rw [left_triangle_components_assoc]

omit [MonoidalCategory C] [MonoidalCategory D] in
variable {adj π} in
/-- Two morphisms into `R M` agree as soon as their transposes along `L ⊣ R` do. -/
lemma ext_of_comp_counit {P : C} {M : D} {φ ψ : P ⟶ R.obj M}
    (h : L.map φ ≫ adj.counit.app M = L.map ψ ≫ adj.counit.app M) : φ = ψ := by
  apply (adj.homEquiv _ _).symm.injective
  simpa only [homEquiv_counit] using h

/-- The tensor map is natural in the first variable, if the projection map is. -/
@[reassoc]
lemma projectionTensorMap_naturality_left
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    {M M' : D} (φ : M ⟶ M') (N : D) :
    R.map φ ▷ F.obj N ≫ adj.projectionTensorMap π M' N =
      adj.projectionTensorMap π M N ≫ R.map (φ ▷ N) := by
  apply ext_of_comp_counit (adj := adj)
  have h := hπ (R.map φ) N
  rw [← cancel_epi (inv (π _ N)), ← cancel_mono (inv (π _ N))] at h
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  rw [Functor.map_comp, Category.assoc, map_projectionTensorMap_comp_counit, ← reassoc_of% h,
    Functor.map_comp, Category.assoc]
  erw [counit_naturality]
  rw [map_projectionTensorMap_comp_counit_assoc, ← comp_whiskerRight, ← comp_whiskerRight]
  erw [counit_naturality]

/-- The tensor map is natural in the second variable, if the projection map is. -/
@[reassoc]
lemma projectionTensorMap_naturality_right
    (hπ : ∀ (M : C) {N N' : D} (φ : N ⟶ N'), L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ F.map φ))
    (M : D) {N N' : D} (φ : N ⟶ N') :
    R.obj M ◁ F.map φ ≫ adj.projectionTensorMap π M N' =
      adj.projectionTensorMap π M N ≫ R.map (M ◁ φ) := by
  apply ext_of_comp_counit (adj := adj)
  have h := hπ (R.obj M) φ
  rw [← cancel_epi (inv (π _ N)), ← cancel_mono (inv (π _ N'))] at h
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  rw [Functor.map_comp, Category.assoc, map_projectionTensorMap_comp_counit, ← reassoc_of% h,
    Functor.map_comp, Category.assoc]
  erw [counit_naturality]
  rw [map_projectionTensorMap_comp_counit_assoc, whisker_exchange]
  rfl

/-- **The tensor map is an isomorphism at an invertible object.** If `N` and `F N` are
invertible and the projection map is natural in its first variable, then
`τ M N : R M ⊗ F N ⟶ R (M ⊗ N)` is an isomorphism. Tensoring with `N` and with `F N` being
equivalences, `τ (-) N` is the mate of the isomorphism `π⁻¹` along adjoint equivalences on the
sides, whose iterated mate is the conjugate of `π⁻¹`. -/
theorem isIso_projectionTensorMap_of_isInvertible
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    {N : D} (hN : IsInvertible N) (hFN : IsInvertible (F.obj N)) (M : D) :
    IsIso (adj.projectionTensorMap π M N) := by
  obtain ⟨N', ⟨e₁⟩, ⟨e₂⟩⟩ := hN
  obtain ⟨P', ⟨e₁'⟩, ⟨e₂'⟩⟩ := hFN
  let α : TwoSquare (tensorRight (F.obj N)) L L (tensorRight N) := TwoSquare.mk _ _ _ _
    { app M := inv (π M N)
      naturality M M' φ := by
        have h := hπ φ N
        rw [← cancel_epi (inv (π _ N)), ← cancel_mono (inv (π _ N))] at h
        simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id] at h
        exact h.symm }
  have : IsIso α := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    fun M ↦ inferInstanceAs (IsIso (inv (π M N)))
  have hα : (mateEquiv adj adj α).app M = adj.projectionTensorMap π M N := by
    apply ext_of_comp_counit (adj := adj)
    erw [mateEquiv_counit, map_projectionTensorMap_comp_counit]
    rfl
  suffices IsIso (mateEquiv adj adj α) by rw [← hα]; infer_instance
  let adjG := (tensorRightEquivalenceOfTensorIso e₁' e₂').toAdjunction
  let adjH := (tensorRightEquivalenceOfTensorIso e₁ e₂).toAdjunction
  have h := iterated_mateEquiv_conjugateEquiv adj adj adjG adjH α
  have : IsIso (mateEquiv adjH adjG (mateEquiv adj adj α)) := by
    rw [h]
    infer_instance
  have : IsIso adjG.unit :=
    inferInstanceAs (IsIso (tensorRightEquivalenceOfTensorIso e₁' e₂').unitIso.hom)
  have : IsIso adjG.counit :=
    inferInstanceAs (IsIso (tensorRightEquivalenceOfTensorIso e₁' e₂').counitIso.hom)
  have : IsIso adjH.unit :=
    inferInstanceAs (IsIso (tensorRightEquivalenceOfTensorIso e₁ e₂).unitIso.hom)
  have : IsIso adjH.counit :=
    inferInstanceAs (IsIso (tensorRightEquivalenceOfTensorIso e₁ e₂).counitIso.hom)
  exact isIso_of_isIso_mateEquiv adjH adjG _

/-- **Associativity of the tensor map.** If the projection map is natural in its first
variable and associative,
```
(L M ⊗ N) ⊗ N' ──π ▷ N'──▶ L (M ⊗ F N) ⊗ N' ──π──▶ L ((M ⊗ F N) ⊗ F N')
      │α                                                   │L α
      ▼                                                    ▼
L M ⊗ (N ⊗ N') ──π──▶ L (M ⊗ F (N ⊗ N')) ──L (M ◁ δ)──▶ L (M ⊗ (F N ⊗ F N'))
```
for a comparison `δ : F (N ⊗ N') ⟶ F N ⊗ F N'`, then so is the tensor map:
`τ (M ⊗ N) N' ∘ (τ M N ▷ F N') = τ M (N ⊗ N') ∘ (R M ◁ δ⁻¹)` up to the associators. -/
theorem projectionTensorMap_assoc
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (δ : ∀ N N' : D, F.obj (N ⊗ N') ⟶ F.obj N ⊗ F.obj N') [∀ N N', IsIso (δ N N')]
    (hassoc : ∀ (M : C) (N N' : D), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
      L.map (α_ M (F.obj N) (F.obj N')).hom = (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ δ N N'))
    (M N N' : D) :
    adj.projectionTensorMap π M N ▷ F.obj N' ≫ adj.projectionTensorMap π (M ⊗ N) N' ≫
        R.map (α_ M N N').hom =
      (α_ (R.obj M) (F.obj N) (F.obj N')).hom ≫ R.obj M ◁ inv (δ N N') ≫
        adj.projectionTensorMap π M (N ⊗ N') := by
  apply ext_of_comp_counit (adj := adj)
  have h₁ := hπ (adj.projectionTensorMap π M N) N'
  rw [← cancel_epi (inv (π _ N')), ← cancel_mono (inv (π _ N'))] at h₁
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h₁
  have h₂ := hassoc (R.obj M) N N'
  rw [← cancel_epi (inv (π (R.obj M) N ▷ N')), ← cancel_epi (inv (π _ N'))] at h₂
  simp only [IsIso.inv_hom_id_assoc, inv_whiskerRight,
    ← comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight, Category.id_comp] at h₂
  simp only [Functor.map_comp, Category.assoc]
  erw [counit_naturality]
  rw [map_projectionTensorMap_comp_counit_assoc, map_projectionTensorMap_comp_counit,
    ← reassoc_of% h₁, ← comp_whiskerRight_assoc, map_projectionTensorMap_comp_counit, h₂]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← whiskerLeft_comp, IsIso.hom_inv_id,
    whiskerLeft_id, Functor.map_id, Category.id_comp, IsIso.hom_inv_id_assoc, comp_whiskerRight]
  erw [associator_naturality_left]
  rfl


/-- The tensor map at `(M, N')` is an isomorphism if it is one at `(M, N)` for an isomorphic
`N`, provided the projection map is natural in its second variable. -/
lemma isIso_projectionTensorMap_of_iso_right
    (hπ : ∀ (M : C) {N N' : D} (φ : N ⟶ N'), L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ F.map φ))
    {M N N' : D} (e : N ≅ N') [IsIso (adj.projectionTensorMap π M N)] :
    IsIso (adj.projectionTensorMap π M N') := by
  have h := adj.projectionTensorMap_naturality_right π hπ M e.hom
  have : IsIso (R.obj M ◁ F.map e.hom ≫ adj.projectionTensorMap π M N') := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (R.obj M ◁ F.map e.hom) _

/-- The tensor map at `(M', N)` is an isomorphism if it is one at `(M, N)` for an isomorphic
`M`, provided the projection map is natural in its first variable. -/
lemma isIso_projectionTensorMap_of_iso_left
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    {M M' N : D} (e : M ≅ M') [IsIso (adj.projectionTensorMap π M N)] :
    IsIso (adj.projectionTensorMap π M' N) := by
  have h := adj.projectionTensorMap_naturality_left π hπ e.hom N
  have : IsIso (R.map e.hom ▷ F.obj N ≫ adj.projectionTensorMap π M' N) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (R.map e.hom ▷ F.obj N) _

/-- If the tensor map is an isomorphism at `(M, N)` and at `(M, N ⊗ N')`, it is one at
`(M ⊗ N, N')`, by associativity
(`CategoryTheory.Adjunction.projectionTensorMap_assoc`). -/
lemma isIso_projectionTensorMap_tensor_left
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (δ : ∀ N N' : D, F.obj (N ⊗ N') ⟶ F.obj N ⊗ F.obj N') [∀ N N', IsIso (δ N N')]
    (hassoc : ∀ (M : C) (N N' : D), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
      L.map (α_ M (F.obj N) (F.obj N')).hom = (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ δ N N'))
    {M N N' : D} [IsIso (adj.projectionTensorMap π M N)]
    [IsIso (adj.projectionTensorMap π M (N ⊗ N'))] :
    IsIso (adj.projectionTensorMap π (M ⊗ N) N') := by
  have h := adj.projectionTensorMap_assoc π hπ δ hassoc M N N'
  have : IsIso (adj.projectionTensorMap π M N ▷ F.obj N' ≫ adj.projectionTensorMap π (M ⊗ N) N' ≫
      R.map (α_ M N N').hom) := by
    rw [h]
    infer_instance
  have := IsIso.of_isIso_comp_left (adj.projectionTensorMap π M N ▷ F.obj N')
    (adj.projectionTensorMap π (M ⊗ N) N' ≫ R.map (α_ M N N').hom)
  exact IsIso.of_isIso_comp_right _ (R.map (α_ M N N').hom)

/-- If the tensor map is an isomorphism at `(M, N)` and at `(M ⊗ N, N')`, it is one at
`(M, N ⊗ N')`, by associativity
(`CategoryTheory.Adjunction.projectionTensorMap_assoc`). -/
lemma isIso_projectionTensorMap_tensor_right
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (δ : ∀ N N' : D, F.obj (N ⊗ N') ⟶ F.obj N ⊗ F.obj N') [∀ N N', IsIso (δ N N')]
    (hassoc : ∀ (M : C) (N N' : D), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
      L.map (α_ M (F.obj N) (F.obj N')).hom = (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ δ N N'))
    {M N N' : D} [IsIso (adj.projectionTensorMap π M N)]
    [IsIso (adj.projectionTensorMap π (M ⊗ N) N')] :
    IsIso (adj.projectionTensorMap π M (N ⊗ N')) := by
  have h := adj.projectionTensorMap_assoc π hπ δ hassoc M N N'
  have : IsIso ((α_ (R.obj M) (F.obj N) (F.obj N')).hom ≫ R.obj M ◁ inv (δ N N') ≫
      adj.projectionTensorMap π M (N ⊗ N')) := by
    rw [← h]
    infer_instance
  have := IsIso.of_isIso_comp_left (α_ (R.obj M) (F.obj N) (F.obj N')).hom
    (R.obj M ◁ inv (δ N N') ≫ adj.projectionTensorMap π M (N ⊗ N'))
  exact IsIso.of_isIso_comp_left (R.obj M ◁ inv (δ N N')) _
end

/-- The isomorphism of right adjoints `Rh ≅ Rg ⋙ Rf` induced by a composition isomorphism
`e : Lh ≅ Lf ⋙ Lg` of left adjoints is compatible with `e` and the counits. -/
lemma rightAdjointUniq_ofNatIsoLeft_comp_counit {C D E : Type*} [Category* C] [Category* D]
    [Category* E] {Lf : C ⥤ D} {Rf : D ⥤ C} (adjf : Lf ⊣ Rf) {Lg : D ⥤ E} {Rg : E ⥤ D}
    (adjg : Lg ⊣ Rg) {Lh : C ⥤ E} {Rh : E ⥤ C} (adjh : Lh ⊣ Rh) (e : Lh ≅ Lf ⋙ Lg) (K : E) :
    Lg.map (Lf.map ((rightAdjointUniq (adjh.ofNatIsoLeft e) (adjf.comp adjg)).hom.app K)) ≫
        Lg.map (adjf.counit.app _) ≫ adjg.counit.app K = e.inv.app _ ≫ adjh.counit.app K := by
  have := rightAdjointUniq_hom_app_counit (adjh.ofNatIsoLeft e) (adjf.comp adjg) K
  simpa [Adjunction.comp_counit_app] using this

section Composition

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E]
  {Ff : D ⥤ C} {Lf : C ⥤ D} {Rf : D ⥤ C} (adjf : Lf ⊣ Rf)
  {Fg : E ⥤ D} {Lg : D ⥤ E} {Rg : E ⥤ D} (adjg : Lg ⊣ Rg)
  {Fh : E ⥤ C} {Lh : C ⥤ E} {Rh : E ⥤ C} (adjh : Lh ⊣ Rh)
  (πf : ∀ (M : C) (N : D), Lf.obj M ⊗ N ⟶ Lf.obj (M ⊗ Ff.obj N)) [∀ M N, IsIso (πf M N)]
  (πg : ∀ (M : D) (N : E), Lg.obj M ⊗ N ⟶ Lg.obj (M ⊗ Fg.obj N)) [∀ M N, IsIso (πg M N)]
  (πh : ∀ (M : C) (N : E), Lh.obj M ⊗ N ⟶ Lh.obj (M ⊗ Fh.obj N)) [∀ M N, IsIso (πh M N)]

/-- **The tensor map of a composite.** Let `e : Lh ≅ Lf ⋙ Lg` be a composition isomorphism of
left adjoints compatible with the projection maps through comparisons
`γ N : Fh N ⟶ Ff (Fg N)`,
```
Lh M ⊗ N ──e ▷ N──▶ Lg (Lf M) ⊗ N ──πg──▶ Lg (Lf M ⊗ Fg N) ──Lg πf──▶ Lg (Lf (M ⊗ Ff (Fg N)))
     │πh                                                                     ‖
     ▼                                                                       ‖
Lh (M ⊗ Fh N) ──────e──────▶ Lg (Lf (M ⊗ Fh N)) ──────Lg (Lf (M ◁ γ))──────▶ Lg (Lf (M ⊗ Ff (Fg N)))
```
and let `ρ : Rh ⟶ Rg ⋙ Rf` be compatible with `e` and the counits (for instance the
isomorphism of right adjoints induced by `e`). Then the tensor map of `h` is, through `ρ`, the
composite of the tensor map of `f` at `(Rg M, Fg N)` and `Rf` of the tensor map of `g`:
`ρ ∘ τh M N = Rf (τg M N) ∘ τf (Rg M) (Fg N) ∘ (ρ ⊗ γ)`. -/
theorem projectionTensorMap_comp
    (hπf : ∀ {M M' : C} (φ : M ⟶ M') (N : D),
      Lf.map φ ▷ N ≫ πf M' N = πf M N ≫ Lf.map (φ ▷ Ff.obj N))
    (hπg : ∀ {M M' : D} (φ : M ⟶ M') (N : E),
      Lg.map φ ▷ N ≫ πg M' N = πg M N ≫ Lg.map (φ ▷ Fg.obj N))
    (γ : ∀ N : E, Fh.obj N ⟶ Ff.obj (Fg.obj N)) (e : Lh ≅ Lf ⋙ Lg)
    (hcomp : ∀ (M : C) (N : E), e.hom.app M ▷ N ≫ πg (Lf.obj M) N ≫ Lg.map (πf M (Fg.obj N)) =
      πh M N ≫ e.hom.app _ ≫ Lg.map (Lf.map (M ◁ γ N)))
    (ρ : Rh ⟶ Rg ⋙ Rf)
    (hρ : ∀ K : E, Lg.map (Lf.map (ρ.app K)) ≫ Lg.map (adjf.counit.app _) ≫ adjg.counit.app K =
      e.inv.app _ ≫ adjh.counit.app K)
    (M : E) (N : E) :
    adjh.projectionTensorMap πh M N ≫ ρ.app (M ⊗ N) =
      ρ.app M ▷ Fh.obj N ≫ Rf.obj (Rg.obj M) ◁ γ N ≫
        adjf.projectionTensorMap πf (Rg.obj M) (Fg.obj N) ≫
          Rf.map (adjg.projectionTensorMap πg M N) := by
  apply ext_of_comp_counit (adj := adjf)
  apply ext_of_comp_counit (adj := adjg)
  rw [← cancel_epi (πh (Rh.obj M) N ≫ e.hom.app _)]
  simp only [Functor.map_comp, Category.assoc]
  rw [hρ (M ⊗ N)]
  erw [← e.hom.naturality_assoc]
  rw [Iso.hom_inv_id_app_assoc, map_projectionTensorMap_comp_counit, IsIso.hom_inv_id_assoc]
  rw [← Lg.map_comp_assoc (Lf.map (Rf.map _))]
  erw [adjf.counit_naturality]
  rw [Lg.map_comp_assoc, map_projectionTensorMap_comp_counit,
    ← Lg.map_comp_assoc (Lf.map (adjf.projectionTensorMap πf _ _)),
    map_projectionTensorMap_comp_counit, ← Lg.map_comp_assoc (Lf.map (ρ.app M ▷ _)),
    ← Lf.map_comp]
  erw [← whisker_exchange]
  rw [Lf.map_comp, Lg.map_comp_assoc]
  rw [← reassoc_of% (hcomp (Rh.obj M) N), ← Lg.map_comp_assoc (πf _ _),
    ← Lg.map_comp_assoc (πf _ _ ≫ _), ← hπf]
  simp only [Category.assoc]
  erw [IsIso.hom_inv_id_assoc]
  rw [← comp_whiskerRight]
  rw [← reassoc_of% (hπg (Lf.map (ρ.app M) ≫ adjf.counit.app _) N), IsIso.hom_inv_id_assoc,
    ← comp_whiskerRight, ← comp_whiskerRight]
  congr 1
  rw [Lg.map_comp, Category.assoc, hρ, Iso.hom_inv_id_app_assoc]


/-- A composition isomorphism `e : Lh ≅ Lf ⋙ Lg` of left adjoints is compatible with the
projection maps through comparisons `γ N : Fh N ⟶ Ff (Fg N)` if the square of
`CategoryTheory.Adjunction.projectionTensorMap_comp` commutes. -/
structure ProjectionCompCompatible (γ : ∀ N : E, Fh.obj N ⟶ Ff.obj (Fg.obj N))
    (e : Lh ≅ Lf ⋙ Lg) : Prop where
  comp (M : C) (N : E) : e.hom.app M ▷ N ≫ πg (Lf.obj M) N ≫ Lg.map (πf M (Fg.obj N)) =
    πh M N ≫ e.hom.app _ ≫ Lg.map (Lf.map (M ◁ γ N))

/-- **The tensor map of a composite**, through the isomorphism `Rh ≅ Rg ⋙ Rf` of right
adjoints induced by a composition isomorphism `e : Lh ≅ Lf ⋙ Lg` compatible with the projection
maps (`CategoryTheory.Adjunction.projectionTensorMap_comp`). -/
theorem projectionTensorMap_comp_rightAdjointUniq
    (hπf : ∀ {M M' : C} (φ : M ⟶ M') (N : D),
      Lf.map φ ▷ N ≫ πf M' N = πf M N ≫ Lf.map (φ ▷ Ff.obj N))
    (hπg : ∀ {M M' : D} (φ : M ⟶ M') (N : E),
      Lg.map φ ▷ N ≫ πg M' N = πg M N ≫ Lg.map (φ ▷ Fg.obj N))
    (γ : ∀ N : E, Fh.obj N ⟶ Ff.obj (Fg.obj N)) (e : Lh ≅ Lf ⋙ Lg)
    (he : ProjectionCompCompatible πf πg πh γ e) (M N : E) :
    adjh.projectionTensorMap πh M N ≫
        (rightAdjointUniq (adjh.ofNatIsoLeft e) (adjf.comp adjg)).hom.app (M ⊗ N) =
      (rightAdjointUniq (adjh.ofNatIsoLeft e) (adjf.comp adjg)).hom.app M ▷ Fh.obj N ≫
        Rf.obj (Rg.obj M) ◁ γ N ≫ adjf.projectionTensorMap πf (Rg.obj M) (Fg.obj N) ≫
          Rf.map (adjg.projectionTensorMap πg M N) :=
  projectionTensorMap_comp adjf adjg adjh πf πg πh hπf hπg γ e he.comp _
    (rightAdjointUniq_ofNatIsoLeft_comp_counit adjf adjg adjh e) M N
end Composition

section BaseChange

/-- **Base change maps of a composite.** Consider two composable pairs of left adjoints
`Lf, Lg` and `Lf', Lg'` with composites `Lh ≅ Lf ⋙ Lg` and `Lh' ≅ Lf' ⋙ Lg'`, and pullbacks
`Ga, Gb, Gc` with isomorphisms `Exf : Lf ⋙ Gb ⟶ Ga ⋙ Lf'`, `Exg`, `Exh` compatible with the
composition isomorphisms (the exchange of a pasted square is the pasting of the exchanges).
Then the mates `βf, βg, βh` of the inverses of the exchanges paste: through the isomorphisms
`ρ : Rh ⟶ Rg ⋙ Rf` and `ρ'` compatible with the composition isomorphisms and the counits,
`βh = Rf' βg ∘ βf ∘ Ga ρ`. -/
theorem mateEquiv_inv_comp
    {Cx Cy Cz Cx' Cy' Cz' : Type*} [Category* Cx] [Category* Cy] [Category* Cz] [Category* Cx']
    [Category* Cy'] [Category* Cz']
    {Lf : Cx ⥤ Cy} {Rf : Cy ⥤ Cx} (adjf : Lf ⊣ Rf) {Lg : Cy ⥤ Cz} {Rg : Cz ⥤ Cy} (adjg : Lg ⊣ Rg)
    {Lh : Cx ⥤ Cz} {Rh : Cz ⥤ Cx} (adjh : Lh ⊣ Rh)
    {Lf' : Cx' ⥤ Cy'} {Rf' : Cy' ⥤ Cx'} (adjf' : Lf' ⊣ Rf')
    {Lg' : Cy' ⥤ Cz'} {Rg' : Cz' ⥤ Cy'} (adjg' : Lg' ⊣ Rg')
    {Lh' : Cx' ⥤ Cz'} {Rh' : Cz' ⥤ Cx'} (adjh' : Lh' ⊣ Rh')
    {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'} {Gc : Cz ⥤ Cz'}
    (ξf : TwoSquare Ga Lf Lf' Gb) (ξg : TwoSquare Gb Lg Lg' Gc) (ξh : TwoSquare Ga Lh Lh' Gc)
    (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg')
    (hξ : ∀ M : Cx, ξh.app M ≫ Gc.map (e.hom.app M) =
      e'.hom.app (Ga.obj M) ≫ Lg'.map (ξf.app M) ≫ ξg.app (Lf.obj M))
    (ρ : Rh ⟶ Rg ⋙ Rf)
    (hρ : ∀ K : Cz, Lg.map (Lf.map (ρ.app K)) ≫ Lg.map (adjf.counit.app _) ≫ adjg.counit.app K =
      e.inv.app _ ≫ adjh.counit.app K)
    (ρ' : Rh' ⟶ Rg' ⋙ Rf')
    (hρ' : ∀ K : Cz', Lg'.map (Lf'.map (ρ'.app K)) ≫ Lg'.map (adjf'.counit.app _) ≫
      adjg'.counit.app K = e'.inv.app _ ≫ adjh'.counit.app K)
    (K : Cz) :
    Ga.map (ρ.app K) ≫ (mateEquiv adjf adjf' ξf).app (Rg.obj K) ≫
        Rf'.map ((mateEquiv adjg adjg' ξg).app K) =
      (mateEquiv adjh adjh' ξh).app K ≫ ρ'.app (Gc.obj K) := by
  apply ext_of_comp_counit (adj := adjf')
  apply ext_of_comp_counit (adj := adjg')
  simp only [Functor.map_comp, Category.assoc]
  erw [hρ', e'.inv.naturality_assoc, mateEquiv_counit]
  rw [← cancel_epi (e'.hom.app (Ga.obj (Rh.obj K)))]
  simp only [Iso.hom_inv_id_app_assoc]
  have hε : adjh.counit.app K = e.hom.app _ ≫ e.inv.app _ ≫ adjh.counit.app K := by simp
  rw [hε, ← hρ, Gc.map_comp, reassoc_of% (hξ (Rh.obj K))]
  congr 1
  rw [← Lg'.map_comp_assoc (Lf'.map (Rf'.map _))]
  erw [adjf'.counit_naturality]
  rw [Lg'.map_comp_assoc]
  erw [mateEquiv_counit]
  rw [← Lg'.map_comp_assoc (Lf'.map _) (adjf'.counit.app _)]
  erw [mateEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  erw [← ξg.naturality_assoc, ← ξg.naturality_assoc]
  simp only [Functor.comp_map, ← Lg'.map_comp_assoc]
  erw [← ξf.naturality_assoc]
  rfl

/-- **Base change of the tensor map.** Let `Ex : L ⋙ Gb ⟶ Ga ⋙ L'` be an exchange map with
inverse `ξ`, compatible with the projection maps `π` and `π'`, the comparisons
`δa : Ga (M ⊗ M') ⟶ Ga M ⊗ Ga M'`, `δb` and `κ N : Ga (F N) ⟶ F' (Gb N)`:
```
Gb (L M ⊗ N) ──Gb π──▶ Gb (L (M ⊗ F N)) ──Ex──▶ L' (Ga (M ⊗ F N))
     │δb                                               │L' (δa ≫ Ga M ◁ κ)
     ▼                                                 ▼
Gb (L M) ⊗ Gb N ──Ex ▷ Gb N──▶ L' (Ga M) ⊗ Gb N ──π'──▶ L' (Ga M ⊗ F' (Gb N))
```
Then the base change map `β`, the mate of `ξ`, commutes with the tensor maps:
`R' δb ∘ β (M ⊗ N) ∘ Ga (τ M N) = τ' (Gb M) (Gb N) ∘ (β M ⊗ κ N) ∘ δa`. -/
theorem projectionTensorMap_mateEquiv
    {Cx Cy Cx' Cy' : Type*} [Category* Cx] [Category* Cy] [Category* Cx'] [Category* Cy']
    [MonoidalCategory Cx] [MonoidalCategory Cy] [MonoidalCategory Cx'] [MonoidalCategory Cy']
    {F : Cy ⥤ Cx} {L : Cx ⥤ Cy} {R : Cy ⥤ Cx} (adj : L ⊣ R)
    {F' : Cy' ⥤ Cx'} {L' : Cx' ⥤ Cy'} {R' : Cy' ⥤ Cx'} (adj' : L' ⊣ R')
    (π : ∀ (M : Cx) (N : Cy), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
    (π' : ∀ (M : Cx') (N : Cy'), L'.obj M ⊗ N ⟶ L'.obj (M ⊗ F'.obj N)) [∀ M N, IsIso (π' M N)]
    (hπ' : ∀ {M M' : Cx'} (φ : M ⟶ M') (N : Cy'),
      L'.map φ ▷ N ≫ π' M' N = π' M N ≫ L'.map (φ ▷ F'.obj N))
    {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'}
    (δa : ∀ M M' : Cx, Ga.obj (M ⊗ M') ⟶ Ga.obj M ⊗ Ga.obj M')
    (δb : ∀ N N' : Cy, Gb.obj (N ⊗ N') ⟶ Gb.obj N ⊗ Gb.obj N')
    (hδb : ∀ {N N' : Cy} (φ : N ⟶ N') (N'' : Cy),
      Gb.map (φ ▷ N'') ≫ δb N' N'' = δb N N'' ≫ Gb.map φ ▷ Gb.obj N'')
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N))
    (Ex : L ⋙ Gb ⟶ Ga ⋙ L') [IsIso Ex] (ξ : TwoSquare Ga L L' Gb)
    (hExξ : ∀ M : Cx, Ex.app M ≫ ξ.app M = 𝟙 _)
    (hEx : ∀ (M : Cx) (N : Cy), Gb.map (π M N) ≫ Ex.app (M ⊗ F.obj N) ≫
      L'.map (δa M (F.obj N)) ≫ L'.map (Ga.obj M ◁ κ N) =
        δb (L.obj M) N ≫ Ex.app M ▷ Gb.obj N ≫ π' (Ga.obj M) (Gb.obj N))
    (M N : Cy) :
    Ga.map (adj.projectionTensorMap π M N) ≫ (mateEquiv adj adj' ξ).app (M ⊗ N) ≫
        R'.map (δb M N) =
      δa (R.obj M) (F.obj N) ≫ (mateEquiv adj adj' ξ).app M ▷ Ga.obj (F.obj N) ≫
        R'.obj (Gb.obj M) ◁ κ N ≫ adj'.projectionTensorMap π' (Gb.obj M) (Gb.obj N) := by
  apply ext_of_comp_counit (adj := adj')
  rw [← cancel_epi (Gb.map (π (R.obj M) N) ≫ Ex.app _)]
  simp only [Functor.map_comp, Category.assoc]
  erw [adj'.counit_naturality, reassoc_of% (mateEquiv_counit adj adj' ξ (M ⊗ N)),
    ← Ex.naturality_assoc]
  rw [reassoc_of% (hExξ _), map_projectionTensorMap_comp_counit]
  have hx : L'.map ((mateEquiv adj adj' ξ).app M ▷ Ga.obj (F.obj N)) ≫
      L'.map (R'.obj (Gb.obj M) ◁ κ N) = L'.map (Ga.obj (R.obj M) ◁ κ N) ≫
      L'.map ((mateEquiv adj adj' ξ).app M ▷ F'.obj (Gb.obj N)) := by
    rw [← L'.map_comp, ← L'.map_comp, whisker_exchange]
    rfl
  erw [reassoc_of% hx]
  rw [reassoc_of% (hEx (R.obj M) N)]
  erw [← reassoc_of% (hπ' ((mateEquiv adj adj' ξ).app M) (Gb.obj N))]
  rw [IsIso.hom_inv_id_assoc, ← comp_whiskerRight, ← comp_whiskerRight]
  erw [mateEquiv_counit]
  rw [reassoc_of% (hExξ _)]
  simp only [Functor.comp_map]
  rw [← Gb.map_comp_assoc, ← Gb.map_comp_assoc, Category.assoc, map_projectionTensorMap_comp_counit,
    IsIso.hom_inv_id_assoc]
  exact hδb (adj.counit.app M) N


/-- Exchange maps `Exf`, `Exg`, `Exh` of two stacked squares and of the pasted square are
compatible with composition isomorphisms `e : Lh ≅ Lf ⋙ Lg` and `e' : Lh' ≅ Lf' ⋙ Lg'` if
`Gc e ≫ Exg ≫ Lg' Exf = Exh ≫ e'`. -/
structure ExchangeCompCompatible
    {Cx Cy Cz Cx' Cy' Cz' : Type*} [Category* Cx] [Category* Cy] [Category* Cz] [Category* Cx']
    [Category* Cy'] [Category* Cz'] {Lf : Cx ⥤ Cy} {Lg : Cy ⥤ Cz} {Lh : Cx ⥤ Cz}
    {Lf' : Cx' ⥤ Cy'} {Lg' : Cy' ⥤ Cz'} {Lh' : Cx' ⥤ Cz'}
    {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'} {Gc : Cz ⥤ Cz'}
    (Exf : Lf ⋙ Gb ⟶ Ga ⋙ Lf') (Exg : Lg ⋙ Gc ⟶ Gb ⋙ Lg') (Exh : Lh ⋙ Gc ⟶ Ga ⋙ Lh')
    (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg') : Prop where
  comp (M : Cx) : Gc.map (e.hom.app M) ≫ Exg.app (Lf.obj M) ≫ Lg'.map (Exf.app M) =
    Exh.app M ≫ e'.hom.app (Ga.obj M)

/-- **Base change maps of a composite**, through the isomorphisms of right adjoints induced by
composition isomorphisms compatible with the exchange maps: the mate of the inverse exchange of
the pasted square is the pasting of the mates
(`CategoryTheory.Adjunction.mateEquiv_inv_comp`). -/
theorem mateEquiv_inv_comp_rightAdjointUniq
    {Cx Cy Cz Cx' Cy' Cz' : Type*} [Category* Cx] [Category* Cy] [Category* Cz] [Category* Cx']
    [Category* Cy'] [Category* Cz']
    {Lf : Cx ⥤ Cy} {Rf : Cy ⥤ Cx} (adjf : Lf ⊣ Rf) {Lg : Cy ⥤ Cz} {Rg : Cz ⥤ Cy} (adjg : Lg ⊣ Rg)
    {Lh : Cx ⥤ Cz} {Rh : Cz ⥤ Cx} (adjh : Lh ⊣ Rh)
    {Lf' : Cx' ⥤ Cy'} {Rf' : Cy' ⥤ Cx'} (adjf' : Lf' ⊣ Rf')
    {Lg' : Cy' ⥤ Cz'} {Rg' : Cz' ⥤ Cy'} (adjg' : Lg' ⊣ Rg')
    {Lh' : Cx' ⥤ Cz'} {Rh' : Cz' ⥤ Cx'} (adjh' : Lh' ⊣ Rh')
    {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'} {Gc : Cz ⥤ Cz'}
    (Exf : Lf ⋙ Gb ⟶ Ga ⋙ Lf') [IsIso Exf] (Exg : Lg ⋙ Gc ⟶ Gb ⋙ Lg') [IsIso Exg]
    (Exh : Lh ⋙ Gc ⟶ Ga ⋙ Lh') [IsIso Exh] (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg')
    (hEx : ExchangeCompCompatible Exf Exg Exh e e') (K : Cz) :
    Ga.map ((rightAdjointUniq (adjh.ofNatIsoLeft e) (adjf.comp adjg)).hom.app K) ≫
        (mateEquiv adjf adjf' (inv Exf)).app (Rg.obj K) ≫
        Rf'.map ((mateEquiv adjg adjg' (inv Exg)).app K) =
      (mateEquiv adjh adjh' (inv Exh)).app K ≫
        (rightAdjointUniq (adjh'.ofNatIsoLeft e') (adjf'.comp adjg')).hom.app (Gc.obj K) := by
  refine mateEquiv_inv_comp adjf adjg adjh adjf' adjg' adjh' _ _ _ e e' (fun M ↦ ?_) _
    (rightAdjointUniq_ofNatIsoLeft_comp_counit adjf adjg adjh e) _
    (rightAdjointUniq_ofNatIsoLeft_comp_counit adjf' adjg' adjh' e') K
  have h := hEx.comp M
  rw [← cancel_epi (Exh.app M)]
  change Exh.app M ≫ (inv Exh).app M ≫ _ = Exh.app M ≫ e'.hom.app _ ≫
    Lg'.map ((inv Exf).app M) ≫ (inv Exg).app _
  simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, Functor.map_inv]
  rw [← cancel_mono (Exg.app _), ← cancel_mono (Lg'.map (Exf.app M))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact h

/-- **Base change at an invertible object.** In the situation of
`CategoryTheory.Adjunction.projectionTensorMap_mateEquiv`, with invertible comparisons, if the
base change map `β` is an isomorphism at `𝟙_`, then it is one at every invertible `N` (with
`F N`, `Gb N` and `F' (Gb N)` invertible): `β` at `𝟙_ ⊗ N` is, through the tensor maps, `β` at
`𝟙_` tensored with `κ N`. -/
theorem isIso_mateEquiv_app_of_isInvertible
    {Cx Cy Cx' Cy' : Type*} [Category* Cx] [Category* Cy] [Category* Cx'] [Category* Cy']
    [MonoidalCategory Cx] [MonoidalCategory Cy] [MonoidalCategory Cx'] [MonoidalCategory Cy']
    {F : Cy ⥤ Cx} {L : Cx ⥤ Cy} {R : Cy ⥤ Cx} (adj : L ⊣ R)
    {F' : Cy' ⥤ Cx'} {L' : Cx' ⥤ Cy'} {R' : Cy' ⥤ Cx'} (adj' : L' ⊣ R')
    (π : ∀ (M : Cx) (N : Cy), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
    (π' : ∀ (M : Cx') (N : Cy'), L'.obj M ⊗ N ⟶ L'.obj (M ⊗ F'.obj N)) [∀ M N, IsIso (π' M N)]
    (hπ : ∀ {M M' : Cx} (φ : M ⟶ M') (N : Cy),
      L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (hπ' : ∀ {M M' : Cx'} (φ : M ⟶ M') (N : Cy'),
      L'.map φ ▷ N ≫ π' M' N = π' M N ≫ L'.map (φ ▷ F'.obj N))
    {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'}
    (δa : ∀ M M' : Cx, Ga.obj (M ⊗ M') ⟶ Ga.obj M ⊗ Ga.obj M') [∀ M M', IsIso (δa M M')]
    (δb : ∀ N N' : Cy, Gb.obj (N ⊗ N') ⟶ Gb.obj N ⊗ Gb.obj N') [∀ N N', IsIso (δb N N')]
    (hδb : ∀ {N N' : Cy} (φ : N ⟶ N') (N'' : Cy),
      Gb.map (φ ▷ N'') ≫ δb N' N'' = δb N N'' ≫ Gb.map φ ▷ Gb.obj N'')
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N)) [∀ N, IsIso (κ N)]
    (Ex : L ⋙ Gb ⟶ Ga ⋙ L') [IsIso Ex] (ξ : TwoSquare Ga L L' Gb)
    (hExξ : ∀ M : Cx, Ex.app M ≫ ξ.app M = 𝟙 _)
    (hEx : ∀ (M : Cx) (N : Cy), Gb.map (π M N) ≫ Ex.app (M ⊗ F.obj N) ≫
      L'.map (δa M (F.obj N)) ≫ L'.map (Ga.obj M ◁ κ N) =
        δb (L.obj M) N ≫ Ex.app M ▷ Gb.obj N ≫ π' (Ga.obj M) (Gb.obj N))
    (h₁ : IsIso ((mateEquiv adj adj' ξ).app (𝟙_ Cy))) {N : Cy} (hN : IsInvertible N)
    (hFN : IsInvertible (F.obj N)) (hGN : IsInvertible (Gb.obj N))
    (hF'GN : IsInvertible (F'.obj (Gb.obj N))) :
    IsIso ((mateEquiv adj adj' ξ).app N) := by
  have key := projectionTensorMap_mateEquiv adj adj' π π' hπ' δa δb hδb κ Ex ξ hExξ hEx (𝟙_ _) N
  have := isIso_projectionTensorMap_of_isInvertible adj π hπ hN hFN (𝟙_ _)
  have := isIso_projectionTensorMap_of_isInvertible adj' π' hπ' hGN hF'GN (Gb.obj (𝟙_ _))
  have h₂ : IsIso (Ga.map (adj.projectionTensorMap π (𝟙_ _) N) ≫
      (mateEquiv adj adj' ξ).app (𝟙_ _ ⊗ N) ≫ R'.map (δb (𝟙_ _) N)) := by
    rw [key]
    infer_instance
  have := (isIso_comp_left_iff _ _).1 h₂
  have : IsIso ((mateEquiv adj adj' ξ).app (𝟙_ _ ⊗ N)) :=
    IsIso.of_isIso_comp_right _ (R'.map (δb (𝟙_ _) N))
  have hn := (mateEquiv adj adj' ξ).naturality (λ_ N).hom
  have h₄ : IsIso ((R ⋙ Ga).map (λ_ N).hom ≫ (mateEquiv adj adj' ξ).app N) := by
    rw [hn]
    infer_instance
  exact (isIso_comp_left_iff _ _).1 h₄
end BaseChange

end CategoryTheory.Adjunction
