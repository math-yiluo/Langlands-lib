import Langlands.Cohomology.ExactBaseChange.ResolutionMap

/-!
# Pasting base change transformations

Consider two squares of additive functors between abelian categories

```
C₁ --F₁--> D₁        C₂ --F₂--> D₂
|α         |β        |δ         |γ
C₂ --F₂--> D₂        C₃ --F₃--> D₃
```

with exact vertical functors, and natural transformations `τ₀ : F₁ ⋙ β ⟶ α ⋙ F₂` and
`τ₂ : F₂ ⋙ γ ⟶ δ ⋙ F₃`. Stacking them gives `pasteNatTrans τ₀ τ₂ : F₁ ⋙ β ⋙ γ ⟶
(α ⋙ δ) ⋙ F₃`. The base change transformation of the pasted square is the composite of the
two base change transformations (`baseChangeNatTrans_paste_app`).

On the way, `homologyHom` and `homologyNatTrans` of `LeftExactHomology` are shown to be
compatible with composition of functors.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.LeftExactHomology

section Composition

variable {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]
  {E' : Type u₃} [Category.{v₃} E'] [Abelian E']
  (β : D ⥤ E) [β.Additive] [PreservesFiniteLimits β]
  (γ : E ⥤ E') [γ.Additive] [PreservesFiniteLimits γ]

omit [PreservesFiniteLimits β] [PreservesFiniteLimits γ] in
/-- The map `toCycles` of a composite is `γ` of the map for `β`, followed by the map for `γ`. -/
lemma toCycles_comp (S : ShortComplex D) :
    toCycles (β ⋙ γ) S = γ.map (toCycles β S) ≫ toCycles γ (S.map β) := by
  rw [← cancel_mono (S.map (β ⋙ γ)).iCycles, toCycles_iCycles, Category.assoc]
  change _ = γ.map (toCycles β S) ≫ toCycles γ (S.map β) ≫ ((S.map β).map γ).iCycles
  rw [toCycles_iCycles, ← γ.map_comp, toCycles_iCycles]
  rfl

/-- The map `homologyHom` of a composite is the map for `γ` followed by `γ` of the map for
`β`. -/
lemma homologyHom_comp (S : ShortComplex D) :
    homologyHom (β ⋙ γ) S = homologyHom γ (S.map β) ≫ γ.map (homologyHom β S) := by
  rw [← cancel_epi (toCycles (β ⋙ γ) S ≫ (S.map (β ⋙ γ)).homologyπ), Category.assoc,
    toCycles_homologyπ_homologyHom, toCycles_comp]
  simp only [Category.assoc]
  change _ = γ.map (toCycles β S) ≫ toCycles γ (S.map β) ≫ ((S.map β).map γ).homologyπ ≫
    homologyHom γ (S.map β) ≫ γ.map (homologyHom β S)
  rw [toCycles_homologyπ_homologyHom_assoc, ← γ.map_comp, ← γ.map_comp,
    toCycles_homologyπ_homologyHom]
  rfl

/-- The components of `homologyNatTrans` for a composite. -/
lemma homologyNatTrans_comp_app {ι : Type*} (c : ComplexShape ι) (i : ι)
    (K : HomologicalComplex D c) :
    (homologyNatTrans (β ⋙ γ) c i).app K =
      (homologyNatTrans γ c i).app ((β.mapHomologicalComplex c).obj K) ≫
        γ.map ((homologyNatTrans β c i).app K) :=
  homologyHom_comp β γ (K.sc i)

end Composition

end Langlands.Cohomology.LeftExactHomology

namespace Langlands.Cohomology.ExactBaseChange

open AcyclicResolution

section Paste

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {D₁ : Type u₄} [Category.{v₄} D₁]
  {D₂ : Type u₅} [Category.{v₅} D₂] {D₃ : Type u₆} [Category.{v₆} D₃]
  {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {F₃ : C₃ ⥤ D₃} {α : C₁ ⥤ C₂} {δ : C₂ ⥤ C₃}
  {β : D₁ ⥤ D₂} {γ : D₂ ⥤ D₃}

/-- The pasting of `τ₀ : F₁ ⋙ β ⟶ α ⋙ F₂` and `τ₂ : F₂ ⋙ γ ⟶ δ ⋙ F₃`: its component at
`A` is `γ.map (τ₀.app A) ≫ τ₂.app (α.obj A)`. -/
@[simps]
def pasteNatTrans (τ₀ : F₁ ⋙ β ⟶ α ⋙ F₂) (τ₂ : F₂ ⋙ γ ⟶ δ ⋙ F₃) :
    F₁ ⋙ β ⋙ γ ⟶ (α ⋙ δ) ⋙ F₃ where
  app A := γ.map (τ₀.app A) ≫ τ₂.app (α.obj A)
  naturality A B f := by
    have h₀ := τ₀.naturality f
    have h₂ := τ₂.naturality (α.map f)
    dsimp at h₀ h₂ ⊢
    rw [← Category.assoc, ← γ.map_comp, h₀, γ.map_comp, Category.assoc, h₂]
    simp only [Category.assoc]

end Paste

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasInjectiveResolutions C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasInjectiveResolutions C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasInjectiveResolutions C₃]
  {D₁ : Type u₄} [Category.{v₄} D₁] [Abelian D₁]
  {D₂ : Type u₅} [Category.{v₅} D₂] [Abelian D₂]
  {D₃ : Type u₆} [Category.{v₆} D₃] [Abelian D₃]
  {F₁ : C₁ ⥤ D₁} [F₁.Additive] {F₂ : C₂ ⥤ D₂} [F₂.Additive] {F₃ : C₃ ⥤ D₃} [F₃.Additive]
  {α : C₁ ⥤ C₂} [α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]
  {δ : C₂ ⥤ C₃} [δ.Additive] [PreservesFiniteLimits δ] [δ.PreservesHomology]
  {β : D₁ ⥤ D₂} [β.Additive] [PreservesFiniteLimits β] [β.PreservesHomology]
  {γ : D₂ ⥤ D₃} [γ.Additive] [PreservesFiniteLimits γ] [γ.PreservesHomology]

omit [HasInjectiveResolutions C₂] [HasInjectiveResolutions C₃] [PreservesFiniteLimits α]
  [α.PreservesHomology] [PreservesFiniteLimits β] [β.PreservesHomology] in
/-- For Mathlib's chosen injective resolution, the resolution comparison is an isomorphism,
for any additive functor. -/
lemma isIso_resolutionComparison_injectiveResolution (A : C₁) (n : ℕ) :
    IsIso (resolutionComparison F₁ (injectiveResolution A).ι n) := by
  rw [resolutionComparison_eq F₁ (injectiveResolution A).ι (injectiveResolution A) (𝟙 _)
    (Category.comp_id _) n, comparison, CategoryTheory.Functor.map_id, Category.id_comp]
  infer_instance

/-- The base change transformation of a pasted square is the composite of the base change
transformations of the two squares. -/
theorem baseChangeNatTrans_paste_app (τ₀ : F₁ ⋙ β ⟶ α ⋙ F₂) (τ₂ : F₂ ⋙ γ ⟶ δ ⋙ F₃)
    [(β ⋙ γ).PreservesHomology] [(α ⋙ δ).PreservesHomology] (n : ℕ) (A : C₁) :
    (baseChangeNatTrans (pasteNatTrans τ₀ τ₂) n).app A =
      γ.map ((baseChangeNatTrans τ₀ n).app A) ≫ (baseChangeNatTrans τ₂ n).app (α.obj A) := by
  let I := injectiveResolution A
  let J := injectiveResolution (α.obj A)
  let K := I.cocomplex
  have := quasiIso_mapResolutionAugmentation α I.ι
  have := quasiIso_mapResolutionAugmentation δ J.ι
  let ψ₀ : (α.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ J.cocomplex :=
    lift (mapResolutionAugmentation α I.ι) (𝟙 _) J.ι
  have hψ₀ : mapResolutionAugmentation α I.ι ≫ ψ₀ = J.ι := comp_lift_id _ J
  let ψ₁ : ((α ⋙ δ).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶
      (δ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex :=
    (δ.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ₀
  have hψ₁ : mapResolutionAugmentation (α ⋙ δ) I.ι ≫ ψ₁ = mapResolutionAugmentation δ J.ι := by
    refine HomologicalComplex.from_single_hom_ext ?_
    rw [HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero,
      mapResolutionAugmentation_f_zero, ← hψ₀]
    change δ.map (α.map (I.ι.f 0)) ≫ δ.map (ψ₀.f 0) = _
    rw [← δ.map_comp, HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero]
    rfl
  have h₀ := resolutionComparison_baseChangeNatTrans τ₀ hψ₀
    (Φ := resolutionBaseChangeMap τ₀ ψ₀) (fun _ => rfl) n
  have h₂ := resolutionComparison_baseChangeNatTrans τ₂ (ε := J.ι)
    (ψ := 𝟙 ((δ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex))
    (Category.comp_id _) (Φ := resolutionBaseChangeMap τ₂ (𝟙 _)) (fun _ => rfl) n
  have h₁ := resolutionComparison_baseChangeNatTrans (pasteNatTrans τ₀ τ₂) hψ₁
    (Φ := resolutionBaseChangeMap (pasteNatTrans τ₀ τ₂) ψ₁) (fun _ => rfl) n
  have := isIso_resolutionComparison_injectiveResolution (F₁ := F₁) A n
  rw [← cancel_epi ((β ⋙ γ).map (resolutionComparison F₁ I.ι n)), h₁]
  change _ = γ.map (β.map (resolutionComparison F₁ I.ι n)) ≫ _
  rw [← γ.map_comp_assoc, h₀, γ.map_comp, γ.map_comp, Category.assoc, Category.assoc, h₂]
  have hnat := (LeftExactHomology.homologyNatTrans γ (ComplexShape.up ℕ) n).naturality
    (resolutionBaseChangeMap τ₀ ψ₀)
  have hcomp := LeftExactHomology.homologyNatTrans_comp_app β γ (ComplexShape.up ℕ) n
    ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
  have hΦ : (γ.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionBaseChangeMap τ₀ ψ₀) ≫
      resolutionBaseChangeMap τ₂ (𝟙 _) = resolutionBaseChangeMap (pasteNatTrans τ₀ τ₂) ψ₁ := by
    ext q
    have h := τ₂.naturality (ψ₀.f q)
    dsimp at h ⊢
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, γ.map_comp, Category.assoc, h]
    exact (Category.assoc _ _ _).symm
  have hkey : inv ((LeftExactHomology.homologyNatTrans γ (ComplexShape.up ℕ) n).app
        ((β.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))) ≫
      (HomologicalComplex.homologyFunctor D₃ (ComplexShape.up ℕ) n).map
        ((γ.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionBaseChangeMap τ₀ ψ₀)) =
      γ.map ((HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n).map
        (resolutionBaseChangeMap τ₀ ψ₀)) ≫
        inv ((LeftExactHomology.homologyNatTrans γ (ComplexShape.up ℕ) n).app
          ((F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact hnat
  have hinv : inv ((LeftExactHomology.homologyNatTrans (β ⋙ γ) (ComplexShape.up ℕ) n).app
        ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) =
      γ.map (inv ((LeftExactHomology.homologyNatTrans β (ComplexShape.up ℕ) n).app
        ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))) ≫
      inv ((LeftExactHomology.homologyNatTrans γ (ComplexShape.up ℕ) n).app
        ((β.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hcomp, Category.assoc, ← γ.map_comp_assoc, IsIso.hom_inv_id, γ.map_id,
      Category.id_comp, IsIso.hom_inv_id]
  rw [hinv, ← hΦ, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hkey]

end Langlands.Cohomology.ExactBaseChange
