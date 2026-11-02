import Langlands.Cohomology.ExactBaseChange.ResolutionStatement

/-!
# Exact base change computed with arbitrary right resolutions: proof

This file proves `ResolutionCompatibilityStatement`.

* `quasiIso_mapResolutionAugmentation`: a functor preserving homology sends a right
  resolution to a right resolution.
* `resolutionComparison_baseChangeNatTrans`: the comparison equality, with no left exactness or
  acyclicity hypotheses.
* `isIso_baseChangeNatTrans_app_of_acyclic`: the isomorphism criterion, deduced from the
  equality and the ordinary acyclic-resolution comparison theorem.
* `resolutionCompatibility`: the proposition itself.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ExactBaseChange

open AcyclicResolution

section Augmentation

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]

/-- A functor that preserves homology sends a right resolution `ε : A[0] ⟶ K` to the right
resolution `mapResolutionAugmentation α ε : (α A)[0] ⟶ α K`. -/
theorem quasiIso_mapResolutionAugmentation (α : C₁ ⥤ C₂) [α.Additive] [α.PreservesHomology]
    {A : C₁} {K : CochainComplex C₁ ℕ} (ε : (CochainComplex.single₀ C₁).obj A ⟶ K)
    [QuasiIso ε] : QuasiIso (mapResolutionAugmentation α ε) := by
  rw [mapResolutionAugmentation]
  infer_instance

end Augmentation

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasInjectiveResolutions C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasInjectiveResolutions C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁]
  {D₂ : Type u₄} [Category.{v₄} D₂] [Abelian D₂]
  {F₁ : C₁ ⥤ D₁} [F₁.Additive] {F₂ : C₂ ⥤ D₂} [F₂.Additive]
  {α : C₁ ⥤ C₂} [α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]
  {β : D₁ ⥤ D₂} [β.Additive] [PreservesFiniteLimits β] [β.PreservesHomology]
  (τ : F₁ ⋙ β ⟶ α ⋙ F₂)
  {A : C₁} {K : CochainComplex C₁ ℕ} {K' : CochainComplex C₂ ℕ}
  (ε : (CochainComplex.single₀ C₁).obj A ⟶ K) [QuasiIso ε]
  (ε' : (CochainComplex.single₀ C₂).obj (α.obj A) ⟶ K') [QuasiIso ε']
  (ψ : (α.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ K')
  (Φ : (β.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ⟶
    (F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj K')

/-- `β` of the resolution comparison of `ε` for `F₁`, followed by the inverse of the component
of `LeftExactHomology.derivedNatTrans β F₁ n`, is the inverse of `homologyNatTrans β` at
`F₁ K` followed by the resolution comparison of `ε` for `F₁ ⋙ β`. -/
theorem map_resolutionComparison_inv_derivedNatTrans (n : ℕ) :
    β.map (resolutionComparison F₁ ε n) ≫
        inv ((LeftExactHomology.derivedNatTrans β F₁ n).app A) =
      inv ((LeftExactHomology.homologyNatTrans β (ComplexShape.up ℕ) n).app
          ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
        resolutionComparison (F₁ ⋙ β) ε n := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact (LeftExactHomology.comparison_comp_derivedHom β F₁ (injectiveResolution A)
    (lift ε (𝟙 A) (injectiveResolution A).ι) n).symm

omit [HasInjectiveResolutions C₂] [PreservesFiniteLimits α] [α.PreservesHomology]
  [PreservesFiniteLimits β] [β.PreservesHomology] in
/-- The resolution comparison of `ε` for `F₁ ⋙ β`, followed by the component of
`NatTrans.rightDerived τ n`, is the homology map of `τ` on `K` followed by the resolution
comparison of `ε` for `α ⋙ F₂`. -/
theorem resolutionComparison_rightDerived (n : ℕ) :
    resolutionComparison (F₁ ⋙ β) ε n ≫ (NatTrans.rightDerived τ n).app A =
      (HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K) ≫
        resolutionComparison (α ⋙ F₂) ε n := by
  rw [InjectiveResolution.rightDerived_app_eq τ (injectiveResolution A) n]
  simp only [resolutionComparison, comparison, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.comp_map]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    NatTrans.mapHomologicalComplex_naturality]

omit [HasInjectiveResolutions C₁] [PreservesFiniteLimits α] [α.PreservesHomology]
  [QuasiIso ε] in
variable {ε ε' ψ} in
/-- Along an augmentation-compatible `ψ : α K ⟶ K'` over the identity of `α A`, the resolution
comparison of `mapResolutionAugmentation α ε` for `F₂` is the homology map of `F₂ ψ` followed by
the resolution comparison of `ε'`. -/
theorem resolutionComparison_mapResolutionAugmentation
    [QuasiIso (mapResolutionAugmentation α ε)]
    (hψ : mapResolutionAugmentation α ε ≫ ψ = ε') (n : ℕ) :
    resolutionComparison F₂ (mapResolutionAugmentation α ε) n =
      (HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n).map
          ((F₂.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) ≫
        resolutionComparison F₂ ε' n := by
  have h := resolutionComparison_naturality F₂ (mapResolutionAugmentation α ε) ε' (𝟙 _) ψ
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp, hψ]) n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

omit [HasInjectiveResolutions C₁] [HasInjectiveResolutions C₂] [PreservesFiniteLimits α]
  [α.PreservesHomology] [PreservesFiniteLimits β] [β.PreservesHomology] in
variable {τ ψ Φ} in
/-- The cochain map `Φ` is the composite of `τ` on `K`, the identification of `(α ⋙ F₂) K`
with `F₂ (α K)`, and `F₂ ψ`. -/
theorem mapHomologicalComplex_comp_eq
    (hΦ : ∀ q : ℕ, Φ.f q = τ.app (K.X q) ≫ F₂.map (ψ.f q)) :
    (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (α ⋙ F₂)) (ComplexShape.up ℕ)).inv.app
          K ≫ (F₂.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ = Φ := by
  ext q
  simp [hΦ q]

variable {ε ε' ψ Φ} in
/-- The comparison equality: `β` of the resolution comparison of `ε` for `F₁`, followed by the
component at `A` of `baseChangeNatTrans τ n`, is the inverse of `homologyNatTrans β` at `F₁ K`,
followed by the homology map of `Φ` and the resolution comparison of `ε'` for `F₂`. -/
theorem resolutionComparison_baseChangeNatTrans
    (hψ : mapResolutionAugmentation α ε ≫ ψ = ε')
    (hΦ : ∀ q : ℕ, Φ.f q = τ.app (K.X q) ≫ F₂.map (ψ.f q)) (n : ℕ) :
    β.map (resolutionComparison F₁ ε n) ≫ (baseChangeNatTrans τ n).app A =
      inv ((LeftExactHomology.homologyNatTrans β (ComplexShape.up ℕ) n).app
          ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
        (HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n).map Φ ≫
          resolutionComparison F₂ ε' n := by
  have := quasiIso_mapResolutionAugmentation α ε
  have he := resolutionComparison_compComparison F₂ (Iso.refl (α ⋙ F₂)) ε
    (fun q => Langlands.AlgebraicGeometry.Modules.DerivedSections.isZero_rightDerived_succ_of_preservesHomology
      α A q) n
  rw [baseChangeNatTrans_app, reassoc_of% (map_resolutionComparison_inv_derivedNatTrans ε n),
    reassoc_of% (resolutionComparison_rightDerived τ ε n), he,
    resolutionComparison_mapResolutionAugmentation hψ n, ← mapHomologicalComplex_comp_eq hΦ,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

variable {ε ε' ψ Φ} in
/-- The isomorphism criterion: if `F₁` and `F₂` are left exact, the terms of `K` and `K'` are
acyclic for them and `Φ` is a quasi-isomorphism, the component of `baseChangeNatTrans τ n` at
`A` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_app_of_acyclic
    [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂]
    (hψ : mapResolutionAugmentation α ε ≫ ψ = ε')
    (hΦ : ∀ q : ℕ, Φ.f q = τ.app (K.X q) ≫ F₂.map (ψ.f q))
    (hK : ∀ q r : ℕ, IsZero ((F₁.rightDerived (r + 1)).obj (K.X q)))
    (hK' : ∀ q r : ℕ, IsZero ((F₂.rightDerived (r + 1)).obj (K'.X q)))
    [QuasiIso Φ] (n : ℕ) :
    IsIso ((baseChangeNatTrans τ n).app A) := by
  have : IsIso (resolutionComparison F₁ ε n) :=
    (acyclicResolutionComparisonStatement C₁ D₁ F₁ A K ε inferInstance hK
      (injectiveResolution A) _ (comp_lift_id ε _)).2 n
  have : IsIso (resolutionComparison F₂ ε' n) :=
    (acyclicResolutionComparisonStatement C₂ D₂ F₂ (α.obj A) K' ε' inferInstance hK'
      (injectiveResolution (α.obj A)) _ (comp_lift_id ε' _)).2 n
  have : IsIso ((HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n).map Φ) := by
    change IsIso (HomologicalComplex.homologyMap Φ n)
    infer_instance
  have : IsIso (β.map (resolutionComparison F₁ ε n) ≫ (baseChangeNatTrans τ n).app A) := by
    rw [resolutionComparison_baseChangeNatTrans τ hψ hΦ n]
    infer_instance
  exact IsIso.of_isIso_comp_left (β.map (resolutionComparison F₁ ε n)) _

/-- Proof of `ResolutionCompatibilityStatement`. -/
theorem resolutionCompatibility :
    ResolutionCompatibilityStatement.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} := by
  intro C₁ _ _ _ C₂ _ _ _ D₁ _ _ D₂ _ _ F₁ _ F₂ _ α _ _ _ β _ _ _ τ A K K' ε _ ε' _ ψ hψ Φ hΦ
  exact ⟨fun n => resolutionComparison_baseChangeNatTrans τ hψ hΦ n,
    fun hK hK' _ n => isIso_baseChangeNatTrans_app_of_acyclic τ hψ hΦ hK hK' n⟩

end Langlands.Cohomology.ExactBaseChange
