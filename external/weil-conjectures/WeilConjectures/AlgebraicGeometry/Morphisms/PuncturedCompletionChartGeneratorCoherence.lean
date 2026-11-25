/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartTransitions
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Coherence on original elements of the affine section modules

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, item (1)
* Stacks Project, Tag 0BLH, second proof paragraph
* Tag 01I6, sections of a principal open in an affine scheme
* Tag 01I6, affine section modules and base change
* Stacks Project, Tag 0BLH, second proof paragraph (the object check)
* Tag 05EL, item (1), its square and cocycle clauses
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.CompletionGluingData


/-- Sections with the structural action of the affine base. -/
private noncomputable def chartSections {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) (W : Z.Opens) : ModuleCat R :=
  letI := Module.compHom Γ(Z, W) (chartScalarMap h W)
  ModuleCat.of R Γ(Z, W)

/-- Restriction of sections is linear for the structural actions. -/
private noncomputable def chartRestriction {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) {W V : Z.Opens} (hVW : V ≤ W) :
    chartSections h W →ₗ[R] chartSections h V where
  toFun := Z.presheaf.map (homOfLE hVW).op
  map_add' := map_add _
  map_smul' := by
    intro a x
    change (Z.presheaf.map (homOfLE hVW).op)
      (chartScalarMap h W a * (show Γ(Z, W) from x)) =
      chartScalarMap h V a * (Z.presheaf.map (homOfLE hVW).op) x
    rw [map_mul]
    congr 1
    change ((ΓSpecIso (.of R)).inv ≫ h.appTop ≫
      Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      Z.presheaf.map (homOfLE hVW).op) a =
      ((ΓSpecIso (.of R)).inv ≫ h.appTop ≫
        Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) a
    rw [← Z.presheaf.map_comp]
    rfl

private theorem chart_basicOpen {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) (W : Z.Opens) (r : R) :
    Z.basicOpen (chartScalarMap h W r) = W ⊓ h ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
  change Z.basicOpen (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
    (h.appTop ((ΓSpecIso (.of R)).inv r))) = _
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]

private theorem chart_localization {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) (W W' : Z.Opens) (hW : IsAffineOpen W)
    (r : R) (he : W' = W ⊓ h ⁻¹ᵁ PrimeSpectrum.basicOpen r) :
    IsLocalizedModule (Submonoid.powers r)
      (chartRestriction h (show W' ≤ W by rw [he]; exact inf_le_left)) := by
  let : Algebra R Γ(Z, W) := (chartScalarMap h W).toAlgebra
  let : Algebra Γ(Z, W) Γ(Z, W') :=
    (Z.presheaf.map (homOfLE (show W' ≤ W by rw [he]; exact inf_le_left)).op).hom.toAlgebra
  let : Algebra R Γ(Z, W') := (chartScalarMap h W').toAlgebra
  have ht : IsScalarTower R Γ(Z, W) Γ(Z, W') := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change chartScalarMap h W' a =
      Z.presheaf.map (homOfLE (show W' ≤ W by rw [he]; exact inf_le_left)).op
        (chartScalarMap h W a)
    change ((ΓSpecIso (.of R)).inv ≫ h.appTop ≫
      Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op) a =
      ((ΓSpecIso (.of R)).inv ≫ h.appTop ≫
        Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        Z.presheaf.map (homOfLE (show W' ≤ W by rw [he]; exact inf_le_left)).op) a
    rw [← Z.presheaf.map_comp]
    rfl
  let := ht
  have hl : IsLocalization.Away (chartScalarMap h W r) Γ(Z, W') :=
    hW.isLocalization_of_eq_basicOpen _ _ (he.trans (chart_basicOpen h W r).symm)
  let := hl
  have hm : IsLocalizedModule (Submonoid.powers (algebraMap R Γ(Z, W) r))
      (Algebra.linearMap Γ(Z, W) Γ(Z, W')) := inferInstance
  let := hm
  exact IsLocalizedModule.restrictScalars_powers r (Algebra.linearMap Γ(Z, W) Γ(Z, W'))


/-- Localizing the supplied double-intersection equivalence gives the actual sections
on a triple intersection. The equivalence is specified on the original double sections;
no transition or cocycle equality is assumed or asserted.
-/
private theorem exists_chart_section_localization
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
    (T : AffineChartTransitions D t f) (i j k : Fin t) (W : Y.Opens)
    (hW : W = (((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
      ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f j))) ⊓
      ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f k))) :
    ∃ e : FormalGlueing.localize (f k)
        (FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (T.F.M j))) ≃ₗ[A]
        chartSections (q ≫ U.ι) W,
      ∀ x, e (LocalizedModule.mk x 1) =
        chartRestriction (q ≫ U.ι)
          (show W ≤ ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
            ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)) by
              rw [hW]; exact inf_le_left) (T.b i j x) := by
  let V := fun l ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f l)
  have hd : IsAffineOpen (V i ⊓ V j) := by
    rw [inf_comm, ← chart_basicOpen (q ≫ U.ι) (V j) (f i)]
    exact (hV j).basicOpen _
  let B : FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (T.F.M j)) ≃ₗ[A]
      chartSections (q ≫ U.ι) (V i ⊓ V j) :=
    { __ := T.b i j
      map_smul' := T.b_scalar i j }
  let a := chartRestriction (q ≫ U.ι)
    (show W ≤ V i ⊓ V j by rw [hW]; exact inf_le_left)
  have hl : IsLocalizedModule (Submonoid.powers (f k)) a :=
    chart_localization (q ≫ U.ι) (V i ⊓ V j) W hd (f k) hW
  let := hl
  have hc : IsLocalizedModule (Submonoid.powers (f k)) (a.comp B.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers (f k)) a B
  let := hc
  refine ⟨IsLocalizedModule.iso (Submonoid.powers (f k)) (a.comp B.toLinearMap), ?_⟩
  intro x
  exact IsLocalizedModule.iso_mk_one _ _ x



private theorem chart_affine_tensor
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {Y O : Scheme.{u}} (hY : Y ⟶ Spec (.of A)) (p : O ⟶ Y)
    (hC : O ⟶ Spec (.of C))
    (H : IsPullback p hC hY (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (V : Y.Opens) (hV : IsAffineOpen V) :
    letI : Algebra A Γ(Y, V) := (chartScalarMap hY V).toAlgebra
    ∃ Q : TensorProduct A C Γ(Y, V) ≃+ Γ(O, p ⁻¹ᵁ V),
      ∀ z x, Q (TensorProduct.tmul A z x) =
        chartScalarMap hC (p ⁻¹ᵁ V) z * p.app V x := by
  let : Algebra A Γ(Y, V) := (chartScalarMap hY V).toAlgebra
  have hUST : (⊤ : (Spec (.of C)).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap A C)) ⁻¹ᵁ ⊤ := by simp
  have hUSX : V ≤ hY ⁻¹ᵁ ⊤ := by simp
  have hUY : p ⁻¹ᵁ V = p ⁻¹ᵁ V ⊓ hC ⁻¹ᵁ ⊤ := by simp
  let := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _) hV
  have Hs := (isIso_pushoutSection_iff H hUST hUSX hUY).mp inferInstance
  have Hs' : IsPushout (CommRingCat.ofHom (chartScalarMap hY V))
      (CommRingCat.ofHom (algebraMap A C)) (p.app V)
      (CommRingCat.ofHom (chartScalarMap hC (p ⁻¹ᵁ V))) := by
    refine Hs.of_iso (ΓSpecIso (.of A)) (Iso.refl _) (ΓSpecIso (.of C))
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appLE, chartScalarMap]
    · simp [Scheme.Hom.appLE]
    · simp [Scheme.Hom.appLE]
    · simp [Scheme.Hom.appLE, chartScalarMap]
  let e := ((CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).isoIsPushout
    (.of C) Γ(Y, V) Hs'.flip).commRingCatIsoToRingEquiv
  refine ⟨e.toAddEquiv, ?_⟩
  intro z x
  change e (TensorProduct.tmul A z x) = _
  have hz := congr($( (CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).inl_isoIsPushout_hom
    (.of C) Γ(Y, V) Hs'.flip ) z)
  have hx := congr($( (CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).inr_isoIsPushout_hom
    (.of C) Γ(Y, V) Hs'.flip ) x)
  change e (TensorProduct.tmul A z x) = _
  rw [show TensorProduct.tmul A z x =
    TensorProduct.tmul A z (1 : Γ(Y, V)) * TensorProduct.tmul A (1 : C) x by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
  rw [map_mul]
  change e (TensorProduct.tmul A z (1 : Γ(Y, V))) =
    chartScalarMap hC (p ⁻¹ᵁ V) z at hz
  change e (TensorProduct.tmul A (1 : C) x) = p.app V x at hx
  rw [hz, hx]

private theorem chart_completed_tensor
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} (q : Y ⟶ U.toScheme)
    (V : Y.Opens) (hV : IsAffineOpen V)
    (M : ModuleCat.{u} A) (b : M ≃+ Γ(Y, V))
    (bs : ∀ a x, b (a • x) = chartScalarMap (q ≫ U.ι) V a * b x) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let O := pullback q (completionSpecMap A ∣_ U)
    let p := pullback.fst q (completionSpecMap A ∣_ U)
    let hC := pullback.snd q (completionSpecMap A ∣_ U) ≫
      (completionSpecMap A ⁻¹ᵁ U).ι
    ∃ Q : FormalGlueing.extend φ M ≃+ Γ(O, p ⁻¹ᵁ V),
      ∀ (z : C) x, Q (TensorProduct.tmul A z x) =
        chartScalarMap hC (p ⁻¹ᵁ V) z * p.app V (b x) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let : Algebra A C := φ.toAlgebra
  let O := pullback q (completionSpecMap A ∣_ U)
  let p := pullback.fst q (completionSpecMap A ∣_ U)
  let hC := pullback.snd q (completionSpecMap A ∣_ U) ≫
    (completionSpecMap A ⁻¹ᵁ U).ι
  let : Algebra A Γ(Y, V) := (chartScalarMap (q ≫ U.ι) V).toAlgebra
  let B : M ≃ₗ[A] Γ(Y, V) := { __ := b, map_smul' := bs }
  have H : IsPullback p hC (q ≫ U.ι) (completionSpecMap A) :=
    (IsPullback.of_hasPullback q (completionSpecMap A ∣_ U)).paste_vert
      (isPullback_morphismRestrict (completionSpecMap A) U)
  obtain ⟨Q, hQ⟩ := chart_affine_tensor (q ≫ U.ι) p hC H V hV
  let e := TensorProduct.congr (LinearEquiv.refl A C) B
  refine ⟨e.toAddEquiv.trans Q, ?_⟩
  intro z x
  change Q (e (TensorProduct.tmul A z x)) = _
  simp only [e, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  exact hQ z (b x)

/-- Base-changing the supplied double-section equivalence gives actual sections on the
completed double intersection, with the usual formula on pure tensors. No transition
map, completed-model comparison, square equation, or d_i map occurs in the conclusion.
-/
private theorem exists_chart_tensor_restriction
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
    (T : AffineChartTransitions D t f) (i j : Fin t) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let O := pullback q (completionSpecMap A ∣_ U)
    let p := pullback.fst q (completionSpecMap A ∣_ U)
    let hC := pullback.snd q (completionSpecMap A ∣_ U) ≫
      (completionSpecMap A ⁻¹ᵁ U).ι
    let V := fun l ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f l)
    ∃ Q : FormalGlueing.extend φ
        (FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (T.F.M j))) ≃+
        Γ(O, p ⁻¹ᵁ (V i ⊓ V j)),
      ∀ (z : C) x, Q (TensorProduct.tmul A z x) =
        chartScalarMap hC (p ⁻¹ᵁ (V i ⊓ V j)) z *
          p.app (V i ⊓ V j) (T.b i j x) := by
  let V := fun l ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f l)
  have hd : IsAffineOpen (V i ⊓ V j) := by
    rw [inf_comm, ← chart_basicOpen (q ≫ U.ι) (V j) (f i)]
    exact (hV j).basicOpen _
  exact chart_completed_tensor q (V i ⊓ V j) hd
    (FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (T.F.M j)))
    (T.b i j) (T.b_scalar i j)



private theorem equiv_units {R : Type u} [CommRing R]
    (r : R) (M N : ModuleCat.{u} R) (e : FormalGlueing.localize r M ≃ₗ[R] N)
    (x : Submonoid.powers r) : IsUnit (algebraMap R (Module.End R N) x) := by
  let : IsLocalizedModule (Submonoid.powers r)
      (e.toLinearMap.comp (LocalizedModule.mkLinearMap _ M)) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
      (LocalizedModule.mkLinearMap _ M) e
  exact IsLocalizedModule.map_units
    (e.toLinearMap.comp (LocalizedModule.mkLinearMap _ M)) x

private theorem map_mk {R : Type u} [CommRing R] (r : R)
    {M N : ModuleCat.{u} R} (g : M →ₗ[R] N) (x : M) :
    FormalGlueing.localMap r g (LocalizedModule.mk x 1) = LocalizedModule.mk (g x) 1 :=
  IsLocalizedModule.map_LocalizedModules _ g x 1

private theorem swap_mk {R : Type u} [CommRing R] (r s : R)
    (M : ModuleCat.{u} R) (m : M) :
    FormalGlueing.swap r s M (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 :=
  (FormalGlueing.exists_swap r s M).exists.choose_spec m

private theorem double_ext {R : Type u} [CommRing R]
    (r s : R) (M N : ModuleCat.{u} R)
    (hr : ∀ x : Submonoid.powers r, IsUnit (algebraMap R (Module.End R N) x))
    (hs : ∀ x : Submonoid.powers s, IsUnit (algebraMap R (Module.End R N) x))
    {g g' : FormalGlueing.localize s (FormalGlueing.localize r M) →ₗ[R] N}
    (h : ∀ m : M, g (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      g' (LocalizedModule.mk (LocalizedModule.mk m 1) 1)) : g = g' := by
  apply IsLocalizedModule.ext (Submonoid.powers s)
    (LocalizedModule.mkLinearMap _ (FormalGlueing.localize r M)) hs
  apply IsLocalizedModule.ext (Submonoid.powers r)
    (LocalizedModule.mkLinearMap _ M) hr
  ext m
  exact h m

private theorem restriction_chain {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) {V₁ V₂ W : Z.Opens}
    (h₂₁ : V₂ ≤ V₁) (hW₂ : W ≤ V₂) (x : Γ(Z, V₁)) :
    chartRestriction h hW₂ (Z.presheaf.map (homOfLE h₂₁).op x) =
      Z.presheaf.map (homOfLE (hW₂.trans h₂₁)).op x := by
  change (Z.presheaf.map (homOfLE h₂₁).op ≫
    Z.presheaf.map (homOfLE hW₂).op) x = _
  rw [← Z.presheaf.map_comp]
  rfl

private theorem scalar_restrict {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) {W V : Z.Opens}
    (hVW : V ≤ W) (a : R) :
    Z.presheaf.map (homOfLE hVW).op (chartScalarMap h W a) =
      chartScalarMap h V a := by
  change ((ΓSpecIso (.of R)).inv ≫ h.appTop ≫
    Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
    Z.presheaf.map (homOfLE hVW).op) a =
      ((ΓSpecIso (.of R)).inv ≫ h.appTop ≫
        Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) a
  rw [← Z.presheaf.map_comp]
  rfl

private theorem app_restrict {O Y : Scheme.{u}} (p : O ⟶ Y)
    {V W : Y.Opens} (hWV : W ≤ V) (x : Γ(Y, V)) :
    p.app W (Y.presheaf.map (homOfLE hWV).op x) =
      O.presheaf.map (homOfLE (show p ⁻¹ᵁ W ≤ p ⁻¹ᵁ V from
        (TopologicalSpace.Opens.map p.base).monotone hWV)).op (p.app V x) := by
  change (Y.presheaf.map (homOfLE hWV).op ≫ p.app W) x =
    (p.app V ≫ O.presheaf.map (homOfLE _).op) x
  rw [p.naturality]
  rfl

private theorem compare_tmul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) (M : ModuleCat.{u} R) :
    letI : Algebra R S := φ.toAlgebra
    ∀ (z : S) (m : M),
      FormalGlueing.compare φ r M (LocalizedModule.mk (TensorProduct.tmul R z m) 1) =
        TensorProduct.tmul R z (LocalizedModule.mk m 1) := by
  let : Algebra R S := φ.toAlgebra
  intro z m
  have hh := LinearMap.congr_fun (FormalGlueing.exists_compare φ r M).exists.choose_spec
    (TensorProduct.tmul R z m)
  simpa [FormalGlueing.compare, FormalGlueing.restrictMap, FormalGlueing.extendMap] using hh

private theorem extendMapR_tmul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {M N : ModuleCat.{u} R} (g : M →ₗ[R] N) :
    letI : Algebra R S := φ.toAlgebra
    ∀ (z : S) (m : M),
      FormalGlueing.extendMapR φ g (TensorProduct.tmul R z m) =
        TensorProduct.tmul R z (g m) := by
  let : Algebra R S := φ.toAlgebra
  intro z m
  simp [FormalGlueing.extendMapR, FormalGlueing.restrictMap, FormalGlueing.extendMap]


private theorem mk_add_one {R : Type u} [CommRing R] (S : Submonoid R)
    (M : ModuleCat.{u} R) (x y : M) :
    LocalizedModule.mk (x + y) (1 : S) =
      LocalizedModule.mk x 1 + LocalizedModule.mk y 1 := by
  simpa only [LocalizedModule.mkLinearMap_apply] using
    (LocalizedModule.mkLinearMap S M).map_add x y

private theorem chart_tensor_naturality
    {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
    {O Y : Scheme.{u}} (p : O ⟶ Y) (hC : O ⟶ Spec (.of C))
    (t : ℕ) (f : Fin t → A) (V : Fin t → Y.Opens) (M : Fin t → ModuleCat.{u} A)
    (c : ∀ l, M l ≃+ Γ(Y, V l))
    (b : ∀ i j, FormalGlueing.localize (f i) (M j) ≃+ Γ(Y, V i ⊓ V j))
    (β : ∀ i j, FormalGlueing.localize (f j) (M i) ≃ₗ[A]
      FormalGlueing.localize (f i) (M j))
    (bl : ∀ i j m, b i j (β i j (LocalizedModule.mk m 1)) =
      Y.presheaf.map (homOfLE inf_le_left).op (c i m))
    (br : ∀ i j m, b i j (LocalizedModule.mk m 1) =
      Y.presheaf.map (homOfLE inf_le_right).op (c j m))
    (d : ∀ l, FormalGlueing.extend φ (M l) ≃+
      Γ(O, p ⁻¹ᵁ V l))
    : letI : Algebra A C := φ.toAlgebra
    ∀ (_dc : ∀ l m, d l (TensorProduct.tmul A (1 : C) m) = p.app (V l) (c l m))
    (_ds : ∀ l (z : C) x, d l (z • x) = chartScalarMap hC (p ⁻¹ᵁ V l) z * d l x)
    (i j : Fin t)
    (Q : FormalGlueing.extend φ
      (FormalGlueing.localize (f i) (M j)) ≃+ Γ(O, p ⁻¹ᵁ (V i ⊓ V j)))
    (_hQ : ∀ (z : C) x, Q (TensorProduct.tmul A z x) =
      chartScalarMap hC (p ⁻¹ᵁ (V i ⊓ V j)) z * p.app (V i ⊓ V j) (b i j x)),
    (∀ x : FormalGlueing.extend φ (M i),
      Q (FormalGlueing.extendMapR φ (β i j).toLinearMap
        (FormalGlueing.compare φ (f j) (M i) (LocalizedModule.mk x 1))) =
        O.presheaf.map (homOfLE
          ((TopologicalSpace.Opens.map p.base).monotone inf_le_left)).op (d i x)) ∧
    (∀ y : FormalGlueing.extend φ (M j),
      Q (FormalGlueing.compare φ (f i) (M j) (LocalizedModule.mk y 1)) =
        O.presheaf.map (homOfLE
          ((TopologicalSpace.Opens.map p.base).monotone inf_le_right)).op (d j y)) := by
  let : Algebra A C := φ.toAlgebra
  intro dc ds i j Q hQ
  have dt (l : Fin t) (z : C) (m : M l) :
      d l (TensorProduct.tmul A z m) = chartScalarMap hC (p ⁻¹ᵁ V l) z * p.app (V l) (c l m) := by
    have hh := ds l z (TensorProduct.tmul A (1 : C) m)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, dc] using hh
  constructor
  · intro x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro z m
      rw [compare_tmul, extendMapR_tmul, hQ]
      simp only [LinearEquiv.coe_coe]
      rw [bl i j m, dt, map_mul, scalar_restrict, app_restrict]
    · intro x y hx hy
      rw [mk_add_one (Submonoid.powers (f j))
        (FormalGlueing.restrict φ (FormalGlueing.extend φ (M i)))]
      simp only [map_add, hx, hy]
  · intro y
    refine TensorProduct.inductionOn y ?_ ?_
    · intro z m
      rw [compare_tmul, hQ, br, dt, map_mul, scalar_restrict, app_restrict]
    · intro x y hx hy
      rw [mk_add_one (Submonoid.powers (f i))
        (FormalGlueing.restrict φ (FormalGlueing.extend φ (M j)))]
      simp only [map_add, hx, hy]


/-- The square and cocycle paths agree on the images of original module elements.
This checks maps already supplied; it constructs no section module or equivalence.
-/
theorem affine_chart_transition_generator_coherence
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
    (T : AffineChartTransitions D t f) :
    (∀ i j : Fin t,
      ∀ m : T.F.M',
      T.F.squareLeft i j (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        T.F.squareRight i j (LocalizedModule.mk (LocalizedModule.mk m 1) 1)) ∧
    (∀ i j k : Fin t,
      ∀ m : FormalGlueing.piece (f i) (T.F.M i),
      T.F.cocycleLeft i j k (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        T.F.cocycleRight i j k (LocalizedModule.mk (LocalizedModule.mk m 1) 1)) := by
  have _ := hf
  constructor
  · intro i j m
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let p := pullback.fst q (completionSpecMap A ∣_ U)
    let hC := pullback.snd q (completionSpecMap A ∣_ U) ≫
      (completionSpecMap A ⁻¹ᵁ U).ι
    let V := fun l ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f l)
    obtain ⟨Q, hQ⟩ := exists_chart_tensor_restriction D t f hV T i j
    obtain ⟨hleft, hright⟩ := chart_tensor_naturality φ p hC t f V
      (fun l ↦ FormalGlueing.piece (f l) (T.F.M l)) T.c T.b T.F.alpha_overlap
      T.b_left T.b_right T.d T.d_chart T.d_scalar i j Q hQ
    apply Q.injective
    simp only [FormalGlueing.Transitions.squareLeft,
      FormalGlueing.Transitions.squareRight, LinearMap.comp_apply]
    rw [map_mk, swap_mk, map_mk, hleft, hright]
    simp only [LinearEquiv.coe_coe]
    rw [T.d_prime i m, T.d_prime j m]
    let O := pullback q (completionSpecMap A ∣_ U)
    change ((D.toCompleted.appTop ≫
      O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V i ≤ ⊤)).op ≫
      O.presheaf.map (homOfLE
        ((TopologicalSpace.Opens.map p.base).monotone inf_le_left)).op) (T.e m)) =
      ((D.toCompleted.appTop ≫
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op ≫
        O.presheaf.map (homOfLE
          ((TopologicalSpace.Opens.map p.base).monotone inf_le_right)).op) (T.e m))
    rw [← O.presheaf.map_comp, ← O.presheaf.map_comp]
    rfl
  · intro i j k m
    let V := fun l ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f l)
    let W := (V i ⊓ V j) ⊓ V k
    obtain ⟨e₁, h₁⟩ := exists_chart_section_localization D t f hV T j i k W
      (by dsimp [W, V]; ac_rfl)
    obtain ⟨e₂, h₂⟩ := exists_chart_section_localization D t f hV T i j k W rfl
    obtain ⟨e₃, h₃⟩ := exists_chart_section_localization D t f hV T k j i W
      (by dsimp [W, V]; ac_rfl)
    obtain ⟨e₄, h₄⟩ := exists_chart_section_localization D t f hV T j k i W
      (by dsimp [W, V]; ac_rfl)
    obtain ⟨e₅, h₅⟩ := exists_chart_section_localization D t f hV T i k j W
      (by dsimp [W, V]; ac_rfl)
    obtain ⟨e₆, h₆⟩ := exists_chart_section_localization D t f hV T k i j W
      (by dsimp [W, V]; ac_rfl)
    have hi := equiv_units (f i) _ _ e₄
    have hj := equiv_units (f j) _ _ e₆
    have hk := equiv_units (f k) _ _ e₁
    have hij : e₂.toLinearMap.comp
        (FormalGlueing.localMap (f k) (T.F.alpha_overlap i j).toLinearMap) =
        e₁.toLinearMap := by
      apply double_ext (f j) (f k) _ _ hj hk
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [map_mk]
      change e₂ (LocalizedModule.mk (T.F.alpha_overlap i j (LocalizedModule.mk x 1)) 1) =
        e₁ (LocalizedModule.mk (LocalizedModule.mk x 1) 1)
      rw [h₂, T.b_left i j x, h₁, T.b_right j i x]
      simp only [restriction_chain]
    have hsji : e₃.toLinearMap.comp
        (FormalGlueing.swap (f i) (f k) (FormalGlueing.piece (f j) (T.F.M j))) =
        e₂.toLinearMap := by
      apply double_ext (f i) (f k) _ _ hi hk
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [swap_mk, h₃, T.b_right, h₂, T.b_right]
      simp only [restriction_chain]
    have hjk : e₄.toLinearMap.comp
        (FormalGlueing.localMap (f i) (T.F.alpha_overlap j k).toLinearMap) =
        e₃.toLinearMap := by
      apply double_ext (f k) (f i) _ _ hk hi
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [map_mk]
      change e₄ (LocalizedModule.mk (T.F.alpha_overlap j k (LocalizedModule.mk x 1)) 1) =
        e₃ (LocalizedModule.mk (LocalizedModule.mk x 1) 1)
      rw [h₄, T.b_left j k x, h₃, T.b_right k j x]
      simp only [restriction_chain]
    have hik : e₅.toLinearMap.comp
        (FormalGlueing.localMap (f j) (T.F.alpha_overlap i k).toLinearMap) =
        e₆.toLinearMap := by
      apply double_ext (f k) (f j) _ _ hk hj
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [map_mk]
      change e₅ (LocalizedModule.mk (T.F.alpha_overlap i k (LocalizedModule.mk x 1)) 1) =
        e₆ (LocalizedModule.mk (LocalizedModule.mk x 1) 1)
      rw [h₅, T.b_left i k x, h₆, T.b_right k i x]
      simp only [restriction_chain]
    have hsk : e₄.toLinearMap.comp
        (FormalGlueing.swap (f i) (f j) (FormalGlueing.piece (f k) (T.F.M k))) =
        e₅.toLinearMap := by
      apply double_ext (f i) (f j) _ _ hi hj
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [swap_mk, h₄, T.b_right, h₅, T.b_right]
      simp only [restriction_chain]
    have hsi : e₆.toLinearMap.comp
        (FormalGlueing.swap (f j) (f k) (FormalGlueing.piece (f i) (T.F.M i))) =
        e₁.toLinearMap := by
      apply double_ext (f j) (f k) _ _ hj hk
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [swap_mk, h₆, T.b_right, h₁, T.b_right]
      simp only [restriction_chain]
    apply e₄.injective
    simp only [FormalGlueing.Transitions.cocycleLeft,
      FormalGlueing.Transitions.cocycleRight, LinearMap.comp_apply]
    change ((e₄.toLinearMap.comp _).comp _) _ = ((e₄.toLinearMap.comp _).comp _) _
    rw [hjk, hsk]
    change ((e₃.toLinearMap.comp _).comp _) _ = ((e₅.toLinearMap.comp _).comp _) _
    rw [hsji, hik]
    exact LinearMap.congr_fun hij _ |>.trans (LinearMap.congr_fun hsi _).symm


end AlgebraicGeometry.Scheme.CompletionGluingData
