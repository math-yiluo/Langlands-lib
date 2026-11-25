/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Completed localization and affine pullback section identifications

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, item (1)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/- Construct both maps on a single chart before choosing the finite family. -/
private theorem exists_chart_completed_localization
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (hV : IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let M' := completedSectionModule s
    let M := chartSectionModule (q ≫ U.ι) f
    ∃ (alpha :
        FormalGlueing.localize f (FormalGlueing.restrict φ M') ≃ₗ[A]
          FormalGlueing.restrict φ (FormalGlueing.extend φ
            (FormalGlueing.piece f M)))
      (d : FormalGlueing.extend φ (FormalGlueing.piece f M) ≃+
        Γ(pullback q (completionSpecMap A ∣_ U),
          (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
            ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f))),
      (∀ (z : C) (x : FormalGlueing.localize f (FormalGlueing.restrict φ M')),
        alpha ((FormalGlueing.localizedSModule φ f M').smul z x) =
          z • (alpha x : FormalGlueing.extend φ (FormalGlueing.piece f M))) ∧
      (∀ m, d (alpha (LocalizedModule.mk m 1)) =
        (pullback q (completionSpecMap A ∣_ U)).presheaf.map (homOfLE le_top).op
          (D.toCompleted.appTop m)) ∧
      (∀ m, d (TensorProduct.tmul A (1 : C) m) =
        (pullback.fst q (completionSpecMap A ∣_ U)).app _ m) ∧
      (∀ (z : C) m, d (z • m) =
        ((ΓSpecIso (.of C)).inv ≫
          (pullback.snd q (completionSpecMap A ∣_ U) ≫
            (completionSpecMap A ⁻¹ᵁ U).ι).appTop ≫
          (pullback q (completionSpecMap A ∣_ U)).presheaf.map
            (homOfLE (le_top :
              (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
                ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f) ≤ ⊤)).op).hom z * d m) := by
  classical
  dsimp only
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let V := (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f
  let W := s ⁻¹ᵁ PrimeSpectrum.basicOpen (φ f)
  let O := pullback q (completionSpecMap A ∣_ U)
  let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
  let hC := pullback.snd q (completionSpecMap A ∣_ U) ≫
    (completionSpecMap A ⁻¹ᵁ U).ι
  let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop ≫
    Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
  let aO := ((ΓSpecIso (.of C)).inv ≫ hC.appTop ≫
    O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V ≤ ⊤)).op).hom
  let aE := ((ΓSpecIso (.of C)).inv ≫ s.appTop ≫
    E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  let : Algebra A C := φ.toAlgebra
  let : Algebra A Γ(Y, V) := aY.toAlgebra
  let : Module C Γ(E, W) := Module.compHom _ aE
  have H : IsPullback p hC (q ≫ U.ι) (completionSpecMap A) :=
    (IsPullback.of_hasPullback q (completionSpecMap A ∣_ U)).paste_vert
      (isPullback_morphismRestrict (completionSpecMap A) U)
  have hUST : (⊤ : (Spec (.of C)).Opens) ≤ completionSpecMap A ⁻¹ᵁ ⊤ := by simp
  have hUSX : V ≤ (q ≫ U.ι) ⁻¹ᵁ ⊤ := by simp
  have hUY : p ⁻¹ᵁ V = p ⁻¹ᵁ V ⊓ hC ⁻¹ᵁ ⊤ := by simp
  let := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _) hV
  have Hs := (isIso_pushoutSection_iff H hUST hUSX hUY).mp inferInstance
  have Hs' : IsPushout (CommRingCat.ofHom aY)
      (CommRingCat.ofHom φ) (p.app V) (CommRingCat.ofHom aO) := by
    refine Hs.of_iso (ΓSpecIso (.of A)) (Iso.refl _) (ΓSpecIso (.of C))
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appLE, aY]
    · simp [Scheme.Hom.appLE, completionSpecMap, φ, C]
    · simp [Scheme.Hom.appLE]
    · simp [Scheme.Hom.appLE, aO]
  -- The pushout gives both tensor generator formulas, with the prescribed maps.
  let Q := ((CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).isoIsPushout
    (.of C) Γ(Y, V) Hs'.flip).commRingCatIsoToRingEquiv
  have hQ (c : C) : Q (TensorProduct.tmul A c (1 : Γ(Y, V))) = aO c := by
    exact congr($( (CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).inl_isoIsPushout_hom
      (.of C) Γ(Y, V) Hs'.flip ) c)
  have ht : D.toCompleted ≫ s = hC := by
    change (D.overlapIso.hom ≫ (s ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)).ι) ≫ s = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, D.over]
  let : IsOpenImmersion D.toCompleted := by unfold toCompleted; infer_instance
  have hW : W ≤ D.toCompleted.opensRange := by
    change W ≤ (D.overlapIso.hom ≫ (s ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)).ι).opensRange
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    apply s.preimage_mono
    change completionSpecMap A ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ _
    exact (completionSpecMap A).preimage_mono hf
  have hPV : p ⁻¹ᵁ V = D.toCompleted ⁻¹ᵁ W := by
    change (p ≫ q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f =
      (D.toCompleted ≫ s ≫ completionSpecMap A) ⁻¹ᵁ PrimeSpectrum.basicOpen f
    rw [← D.overlap_base]
  let F : Γ(E, W) ⟶ Γ(O, p ⁻¹ᵁ V) := D.toCompleted.app W ≫
    O.presheaf.map (eqToHom hPV).op
  let := D.toCompleted.isIso_app W hW
  have hQm (m : Γ(Y, V)) : Q (TensorProduct.tmul A (1 : C) m) = p.app V m := by
    exact congr($( (CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).inr_isoIsPushout_hom
      (.of C) Γ(Y, V) Hs'.flip ) m)
  have hF (c : C) : F (aE c) = aO c := by
    have hh : CommRingCat.ofHom aE ≫ F = CommRingCat.ofHom aO := by
      dsimp only [aE, aO, F, CommRingCat.ofHom_hom]
      simp only [Category.assoc]
      rw [D.toCompleted.naturality_assoc]
      simp only [← Category.assoc, ← Scheme.Hom.comp_appTop, ht]
      dsimp only [O]
      simp only [Category.assoc, ← Functor.map_comp]
      rfl
    exact congr($(hh) c)
  let : Module C Γ(O, p ⁻¹ᵁ V) := Module.compHom _ aO
  let B : FormalGlueing.piece f (chartSectionModule (q ≫ U.ι) f) ≃ₗ[A] Γ(Y, V) :=
    { __ := AddEquiv.refl _
      map_smul' := chartSectionModule_smul (q ≫ U.ι) f }
  let T := B.baseChange A C _ _
  let L : TensorProduct A C Γ(Y, V) ≃ₗ[C] Γ(O, p ⁻¹ᵁ V) :=
    { __ := Q.toAddEquiv
      map_smul' := by
        intro c x
        change Q (c • x) = aO c * Q x
        rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, map_mul, hQ]
        rfl }
  let d := T.trans L
  let FL : Γ(E, W) ≃ₗ[C] Γ(O, p ⁻¹ᵁ V) :=
    { __ := (asIso F).commRingCatIsoToRingEquiv.toAddEquiv
      map_smul' := by
        intro c x
        change F (aE c * x) = aO c * F x
        rw [map_mul, hF] }
  let χ : C →+* Γ(E, ⊤) := ((ΓSpecIso (.of C)).inv ≫ s.appTop).hom
  let ρ : Γ(E, ⊤) →+* Γ(E, W) := (E.presheaf.map (homOfLE le_top).op).hom
  let : Algebra A Γ(E, ⊤) := (χ.comp φ).toAlgebra
  let : Algebra Γ(E, ⊤) Γ(E, W) := ρ.toAlgebra
  let : Algebra A Γ(E, W) := (aE.comp φ).toAlgebra
  have : IsScalarTower A Γ(E, ⊤) Γ(E, W) :=
    IsScalarTower.of_algebraMap_eq' (show aE.comp φ = ρ.comp (χ.comp φ) from rfl)
  have hopen : W = E.basicOpen (χ (φ f)) := by
    change _ = E.basicOpen (s.appTop ((ΓSpecIso (.of C)).inv (φ f)))
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  let : IsLocalization.Away (χ (φ f)) Γ(E, W) :=
    (isAffineOpen_top E).isLocalization_of_eq_basicOpen (χ (φ f)) (homOfLE le_top) hopen
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(E, ⊤)
      (Submonoid.powers f)) Γ(E, W) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact inferInstanceAs (IsLocalization.Away (χ (φ f)) Γ(E, W))
  let e₀ : FormalGlueing.restrict φ (completedSectionModule s) ≃ₗ[A] Γ(E, ⊤) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let r := (IsScalarTower.toAlgHom A Γ(E, ⊤) Γ(E, W)).toLinearMap.comp e₀.toLinearMap
  have : IsLocalizedModule (Submonoid.powers f) r :=
    IsLocalizedModule.of_linearEquiv_right _ _ e₀
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f)
      (FormalGlueing.restrict φ (completedSectionModule s))) r
  let K := FL.trans d.symm
  let KA : FormalGlueing.restrict φ (ModuleCat.of C Γ(E, W)) ≃ₗ[A]
      FormalGlueing.restrict φ (FormalGlueing.extend φ
        (FormalGlueing.piece f (chartSectionModule (q ≫ U.ι) f))) :=
    { __ := K.toAddEquiv
      map_smul' := fun a x ↦ K.map_smul (φ a) x }
  let alpha := e.trans KA
  -- Check the completed scalar action on localization generators by extensionality.
  have he (z : C) x :
      e ((FormalGlueing.localizedSModule φ f (completedSectionModule s)).smul z x) =
        aE z * e x := by
    let M := FormalGlueing.restrict φ (completedSectionModule s)
    let a : M →ₗ[A] M :=
      { toFun := fun m ↦ (show M from χ z * (show Γ(E, ⊤) from m))
        map_add' := fun m n ↦ mul_add (χ z) (show Γ(E, ⊤) from m) (show Γ(E, ⊤) from n)
        map_smul' := fun r m ↦ by
          change χ z * (χ (φ r) * (show Γ(E, ⊤) from m)) =
            χ (φ r) * (χ z * (show Γ(E, ⊤) from m))
          exact mul_left_comm _ _ _ }
    let b : Γ(E, W) →ₗ[A] Γ(E, W) :=
      { toFun := fun n ↦ aE z * n
        map_add' := mul_add (aE z)
        map_smul' := fun r n ↦ by
          change aE z * ((aE (φ r)) * n) = aE (φ r) * (aE z * n)
          exact mul_left_comm _ _ _ }
    have hh : e.toLinearMap.comp (FormalGlueing.localMap f a) = b.comp e.toLinearMap := by
      apply IsLocalizedModule.ext (Submonoid.powers f)
        (LocalizedModule.mkLinearMap _ M) (IsLocalizedModule.map_units r)
      ext m
      simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
      rw [show FormalGlueing.localMap f a (LocalizedModule.mk m 1) =
        LocalizedModule.mk (a m) 1 from IsLocalizedModule.map_LocalizedModules _ a m 1]
      change e (LocalizedModule.mk (a m) 1) = b (e (LocalizedModule.mk m 1))
      rw [show e (LocalizedModule.mk (a m) 1) = r (a m) from
        IsLocalizedModule.linearEquiv_apply (Submonoid.powers f) _ r (a m)]
      rw [show e (LocalizedModule.mk m 1) = r m from
        IsLocalizedModule.linearEquiv_apply (Submonoid.powers f) _ r m]
      change ρ (χ z * (show Γ(E, ⊤) from m)) = aE z * ρ (show Γ(E, ⊤) from m)
      rw [map_mul]
      rfl
    have haction : (FormalGlueing.localizedSModule φ f (completedSectionModule s)).smul z x =
        FormalGlueing.localMap f a x := by
      induction x using LocalizedModule.induction_on with
      | _ m t =>
        rw [(FormalGlueing.exists_localized_s_module φ f (completedSectionModule s)).choose_spec]
        change LocalizedModule.mk (a m) t = FormalGlueing.localMap f a (LocalizedModule.mk m t)
        exact (IsLocalizedModule.map_LocalizedModules _ a m t).symm
    rw [haction]
    exact LinearMap.congr_fun hh x
  refine ⟨alpha, d.toAddEquiv, ?_, ?_, ?_, ?_⟩
  · intro z x
    change K (e ((FormalGlueing.localizedSModule φ f (completedSectionModule s)).smul z x)) =
      z • K (e x)
    rw [he]
    exact K.map_smul z (e x)
  · intro m
    change d (K (e (LocalizedModule.mk m 1))) = _
    simp only [K, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [show e (LocalizedModule.mk m 1) = r m from
      IsLocalizedModule.linearEquiv_apply (Submonoid.powers f) _ r m]
    change F (ρ m) = _
    change ((E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      D.toCompleted.app W ≫ O.presheaf.map (eqToHom hPV).op).hom
        (show Γ(E, ⊤) from m)) = _
    rw [D.toCompleted.naturality_assoc]
    dsimp only [O, Hom.appTop]
    simp only [← Functor.map_comp]
    rfl
  · intro m
    change Q (T (TensorProduct.tmul A (1 : C) m)) = _
    change Q (TensorProduct.tmul A (1 : C) m) = _
    exact hQm m
  · intro z m
    exact d.map_smul z m

/-- Completed pullback sections identify scalar extension with localized completed sections. -/
theorem exists_chart_completed_localizations
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let M' := completedSectionModule s
    let M := fun i ↦ chartSectionModule (q ≫ U.ι) (f i)
    ∃ (alpha : ∀ i,
        FormalGlueing.localize (f i) (FormalGlueing.restrict φ M') ≃ₗ[A]
          FormalGlueing.restrict φ (FormalGlueing.extend φ
            (FormalGlueing.piece (f i) (M i))))
      (d : ∀ i, FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i)) ≃+
        Γ(pullback q (completionSpecMap A ∣_ U),
          (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
            ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))),
      (∀ i (z : C) (x : FormalGlueing.localize (f i) (FormalGlueing.restrict φ M')),
        alpha i ((FormalGlueing.localizedSModule φ (f i) M').smul z x) =
          z • (alpha i x : FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i)))) ∧
      (∀ i m, d i (alpha i (LocalizedModule.mk m 1)) =
        (pullback q (completionSpecMap A ∣_ U)).presheaf.map (homOfLE le_top).op
          (D.toCompleted.appTop m)) ∧
      (∀ i m, d i (TensorProduct.tmul A (1 : C) m) =
        (pullback.fst q (completionSpecMap A ∣_ U)).app _ m) ∧
      (∀ i (z : C) m, d i (z • m) =
        ((ΓSpecIso (.of C)).inv ≫
          (pullback.snd q (completionSpecMap A ∣_ U) ≫
            (completionSpecMap A ⁻¹ᵁ U).ι).appTop ≫
          (pullback q (completionSpecMap A ∣_ U)).presheaf.map
            (homOfLE (le_top :
              (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
                ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ≤ ⊤)).op).hom z * d i m) := by
  classical
  dsimp only
  choose alpha d ha hp ht hs using fun i ↦
    exists_chart_completed_localization D (f i) (hf i) (hV i)
  exact ⟨alpha, d, ha, hp, ht, hs⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
