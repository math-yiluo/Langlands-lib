/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage
import WeilConjectures.AlgebraicGeometry.Morphisms.PointedSectionStageDescent

/-!
# Descent of a pointed smooth family to one Noetherian stage

## References

* Stacks Project, Tag 0EZJ, pointed family descent paragraph
* Stacks Project, Tag 0EZJ, family descent paragraph
* Tags 01ZM, 0C0C and 055R
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem exists_unit_stage {I : Type u} [SmallCategory I] [IsCofiltered I]
    {S : Scheme.{u}} (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)]
    [∀ i, CompactSpace (X.obj i)] [∀ i, QuasiSeparatedSpace (X.obj i)]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    ∃ i : I, IsUnit (n : Γ(X.obj i, ⊤)) := by
  obtain ⟨r, hr⟩ := isUnit_iff_exists_inv.mp hn
  obtain ⟨i, t, ht⟩ := exists_appTop_π_eq_of_isLimit X (Cone.mk S α) hα r
  have heq : (α.app i).appTop ((n : Γ(X.obj i, ⊤)) * t - 1) = 0 := by
    simpa only [map_sub, map_mul, map_natCast, map_one, ← ht, sub_eq_zero] using hr
  obtain ⟨j, f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit X (Cone.mk S α) hα _ heq
  refine ⟨j, isUnit_iff_exists_inv.mpr ⟨(X.map f).appTop t, ?_⟩⟩
  simpa only [map_sub, map_mul, map_natCast, map_one, sub_eq_zero] using hf

private theorem comparison_range_in_component {S C P T : Scheme.{u}}
    (c : C ⟶ S) [GeometricallyConnected c] (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (p : P ⟶ T) (τ : T ⟶ P) (a : C ⟶ P) (b : S ⟶ T)
    (H : IsPullback a c p b) (hcompat : σ ≫ a = b ≫ τ)
    (U : P.Opens)
    (hU : ∀ x : P, x ∈ connectedComponentIn (p ⁻¹' {p x}) (τ (p x)) → x ∈ U) :
    Set.range a ⊆ U := by
  rintro _ ⟨x, rfl⟩
  apply hU
  have hsec (s : S) : c (σ s) = s := by
    change (σ ≫ c) s = s
    rw [hσ]
    rfl
  have hcomm (x : C) : p (a x) = b (c x) := congrArg (fun f : C ⟶ T ↦ f x) H.w
  have hcompat' (s : S) : a (σ s) = τ (b s) :=
    congrArg (fun f : S ⟶ P ↦ f s) hcompat
  have hc := (c.isConnected_preimage_singleton (c x)).isPreconnected.image a
    a.continuous.continuousOn
  exact hc.subset_connectedComponentIn
    ⟨σ (c x), hsec (c x), by rw [hcompat', hcomm]⟩
    (by rintro _ ⟨y, hy, rfl⟩; simp only [Set.mem_preimage, Set.mem_singleton_iff,
      hcomm]; exact congrArg b hy) ⟨x, rfl, rfl⟩

private theorem isPullback_open_lift {S C P T : Scheme.{u}}
    {c : C ⟶ S} {p : P ⟶ T} {a : C ⟶ P} {b : S ⟶ T}
    (H : IsPullback a c p b) (U : P.Opens) (ha : Set.range a ⊆ U) :
    IsPullback (IsOpenImmersion.lift U.ι a (by simpa using ha)) c (U.ι ≫ p) b := by
  let a' := IsOpenImmersion.lift U.ι a (by simpa using ha)
  have hfac : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  refine IsPullback.of_isLimit (c := PullbackCone.mk a' c (by
    rw [← Category.assoc, hfac, H.w])) ?_
  refine PullbackCone.IsLimit.mk _ (fun s ↦ H.lift (s.fst ≫ U.ι) s.snd
    (by simpa only [Category.assoc] using s.condition)) ?_ ?_ ?_
  · intro s
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, hfac, H.lift_fst]
  · intro s
    exact H.lift_snd _ _ _
  · intro s m hm₁ hm₂
    apply H.hom_ext
    · rw [H.lift_fst, ← hfac, ← Category.assoc, hm₁]
    · rw [H.lift_snd, hm₂]

private theorem exists_pointed_model {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S C : Scheme.{u}}
    (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hN : ∀ i, IsNoetherian (X.obj i))
    (hqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S) :
    ∃ (i : I) (P : Scheme.{u}) (p : P ⟶ X.obj i) (τ : X.obj i ⟶ P) (a : C ⟶ P),
      IsPullback a c p (α.app i) ∧ σ ≫ a = α.app i ≫ τ ∧
      QuasiCompact p ∧ QuasiSeparated p ∧ Smooth p ∧ GeometricallyConnected p ∧
      τ ≫ p = 𝟙 (X.obj i) := by
  let : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f) := hXa
  let : ∀ i, IsNoetherian (X.obj i) := hN
  let : ∀ i, CompactSpace (X.obj i) := fun i ↦ inferInstance
  let : ∀ i, QuasiSeparatedSpace (X.obj i) := hqs
  obtain ⟨i₁, Y₁, q₁, hqfp, hqqc, hqqs, a₁, H₁⟩ :=
    exists_isPullback_of_finitePresentation (D := X) hα c
  let : LocallyOfFinitePresentation q₁ := hqfp
  let : QuasiCompact q₁ := hqqc
  let : QuasiSeparated q₁ := hqqs
  obtain ⟨j₁, hj₁⟩ := exists_smooth_stage_of_affine_limit X α hα hXa hN hqs q₁ c a₁ H₁
  let i := j₁.left
  let Y := pullback q₁ (X.map j₁.hom)
  let q : Y ⟶ X.obj i := pullback.snd _ _
  let : Smooth q := hj₁
  let a : C ⟶ Y := pullback.lift a₁ (c ≫ α.app i) (by
    rw [H₁.w, Category.assoc, (Cone.mk S α).w j₁.hom])
  have H : IsPullback a c q (α.app i) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q₁ (X.map j₁.hom))
    · simpa only [a, pullback.lift_fst, i, (Cone.mk S α).w j₁.hom] using H₁
    · simp [a]
  obtain ⟨k, f, τ, hτ, hτq⟩ := exists_map_at_refinement_of_affine_limit X
    (fun j ↦ inferInstance) hqs hXa α hα i q (σ ≫ a) (by
      rw [Category.assoc, H.w, ← Category.assoc, hσ, Category.id_comp])
  let j : Over i := Over.mk f
  change α.app j.left ≫ τ = σ ≫ a at hτ
  change τ ≫ q = X.map j.hom at hτq
  let P := pullback q (X.map j.hom)
  let p : P ⟶ X.obj j.left := pullback.snd _ _
  let σ₀ : X.obj j.left ⟶ P := pullback.lift τ (𝟙 _) (by simp [hτq])
  let a₀ : C ⟶ P := pullback.lift a (c ≫ α.app j.left) (by
    rw [H.w, Category.assoc, (Cone.mk S α).w j.hom])
  have Ha : IsPullback a₀ c p (α.app j.left) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q (X.map j.hom))
    · simpa [a₀, (Cone.mk S α).w j.hom] using H
    · simp [a₀]
  have hsection : σ ≫ a₀ = α.app j.left ≫ σ₀ := by
    apply pullback.hom_ext
    · simpa [a₀, σ₀, Category.assoc] using hτ.symm
    · simp only [a₀, σ₀, Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [← Category.assoc, hσ, Category.id_comp]
  have hσ₀ : σ₀ ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
  let : Smooth p := inferInstanceAs (Smooth (pullback.snd q (X.map j.hom)))
  let : QuasiCompact p := inferInstanceAs (QuasiCompact (pullback.snd q (X.map j.hom)))
  let : QuasiSeparated p :=
    inferInstanceAs (QuasiSeparated (pullback.snd q (X.map j.hom)))
  obtain ⟨U, hσU, hUgeo, hU⟩ := Smooth.exists_geometricallyIrreducible_of_section p σ₀ hσ₀
  have haU := comparison_range_in_component c σ hσ p σ₀ a₀ (α.app j.left)
    Ha hsection U hU
  let aU : C ⟶ U.toScheme := IsOpenImmersion.lift U.ι a₀ (by simpa using haU)
  let σU : X.obj j.left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι σ₀ (by simpa using hσU)
  have haUfac : aU ≫ U.ι = a₀ := IsOpenImmersion.lift_fac _ _ _
  have hσUfac : σU ≫ U.ι = σ₀ := IsOpenImmersion.lift_fac _ _ _
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian P := ⟨⟩
  let : GeometricallyIrreducible (U.ι ≫ p) := hUgeo
  refine ⟨j.left, U.toScheme, U.ι ≫ p, σU, aU,
    isPullback_open_lift Ha U haU, ?_, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  · apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, haUfac, hσUfac] using hsection
  · rw [← Category.assoc, hσUfac, hσ₀]

/-- Descend only a single family and section, together with an invertible integer.
The inverse system and its normality are supplied as input, not constructed here. -/
theorem exists_pointed_smooth_family_stage {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S C : Scheme.{u}}
    (X : I ⥤ Scheme.{u}) (α : (Functor.const I).obj S ⟶ X)
    (hα : IsLimit (Cone.mk S α))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (hN : ∀ i, IsNoetherian (X.obj i))
    (hqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    ∃ (i : I) (P : Scheme.{u}) (p : P ⟶ X.obj i) (τ : X.obj i ⟶ P) (a : C ⟶ P),
      IsPullback c a (α.app i) p ∧ σ ≫ a = α.app i ≫ τ ∧
      QuasiCompact p ∧ QuasiSeparated p ∧ Smooth p ∧ GeometricallyConnected p ∧
      τ ≫ p = 𝟙 (X.obj i) ∧ IsUnit (n : Γ(X.obj i, ⊤)) := by
  let : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f) := hXa
  let : ∀ i, IsNoetherian (X.obj i) := hN
  let : ∀ i, CompactSpace (X.obj i) := fun i ↦ inferInstance
  let : ∀ i, QuasiSeparatedSpace (X.obj i) := hqs
  obtain ⟨k, hk⟩ := exists_unit_stage X α hα n hn
  let D := Over.forget k ⋙ X
  let β := Functor.whiskerLeft (Over.forget k) α
  have hβ : IsLimit (Cone.mk S β) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget k) (Cone.mk S α)).symm hα
  obtain ⟨i, P, p, τ, a, H, hcompat, hqc, hqs', hsm, hgeo, hτ⟩ :=
    exists_pointed_model D β hβ (fun f ↦ hXa f.left)
      (fun j ↦ hN j.left) (fun j ↦ hqs j.left) c σ hσ
  refine ⟨i.left, P, p, τ, a, H.flip, hcompat, hqc, hqs', hsm, hgeo, hτ, ?_⟩
  simpa only [map_natCast] using hk.map (X.map i.hom).appTop.hom

end AlgebraicGeometry.Scheme
