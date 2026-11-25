/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.Hilbert.Representability
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Mathlib.RingTheory.Ideal.Colon
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum

/-!
# Hilbert schemes of curves

Let `f : X ⟶ S` be a separated smooth morphism of relative dimension `1`. A closed subscheme of
`X_T` which is finite locally free over `T` is a relative effective Cartier divisor
(`AlgebraicGeometry.Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite`), and such
divisors can be added, by multiplying their ideals. When the Hilbert functors `Hilb^d_{X/S}` are
representable, by schemes `H_d`, this gives addition morphisms `H_d ×[S] X ⟶ H_{d + 1}`, finite
locally free of degree `d + 1`, which show that `H_d` is smooth of relative dimension `d` over
`S`.

For a geometrically integral smooth proper curve `X` over a field `k` all Hilbert functors are
representable, and `H_d` is a smooth proper geometrically integral `k`-scheme of dimension `d`,
whose `k'`-points are the effective Cartier divisors of degree `d` on `X_{k'}`, and which carries
addition morphisms `H_{d₁} ×[k] H_{d₂} ⟶ H_{d₁ + d₂}`.

## Main statements

- `AlgebraicGeometry.IsHilbertSubscheme.mul`: the sum of two finite locally free divisors.
- `AlgebraicGeometry.exists_addition_hilbertPresheaf`: the addition morphism
  `H_d ×[S] X ⟶ H_{d + 1}` (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`).
- `AlgebraicGeometry.smoothOfRelativeDimension_of_representableBy_hilbertPresheaf`: `H_d` is
  smooth of relative dimension `d` (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`).
- `AlgebraicGeometry.isRelativeEffectiveCartier_universal_hilbertPresheaf`: the universal
  divisor and its line bundle (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`).
- `AlgebraicGeometry.hilbertPresheaf_curve_representable`,
  `AlgebraicGeometry.hilbertPresheaf_curve_points`,
  `AlgebraicGeometry.hilbertPresheaf_curve_add`: the Hilbert schemes of a smooth proper curve
  (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- An invertible ideal sheaf is of finite type: its ideal on every affine open is finitely
generated, since it is principal on the members of a cover by basic opens. -/
lemma IsInvertible.fg_ideal {E : X.IdealSheafData} (hE : E.IsInvertible) (U : X.affineOpens) :
    (E.ideal U).FG := by
  let s : Set Γ(X, U) := {g | ((E.ideal U).map
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).IsPrincipal}
  have hs : Ideal.span s = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hxU
    obtain ⟨W, hxW, hW⟩ := hE x
    obtain ⟨g, hgW, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxW⟩ hxU
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, ?_⟩, hxg⟩
    obtain ⟨a, -, ha⟩ := E.isRegularPrincipal_ideal_of_le (V := X.affineBasicOpen g) hgW hW
    change Submodule.IsPrincipal _
    rw [map_ideal_basicOpen, ha]
    exact ⟨⟨a, rfl⟩⟩
  refine Ideal.fg_of_localizationSpan s hs fun g ↦ ?_
  have := U.2.isLocalization_basicOpen g.1
  let e := IsLocalization.algEquiv (Submonoid.powers g.1) Γ(X, X.basicOpen g.1)
    (Localization.Away g.1)
  have he : (E.ideal U).map (algebraMap Γ(X, U) (Localization.Away g.1)) =
      ((E.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le g.1)).op).hom).map
        (e : Γ(X, X.basicOpen g.1) →+* Localization.Away g.1) := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact (e.commutes r).symm
  rw [he]
  obtain ⟨a, ha⟩ := g.2.principal
  rw [ha]
  exact ⟨{e a}, by rw [Ideal.map_span, Set.image_singleton, Finset.coe_singleton]; rfl⟩

/-- The **colon ideal sheaf** `(D : E)` of two ideal sheaves, for `E` of finite type: on an affine
open `U` it is `{a | a • E(U) ⊆ D(U)}`. -/
noncomputable def colon (D E : X.IdealSheafData) (hE : ∀ U, (E.ideal U).FG) :
    X.IdealSheafData where
  ideal U := (D.ideal U).colon (E.ideal U : Set Γ(X, U))
  map_ideal_basicOpen U f := by
    have := U.2.isLocalization_basicOpen f
    rw [← D.map_ideal_basicOpen, ← E.map_ideal_basicOpen]
    exact Ideal.map_colon_of_isLocalization (Submonoid.powers f) _ _ (hE U)

@[simp]
lemma ideal_colon (D E : X.IdealSheafData) (hE : ∀ U, (E.ideal U).FG) (U : X.affineOpens) :
    (D.colon E hE).ideal U = (D.ideal U).colon (E.ideal U : Set Γ(X, U)) :=
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- On an affine open where `E = (v)` and `D = (v g)` are generated by non-zerodivisors, the
colon ideal sheaf `(D : E)` is `(g)`. -/
lemma ideal_colon_of_eq_span {D E : X.IdealSheafData} (hE : ∀ U, (E.ideal U).FG)
    {W : X.affineOpens} {v g : Γ(X, W)} (hv : v ∈ nonZeroDivisors Γ(X, W))
    (hvW : E.ideal W = Ideal.span {v}) (hgW : D.ideal W = Ideal.span {v * g}) :
    (D.colon E hE).ideal W = Ideal.span {g} := by
  rw [ideal_colon, hvW, hgW, Ideal.colon_span_singleton_mul hv]

/-- Two invertible ideal sheaves `D ≤ E` have common local equations `D = (v g)`, `E = (v)` with
`v` and `g` non-zerodivisors. -/
lemma exists_affineOpens_eq_span_mul {D E : X.IdealSheafData} (hD : D.IsInvertible)
    (hE : E.IsInvertible) (hle : D ≤ E) {x : X} {O : X.Opens} (hxO : x ∈ O) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ O ∧ ∃ v g : Γ(X, W), v ∈ nonZeroDivisors Γ(X, W) ∧
      g ∈ nonZeroDivisors Γ(X, W) ∧ E.ideal W = Ideal.span {v} ∧
        D.ideal W = Ideal.span {v * g} := by
  obtain ⟨W, hxW, hWO, ⟨w, hw, hwD⟩, ⟨v, hv, hvE⟩⟩ :=
    exists_affineOpens_isRegularPrincipal hD hE hxO
  have hwv : w ∈ Ideal.span {v} := by
    rw [← hvE]
    exact hle W (by rw [hwD]; exact Ideal.mem_span_singleton_self w)
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hwv
  refine ⟨W, hxW, hWO, v, g, hv, ?_, hvE, by rw [hwD, mul_comm]⟩
  rw [mem_nonZeroDivisors_iff] at hw ⊢
  exact ⟨fun c hc ↦ hw.1 c (by linear_combination v * hc),
    fun c hc ↦ hw.2 c (by linear_combination v * hc)⟩

/-- Two ideal sheaves agreeing on a family of affine opens covering `X` are equal. -/
lemma ext_of_forall_exists {I₁ I₂ : X.IdealSheafData} (P : X.affineOpens → Prop)
    (hP : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧ P W)
    (h : ∀ W, P W → I₁.ideal W = I₂.ideal W) : I₁ = I₂ := by
  refine ext_of_iSup_eq_top (ι := {W // P W}) (fun W ↦ W.1) ?_ fun W ↦ h W.1 W.2
  rw [eq_top_iff]
  intro x _
  obtain ⟨W, hx, hW⟩ := hP x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hx⟩

/-- **Cancellation of effective Cartier divisors**: invertible ideal sheaves are cancellable. -/
lemma IsInvertible.mul_right_cancel {I₁ I₂ J : X.IdealSheafData} (hJ : J.IsInvertible)
    (h : I₁ * J = I₂ * J) : I₁ = I₂ := by
  refine ext_of_forall_exists (fun W ↦ (J.ideal W).IsRegularPrincipal) hJ fun W ⟨v, hv, hvJ⟩ ↦ ?_
  have hW := congr(($h).ideal W)
  simp only [ideal_mul, Pi.mul_apply, hvJ] at hW
  have key (A B : Ideal Γ(X, W)) (hAB : A * Ideal.span {v} = B * Ideal.span {v}) : A ≤ B := by
    intro c hc
    have : c * v ∈ B * Ideal.span {v} := by
      rw [← hAB]
      exact Ideal.mul_mem_mul hc (Ideal.mem_span_singleton_self v)
    obtain ⟨z, hz, hzc⟩ := Ideal.mem_mul_span_singleton.mp this
    have : v * (z - c) = 0 := by linear_combination hzc
    rwa [← sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hv).1 _ this)]
  exact le_antisymm (key _ _ hW) (key _ _ hW.symm)

/-- **Subtraction of effective Cartier divisors** (Stacks, Tag 0B8V): if `D ≤ E` are invertible,
then `D = (D : E) * E`. -/
lemma eq_colon_mul {D E : X.IdealSheafData} (hD : D.IsInvertible) (hE : E.IsInvertible)
    (hle : D ≤ E) : D = D.colon E hE.fg_ideal * E := by
  refine ext_of_forall_exists (fun W ↦ ∃ v g : Γ(X, W), v ∈ nonZeroDivisors Γ(X, W) ∧
    E.ideal W = Ideal.span {v} ∧ D.ideal W = Ideal.span {v * g}) (fun x ↦ ?_) ?_
  · obtain ⟨W, hx, -, v, g, hv, -, hvE, hgD⟩ :=
      exists_affineOpens_eq_span_mul hD hE hle (O := ⊤) (x := x) trivial
    exact ⟨W, hx, v, g, hv, hvE, hgD⟩
  · rintro W ⟨v, g, hv, hvE, hgD⟩
    rw [ideal_mul, Pi.mul_apply, ideal_colon_of_eq_span hE.fg_ideal hv hvE hgD, hvE, hgD,
      Ideal.span_singleton_mul_span_singleton, mul_comm]

/-- The colon ideal sheaf `(D : E)` of invertible ideal sheaves `D ≤ E` is invertible. -/
lemma isInvertible_colon {D E : X.IdealSheafData} (hD : D.IsInvertible) (hE : E.IsInvertible)
    (hle : D ≤ E) : (D.colon E hE.fg_ideal).IsInvertible := fun x ↦ by
  obtain ⟨W, hx, -, v, g, hv, hg, hvE, hgD⟩ :=
    exists_affineOpens_eq_span_mul hD hE hle (O := ⊤) (x := x) trivial
  exact ⟨W, hx, g, hg, ideal_colon_of_eq_span hE.fg_ideal hv hvE hgD⟩

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

/-- On the preimage of an affine open `W ⊆ Y`, the ring map induced by `V(I) ⟶ Y ⟶ T` is the
composite of `Γ(T, U) ⟶ Γ(Y, W)` with the quotient map by `I(W)`, up to isomorphism; in
particular it is flat if and only if `Γ(Y, W) ⧸ I(W)` is flat over `Γ(T, U)`. -/
lemma flat_appLE_subschemeι_comp_iff (π : Y ⟶ T) (I : Y.IdealSheafData) (U : T.Opens)
    (W : Y.affineOpens) (hWU : W.1 ≤ π ⁻¹ᵁ U) :
    ((I.subschemeι ≫ π).appLE U (I.subschemeι ⁻¹ᵁ W.1)
        (by rw [Scheme.Hom.comp_preimage]; exact I.subschemeι.preimage_mono hWU)).hom.Flat ↔
      ((Ideal.Quotient.mk (I.ideal W)).comp (π.appLE U W hWU).hom).Flat := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ W.1 _ hWU le_rfl, Scheme.Hom.appLE_eq_app,
    subschemeι_app, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc,
    RingHom.Flat.comp_iff_of_bijective_left]
  · rfl
  · exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

lemma flat_quotient_iff {R B : Type*} [CommRing R] [CommRing B] (φ : R →+* B) (I : Ideal B) :
    ((Ideal.Quotient.mk I).comp φ).Flat ↔
      letI := φ.toAlgebra
      Module.Flat R (B ⧸ I) := by
  let := φ.toAlgebra
  rw [← RingHom.flat_algebraMap_iff, IsScalarTower.algebraMap_eq R B (B ⧸ I),
    Ideal.Quotient.algebraMap_eq]
  rfl

/-- **Sums of relative effective Cartier divisors are flat.** If `I` and `J` are invertible
ideal sheaves on `Y` whose closed subschemes are flat over `T`, then so is the closed subscheme of
`I * J`: locally it is `B ⧸ (v₁ v₂)`, an extension of `B ⧸ (v₁)` by `B ⧸ (v₂)`. -/
lemma flat_subschemeι_mul_comp (π : Y ⟶ T) {I J : Y.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) [Flat (I.subschemeι ≫ π)] [Flat (J.subschemeι ≫ π)] :
    Flat ((I * J).subschemeι ≫ π) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).1]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := π ((I * J).subschemeι x)) trivial
  obtain ⟨W, hxW, hWU, ⟨a, ha, haI⟩, ⟨b, hb, hbJ⟩⟩ :=
    exists_affineOpens_isRegularPrincipal hI hJ (x := (I * J).subschemeι x) (O := π ⁻¹ᵁ U) hxU
  refine ⟨⟨U, hU⟩, ⟨_, W.2.preimage (I * J).subschemeι⟩, hxW,
    by rw [Scheme.Hom.comp_preimage]; exact (I * J).subschemeι.preimage_mono hWU, ?_⟩
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, ideal_mul, Pi.mul_apply,
    haI, hbJ, Ideal.span_singleton_mul_span_singleton]
  have h₁ := HasRingHomProperty.appLE (P := @Flat) (I.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage I.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact I.subschemeι.preimage_mono hWU)
  have h₂ := HasRingHomProperty.appLE (P := @Flat) (J.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage J.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact J.subschemeι.preimage_mono hWU)
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, haI] at h₁
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, hbJ] at h₂
  let := (π.appLE U W hWU).hom.toAlgebra
  exact Ideal.Quotient.flat_span_singleton_mul a b ha

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

/-- Every point of the closed subscheme of `I * J` lies in the closed subscheme of `I` or in
that of `J`. -/
lemma mem_range_inclusion_or_of_mul (I J : Y.IdealSheafData) (x : (I * J).subscheme) :
    x ∈ Set.range (inclusion (show I * J ≤ I from fun _ ↦ Ideal.mul_le_left)) ∨
      x ∈ Set.range (inclusion (show I * J ≤ J from fun _ ↦ Ideal.mul_le_right)) := by
  have hx : (I * J).subschemeι x ∈ ((I * J).support : Set Y) := by
    rw [← range_subschemeι]
    exact ⟨x, rfl⟩
  rw [support_mul] at hx
  rcases hx with hx | hx
  · left
    rw [← range_subschemeι] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, (I * J).subschemeι.isEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, inclusion_subschemeι, hy])⟩
  · right
    rw [← range_subschemeι] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, (I * J).subschemeι.isEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, inclusion_subschemeι, hy])⟩

/-- **Sums of finite closed subschemes are finite.** If the closed subschemes of `I` and `J`
are finite over `T`, then so is the closed subscheme of `I * J`, whose underlying set is the
union of theirs. It is proper, being separated and universally closed since it is covered by
the two finite closed subschemes, and it has finite fibres. -/
lemma isFinite_subschemeι_mul_comp (π : Y ⟶ T) [LocallyOfFiniteType π] {I J : Y.IdealSheafData}
    [IsFinite (I.subschemeι ≫ π)] [IsFinite (J.subschemeι ≫ π)] :
    IsFinite ((I * J).subschemeι ≫ π) := by
  set g := (I * J).subschemeι ≫ π
  set j₁ := inclusion (show I * J ≤ I from fun _ ↦ Ideal.mul_le_left)
  set j₂ := inclusion (show I * J ≤ J from fun _ ↦ Ideal.mul_le_right)
  have hj₁ : j₁ ≫ g = I.subschemeι ≫ π := by simp [j₁, g, inclusion_subschemeι_assoc]
  have hj₂ : j₂ ≫ g = J.subschemeι ≫ π := by simp [j₂, g, inclusion_subschemeι_assoc]
  have hcover := mem_range_inclusion_or_of_mul I J
  have : Surjective (coprod.desc j₁ j₂) := ⟨fun x ↦ by
    rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨(coprod.inl : _ ⟶ I.subscheme ⨿ J.subscheme) y, by
        rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : _ ⟶ I.subscheme ⨿ J.subscheme) y, by
        rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩⟩
  have : UniversallyClosed (coprod.desc j₁ j₂ ≫ g) := by
    rw [coprod.desc_comp, hj₁, hj₂]
    infer_instance
  have : UniversallyClosed g := .of_comp_surjective (coprod.desc j₁ j₂) g
  have hclosed {Z : Scheme.{u}} (j : Z ⟶ (I * J).subscheme) [IsClosedImmersion j]
      [IsFinite (j ≫ g)] :
      IsClosed (Set.range (pullback.diagonal (j ≫ g) ≫
        pullback.map (j ≫ g) (j ≫ g) g g j j (𝟙 T) (by simp) (by simp))) := by
    have : IsClosedImmersion (pullback.map (j ≫ g) (j ≫ g) g g j j (𝟙 T) (by simp) (by simp)) :=
      MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹_› ‹_› rfl rfl
    exact (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have : IsFinite (j₁ ≫ g) := by rw [hj₁]; infer_instance
  have : IsFinite (j₂ ≫ g) := by rw [hj₂]; infer_instance
  have : IsSeparated g := by
    refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
    have hrange : Set.range (pullback.diagonal g) =
        Set.range (pullback.diagonal (j₁ ≫ g) ≫
          pullback.map (j₁ ≫ g) (j₁ ≫ g) g g j₁ j₁ (𝟙 T) (by simp) (by simp)) ∪
        Set.range (pullback.diagonal (j₂ ≫ g) ≫
          pullback.map (j₂ ≫ g) (j₂ ≫ g) g g j₂ j₂ (𝟙 T) (by simp) (by simp)) := by
      rw [← pullback.comp_diagonal, ← pullback.comp_diagonal]
      apply subset_antisymm
      · rintro _ ⟨x, rfl⟩
        rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
        · exact Or.inl ⟨y, rfl⟩
        · exact Or.inr ⟨y, rfl⟩
      · rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
        · exact ⟨j₁ y, rfl⟩
        · exact ⟨j₂ y, rfl⟩
    rw [hrange]
    exact (hclosed j₁).union (hclosed j₂)
  have : LocallyQuasiFinite g := by
    refine .of_finite_preimage_singleton _ fun t ↦ ?_
    refine (((I.subschemeι ≫ π).finite_preimage_singleton t).image j₁).union
      (((J.subschemeι ≫ π).finite_preimage_singleton t).image j₂) |>.subset ?_
    intro x hx
    rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · refine Or.inl ⟨y, ?_, rfl⟩
      rw [Set.mem_preimage, ← hj₁]
      exact hx
    · refine Or.inr ⟨y, ?_, rfl⟩
      rw [Set.mem_preimage, ← hj₂]
      exact hx
  have : IsProper g := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

section Rank

set_option backward.isDefEq.respectTransparency false in
/-- The affine case of `Scheme.Hom.finrank_eq_fiberDegree`. -/
lemma Scheme.Hom.finrank_eq_fiberDegree_of_isAffine {Z : Scheme.{u}} {R : CommRingCat.{u}}
    (h : Z ⟶ Spec R) [IsAffine Z] [IsFinite h] [Flat h] (y : Spec R) :
    h.finrank y = h.fiberDegree y := by
  wlog hZ : ∃ S, Z = Spec S generalizing Z
  · have := this (Z.isoSpec.inv ≫ h) ⟨_, rfl⟩
    rwa [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.fiberDegree_comp_left_of_isIso] at this
  obtain ⟨S, rfl⟩ := hZ
  obtain ⟨φ, rfl⟩ := Spec.map_surjective h
  have h₁ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have h₂ : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank h₁ h₂]
  algebraize [φ.hom]
  have e : φ = CommRingCat.ofHom (algebraMap R S) := rfl
  conv_rhs => rw [e, Scheme.Hom.fiberDegree_SpecMap]
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap, Module.rankAtStalk_eq]
  rfl

/-- **The rank of a finite flat morphism is its fibre degree**: `f.finrank y` is the dimension
of the fibre of `f` over `y` as a `κ(y)`-vector space. -/
lemma Scheme.Hom.finrank_eq_fiberDegree {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [Flat g]
    (y : Y) : g.finrank y = g.fiberDegree y := by
  obtain ⟨R, i, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  have : IsAffine (pullback g i) := isAffine_of_isAffineHom (pullback.snd g i)
  rw [← Scheme.Hom.finrank_pullback_snd, ← g.fiberDegree_of_isPullback (.of_hasPullback g i),
    Scheme.Hom.finrank_eq_fiberDegree_of_isAffine]

/-- The rank at `t` of a finite flat closed subscheme `V(I) ⊆ Y` over `T` is the dimension over
`κ(t)` of the closed subscheme `V(I) ∩ Y_t` of the fibre `Y_t`. -/
lemma Scheme.IdealSheafData.finrank_subschemeι_comp_eq_finrankΓ {Y T : Scheme.{u}} (π : Y ⟶ T)
    (I : Y.IdealSheafData) [IsFinite (I.subschemeι ≫ π)] [Flat (I.subschemeι ≫ π)] (t : T) :
    (I.subschemeι ≫ π).finrank t =
      ((I.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t).finrankΓ := by
  have hsq := (I.isPullback_comap (π.fiberι t)).flip.paste_vert (.of_hasPullback π _)
  have : IsFinite ((I.comap (π.fiberι t)).subschemeι ≫ pullback.snd π (T.fromSpecResidueField t)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹_›
  have key := Scheme.Hom.fiberDegree_of_isPullback _ hsq (IsLocalRing.closedPoint _)
  rw [T.fromSpecResidueField_apply] at key
  rw [Scheme.Hom.finrank_eq_fiberDegree, ← key, fiberDegree_eq_finrankΓ]
  rfl

end Rank

end AlgebraicGeometry

namespace AlgebraicGeometry

section Rank

/-- The base change to a fibre of the closed subscheme of `I` is finite if `V(I)` is finite. -/
lemma Scheme.IdealSheafData.isFinite_comap_fiberι {Y T : Scheme.{u}} (π : Y ⟶ T)
    (I : Y.IdealSheafData) [IsFinite (I.subschemeι ≫ π)] (t : T) :
    IsFinite ((I.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t) :=
  MorphismProperty.of_isPullback (P := @IsFinite)
    ((I.isPullback_comap (π.fiberι t)).flip.paste_vert (.of_hasPullback π _)) ‹_›

/-- **The degree is additive on sums of relative effective Cartier divisors.** Let
`π : Y ⟶ T` be flat and locally of finite presentation and let `I, J` be invertible ideal sheaves
on `Y` such that `V(I)`, `V(J)` and `V(I * J)` are finite and flat over `T`. Then the rank of
`V(I * J)` over `T` is the sum of the ranks of `V(I)` and `V(J)`: on the fibre over `t` this is
`Scheme.IdealSheafData.finrankΓ_subschemeι_mul_comp`. -/
lemma Scheme.IdealSheafData.finrank_subschemeι_mul_comp {Y T : Scheme.{u}} (π : Y ⟶ T) [Flat π]
    [LocallyOfFinitePresentation π] {I J : Y.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) [IsFinite (I.subschemeι ≫ π)] [Flat (I.subschemeι ≫ π)]
    [IsFinite (J.subschemeι ≫ π)] [Flat (J.subschemeι ≫ π)]
    [IsFinite ((I * J).subschemeι ≫ π)] [Flat ((I * J).subschemeι ≫ π)] (t : T) :
    ((I * J).subschemeι ≫ π).finrank t =
      (I.subschemeι ≫ π).finrank t + (J.subschemeι ≫ π).finrank t := by
  have hI' : (I.comap (π.fiberι t)).IsInvertible :=
    (IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback ⟨hI, ‹_›⟩
      (IsPullback.of_hasPullback π (T.fromSpecResidueField t))).1
  have hJ' : (J.comap (π.fiberι t)).IsInvertible :=
    (IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback ⟨hJ, ‹_›⟩
      (IsPullback.of_hasPullback π (T.fromSpecResidueField t))).1
  have := I.isFinite_comap_fiberι π t
  have := J.isFinite_comap_fiberι π t
  have := (I * J).isFinite_comap_fiberι π t
  rw [comap_mul] at this
  rw [finrank_subschemeι_comp_eq_finrankΓ, finrank_subschemeι_comp_eq_finrankΓ,
    finrank_subschemeι_comp_eq_finrankΓ, comap_mul]
  exact finrankΓ_subschemeι_mul_comp (K := T.residueField t) (π.fiberToSpecResidueField t) hI' hJ'

end Rank

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

/-- **Differences of relative effective Cartier divisors are flat.** If `D ≤ E` are invertible
ideal sheaves on `Y` whose closed subschemes are flat over `T`, then so is the closed subscheme
of `(D : E)`: locally it is `B ⧸ (g)` where `D = (v g)` and `E = (v)`, the kernel of the
surjection `B ⧸ (v g) ⟶ B ⧸ (v)` of flat modules. -/
lemma flat_subschemeι_colon_comp (π : Y ⟶ T) {D E : Y.IdealSheafData} (hD : D.IsInvertible)
    (hE : E.IsInvertible) (hle : D ≤ E) [Flat (D.subschemeι ≫ π)] [Flat (E.subschemeι ≫ π)] :
    Flat ((D.colon E hE.fg_ideal).subschemeι ≫ π) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).1]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := π ((D.colon E hE.fg_ideal).subschemeι x)) trivial
  obtain ⟨W, hxW, hWU, v, g, hv, -, hvE, hgD⟩ := exists_affineOpens_eq_span_mul hD hE hle
    (x := (D.colon E hE.fg_ideal).subschemeι x) (O := π ⁻¹ᵁ U) hxU
  refine ⟨⟨U, hU⟩, ⟨_, W.2.preimage (D.colon E hE.fg_ideal).subschemeι⟩, hxW,
    by rw [Scheme.Hom.comp_preimage]; exact (D.colon E _).subschemeι.preimage_mono hWU, ?_⟩
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff,
    ideal_colon_of_eq_span hE.fg_ideal hv hvE hgD]
  have h₁ := HasRingHomProperty.appLE (P := @Flat) (D.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage D.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact D.subschemeι.preimage_mono hWU)
  have h₂ := HasRingHomProperty.appLE (P := @Flat) (E.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage E.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact E.subschemeι.preimage_mono hWU)
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, hgD] at h₁
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, hvE] at h₂
  let := (π.appLE U W hWU).hom.toAlgebra
  exact Module.Flat.of_exact_of_flat_of_flat_right _ _
    (Ideal.Quotient.injective_mulSpanSingleton v g hv)
    (Ideal.Quotient.surjective_factorSpanSingleton v g)
    (Ideal.Quotient.exact_mulSpanSingleton_factorSpanSingleton v g)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Subtraction of finite locally free divisors** (Stacks, Tags 0B8V and 0B9G). Let
`f : X ⟶ S` be smooth of relative dimension `1`, and let `D` and `E` be closed subschemes of
`X_T`, finite locally free over `T` of degrees `d₁ + d₂` and `d₂`, with `E ⊆ D`, i.e. with ideals
`I_D ≤ I_E`. Then `D = D' + E` for a closed subscheme `D'`, finite locally free of degree `d₁`:
its ideal is the colon ideal `(I_D : I_E)`, which is invertible since locally `I_E = (v)` and
`I_D = (v g)`, flat over `T` as the kernel of `𝒪/(v g) ⟶ 𝒪/(v)`, finite since `D' ⊆ D`, and of
degree `d₁` by additivity of the degree.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 1) -/
theorem IsHilbertSubscheme.exists_eq_mul {f : X ⟶ S} [SmoothOfRelativeDimension 1 f]
    {d₁ d₂ : ℕ} {T : Over S} {D E : (pullback f T.hom).IdealSheafData}
    (hD : IsHilbertSubscheme f (d₁ + d₂) T D) (hE : IsHilbertSubscheme f d₂ T E) (hle : D ≤ E) :
    ∃ D' : (pullback f T.hom).IdealSheafData, IsHilbertSubscheme f d₁ T D' ∧ D = D' * E := by
  have : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  have := SmoothOfRelativeDimension.smooth 1 (pullback.snd f T.hom)
  have hDi := hD.isInvertible
  have hEi := hE.isInvertible
  obtain ⟨_, _, _, hDr⟩ := hD
  obtain ⟨_, _, _, hEr⟩ := hE
  set D' := D.colon E hEi.fg_ideal
  have heq := Scheme.IdealSheafData.eq_colon_mul hDi hEi hle
  have hD'i := Scheme.IdealSheafData.isInvertible_colon hDi hEi hle
  have := Scheme.IdealSheafData.flat_subschemeι_colon_comp (pullback.snd f T.hom) hDi hEi hle
  have hDD' : D ≤ D' := heq.le.trans (fun U ↦ Ideal.mul_le_left)
  have : IsFinite (D'.subschemeι ≫ pullback.snd f T.hom) := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι hDD', Category.assoc]
    infer_instance
  have hlfp := ((Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_locallyQuasiFinite
    (pullback.snd f T.hom)).mp ⟨hD'i, inferInstance⟩).2.2
  refine ⟨D', ⟨inferInstance, inferInstance, hlfp, fun t ↦ ?_⟩, heq⟩
  have : IsFinite ((D' * E).subschemeι ≫ pullback.snd f T.hom) := by rw [← heq]; infer_instance
  have : Flat ((D' * E).subschemeι ≫ pullback.snd f T.hom) := by rw [← heq]; infer_instance
  have key := Scheme.IdealSheafData.finrank_subschemeι_mul_comp (pullback.snd f T.hom) hD'i hEi t
  rw [← heq, hDr, hEr] at key
  exact (Nat.add_right_cancel key).symm

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The graph `⟨x, 𝟙⟩ : T ⟶ X ×[S] T` of a morphism `x : T ⟶ X` over `S` is a closed immersion
when `X` is separated over `S`: it is a section of the separated morphism `X ×[S] T ⟶ T`. -/
lemma isClosedImmersion_lift_id (f : X ⟶ S) [IsSeparated f] {T : Over S} (x : T.left ⟶ X)
    (hx : x ≫ f = T.hom) :
    IsClosedImmersion (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom) := by
  have : IsClosedImmersion ((pullback.lift x (𝟙 T.left) (by simp [hx]) :
      T.left ⟶ pullback f T.hom) ≫ pullback.snd f T.hom) := by
    rw [pullback.lift_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f T.hom)

/-- **The graph of a point is a point of `Hilb^1`.** If `f : X ⟶ S` is separated, the graph
`Γ_x ⊆ X_T` of `x : T ⟶ X` maps isomorphically to `T`, so it is finite locally free of degree `1`
over `T`. -/
lemma isHilbertSubscheme_ker_lift_id (f : X ⟶ S) [IsSeparated f] {T : Over S} (x : T.left ⟶ X)
    (hx : x ≫ f = T.hom) :
    IsHilbertSubscheme f 1 T
      (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom).ker := by
  set s : T.left ⟶ pullback f T.hom := pullback.lift x (𝟙 T.left) (by simp [hx])
  have := isClosedImmersion_lift_id f x hx
  have := IsClosedImmersion.isIso_lift s.ker.subschemeι s (Scheme.IdealSheafData.ker_subschemeι _)
  set e := asIso (IsClosedImmersion.lift s.ker.subschemeι s
    (Scheme.IdealSheafData.ker_subschemeι s.ker).le)
  have he : e.hom ≫ s.ker.subschemeι = s := IsClosedImmersion.lift_fac _ _ _
  have hinv : s.ker.subschemeι ≫ pullback.snd f T.hom = e.inv := by
    rw [← cancel_epi e.hom, ← Category.assoc, he, e.hom_inv_id, pullback.lift_snd]
  rw [IsHilbertSubscheme, hinv]
  exact ⟨inferInstance, inferInstance, inferInstance, fun t ↦ by
    rw [Scheme.Hom.finrank_eq_one_of_isIso]
    rfl⟩

/-- **Base change of graphs.** For `φ : T' ⟶ T` over `S`, the pullback of the graph of
`x : T ⟶ X` to `X_{T'}` is the graph of `φ ≫ x`. -/
lemma ker_lift_id_comap_baseChangeMap (f : X ⟶ S) [IsSeparated f] {T T' : Over S}
    (φ : T' ⟶ T) (x : T.left ⟶ X) (hx : x ≫ f = T.hom) (x' : T'.left ⟶ X)
    (hx' : x' ≫ f = T'.hom) (hxx' : x' = φ.left ≫ x) :
    (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom).ker.comap
        (baseChangeMap f φ) =
      (pullback.lift x' (𝟙 T'.left) (by simp [hx']) : T'.left ⟶ pullback f T'.hom).ker := by
  subst hxx'
  have := isClosedImmersion_lift_id f x hx
  have hsq : IsPullback φ.left
      (pullback.lift (φ.left ≫ x) (𝟙 T'.left) (by simp [hx']) : T'.left ⟶ pullback f T'.hom)
      (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom)
      (baseChangeMap f φ) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeMap f φ)
    · simp only [pullback.lift_snd]
      exact IsPullback.of_vert_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
    · apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, pullback.lift_snd_assoc]
        rfl
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← hsq.flip.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

end AlgebraicGeometry

namespace AlgebraicGeometry

section Relative

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The underlying ideal sheaf of the element of `Hilb^d_{X/S}(T')` obtained by base change
along `φ : T' ⟶ T` is the pullback of the ideal sheaf along the base-change map. -/
@[simp]
lemma hilbertPresheaf_map_val {d : ℕ} {T T' : Over S} (φ : T' ⟶ T)
    (I : (hilbertPresheaf f d).obj (op T)) :
    ((hilbertPresheaf f d).map φ.op I).1 = I.1.comap (baseChangeMap f φ) :=
  rfl

/-- The point of `Hilb^d_{X/S}` classified by a composite `φ ≫ h` is the pullback of the point
classified by `h` along the base-change map of `φ`. -/
lemma hilbertPresheaf_homEquiv_comp_val {d : ℕ} {H : Over S}
    (e : (hilbertPresheaf f d).RepresentableBy H) {T T' : Over S} (φ : T' ⟶ T) (h : T ⟶ H) :
    (e.homEquiv (φ ≫ h)).1 = (e.homEquiv h).1.comap (baseChangeMap f φ) := by
  rw [e.homEquiv_comp]
  rfl

/-- The empty subscheme `⊤` lies in `Hilb^0_{X/S}(T)`. -/
lemma isHilbertSubscheme_top {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S) :
    IsHilbertSubscheme f 0 T ⊤ :=
  ⟨inferInstance, inferInstance, inferInstance, fun t ↦ Scheme.Hom.finrank_eq_zero_of_isEmpty _ t⟩

/-- The only element of `Hilb^0_{X/S}(T)` is the empty subscheme `⊤`. -/
lemma IsHilbertSubscheme.eq_top_of_zero {X S : Scheme.{u}} {f : X ⟶ S} {T : Over S}
    {I : (pullback f T.hom).IdealSheafData} (hI : IsHilbertSubscheme f 0 T I) : I = ⊤ := by
  obtain ⟨_, _, _, h⟩ := hI
  have : IsEmpty I.subscheme := ⟨fun x ↦ by
    simpa [h] using Scheme.Hom.one_le_finrank_map (I.subschemeι ≫ pullback.snd f T.hom) x⟩
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, ← SetLike.coe_set_eq,
    ← Scheme.IdealSheafData.range_subschemeι]
  simp [Set.range_eq_empty]

/-- `Hilb^0_{X/S}(T)` has at most one element. -/
instance hilbertPresheaf_zero_subsingleton {X S : Scheme.{u}} (f : X ⟶ S) (T : (Over S)ᵒᵖ) :
    Subsingleton ((hilbertPresheaf f 0).obj T) :=
  ⟨fun I J ↦ Subtype.ext (I.2.eq_top_of_zero.trans J.2.eq_top_of_zero.symm)⟩

/-- **The sum of two finite locally free divisors.** Let `f : X ⟶ S` be smooth of relative
dimension `1` and let `D₁, D₂ ⊆ X_T` be closed subschemes, with ideals `I₁` and `I₂`, finite
locally free of degrees `d₁` and `d₂` over `T`. Then `D₁ + D₂`, with ideal `I₁ * I₂`, is finite
locally free of degree `d₁ + d₂` over `T`.

Both are relative effective Cartier divisors by the Cartier criterion; locally `D₁ + D₂` is cut
out by the product `v₁ v₂` of local equations, and the exact sequence
`0 ⟶ 𝒪/(v₁) ⟶ 𝒪/(v₁ v₂) ⟶ 𝒪/(v₂) ⟶ 0` (the first map is multiplication by the
non-zerodivisor `v₂`) shows that `𝒪_{D₁ + D₂}` is finite flat over `T` of rank `d₁ + d₂`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 3, and
`theorem-hilbert-schemes-points-smooth-curve--1`, Step 1) -/
theorem IsHilbertSubscheme.mul [SmoothOfRelativeDimension 1 f] {d₁ d₂ : ℕ} {T : Over S}
    {I₁ I₂ : (pullback f T.hom).IdealSheafData} (h₁ : IsHilbertSubscheme f d₁ T I₁)
    (h₂ : IsHilbertSubscheme f d₂ T I₂) : IsHilbertSubscheme f (d₁ + d₂) T (I₁ * I₂) := by
  have : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  have := SmoothOfRelativeDimension.smooth 1 (pullback.snd f T.hom)
  have hI₁ := h₁.isInvertible
  have hI₂ := h₂.isInvertible
  obtain ⟨_, _, _, hr₁⟩ := h₁
  obtain ⟨_, _, _, hr₂⟩ := h₂
  have := Scheme.IdealSheafData.flat_subschemeι_mul_comp (pullback.snd f T.hom) hI₁ hI₂
  have := Scheme.IdealSheafData.isFinite_subschemeι_mul_comp (pullback.snd f T.hom) (I := I₁)
    (J := I₂)
  refine ⟨inferInstance, inferInstance,
    ((Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_locallyQuasiFinite _).mp
      ⟨hI₁.mul hI₂, inferInstance⟩).2.2, fun t ↦ ?_⟩
  rw [Scheme.IdealSheafData.finrank_subschemeι_mul_comp _ hI₁ hI₂, hr₁, hr₂]

/-- **The addition morphism on Hilbert schemes.** Let `f : X ⟶ S` be separated and smooth of
relative dimension `1`, and let `H` and `H'` represent `Hilb^d_{X/S}` and `Hilb^{d + 1}_{X/S}`.
There is a morphism `a : H ×[S] X ⟶ H'` over `S`, finite locally free of degree `d + 1`,
sending a pair `(Z, x)` of a point `Z` of `H` and a point `x` of `X` to `Z + Γ_x`, where
`Γ_x ⊆ X_T` is the graph of `x : T ⟶ X`, the kernel of `⟨x, 𝟙⟩ : T ⟶ X ×[S] T`.

The morphism `a` identifies `H ×[S] X` with the universal divisor over `H'`, since a divisor
`D` of degree `d + 1` containing the graph `Γ_x` is uniquely `D' + Γ_x` with `D'` of degree `d`.

(Stacks, Tag 0B9G; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem exists_addition_hilbertPresheaf [IsSeparated f] [SmoothOfRelativeDimension 1 f] (d : ℕ)
    (H H' : Over S) (e : (hilbertPresheaf f d).RepresentableBy H)
    (e' : (hilbertPresheaf f (d + 1)).RepresentableBy H') :
    ∃ a : pullback H.hom f ⟶ H'.left, a ≫ H'.hom = pullback.snd H.hom f ≫ f ∧
      IsFinite a ∧ Flat a ∧ LocallyOfFinitePresentation a ∧ (∀ t, a.finrank t = d + 1) ∧
      ∀ (T : Over S) (z : T ⟶ H) (x : T.left ⟶ X) (hx : x ≫ f = T.hom) (t : T ⟶ H'),
        t.left = pullback.lift z.left x (by rw [Over.w z, hx]) ≫ a →
          (e'.homEquiv t).1 = (e.homEquiv z).1 *
            (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom).ker := by
  -- the universal pair `(Z, x)` over `H ×[S] X`
  let P : Over S := Over.mk (pullback.snd H.hom f ≫ f)
  let z₀ : P ⟶ H := Over.homMk (pullback.fst H.hom f) (by simp [P, pullback.condition])
  let x₀ : P.left ⟶ X := pullback.snd H.hom f
  have hx₀ : x₀ ≫ f = P.hom := rfl
  have hΓ₀ := isHilbertSubscheme_ker_lift_id f (T := P) x₀ hx₀
  let u : (hilbertPresheaf f (d + 1)).obj (op P) :=
    ⟨_, IsHilbertSubscheme.mul f (e.homEquiv z₀).2 hΓ₀⟩
  let aP := e'.homEquiv.symm u
  have haP : e'.homEquiv aP = u := Equiv.apply_symm_apply _ _
  have hnat (T : Over S) (z : T ⟶ H) (x : T.left ⟶ X) (hx : x ≫ f = T.hom) (t : T ⟶ H')
      (ht : t.left = pullback.lift z.left x (by rw [Over.w z, hx]) ≫ aP.left) :
      (e'.homEquiv t).1 = (e.homEquiv z).1 *
        (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom).ker := by
    let w : T ⟶ P := Over.homMk (pullback.lift z.left x (by rw [Over.w z, hx])) (by simp [P, hx])
    obtain rfl : t = w ≫ aP := by
      ext1
      exact ht
    have hz : z = w ≫ z₀ := by
      ext1
      simp [w, z₀]
    rw [hilbertPresheaf_homEquiv_comp_val, haP]
    dsimp only [u]
    rw [Scheme.IdealSheafData.comap_mul,
      ← hilbertPresheaf_homEquiv_comp_val, ← hz,
      ker_lift_id_comap_baseChangeMap f w x₀ hx₀ x hx (by simp [w, x₀])]
  -- the universal divisor `D ⊆ X ×[S] H'`, finite locally free of degree `d + 1` over `H'`
  have hDu := (e'.homEquiv (𝟙 H')).2
  have hrank := hDu.2.2.2
  set Du := (e'.homEquiv (𝟙 H')).1
  have hcomap {T : Over S} (y : T ⟶ H') :
      (e'.homEquiv y).1 = Du.comap (baseChangeMap f y) := by
    simpa using hilbertPresheaf_homEquiv_comp_val f e' y (𝟙 H')
  -- `H ×[S] X ⟶ X ×[S] H'` factors through `D`
  let g : P.left ⟶ pullback f H'.hom := pullback.lift x₀ aP.left (by rw [hx₀, Over.w aP])
  have hg : (pullback.lift x₀ (𝟙 P.left) (by rw [hx₀, Category.id_comp]) :
      P.left ⟶ pullback f P.hom) ≫ baseChangeMap f aP = g := by
    apply pullback.hom_ext
    · simp [g]
    · simp only [g, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact Category.id_comp _
  have hle : Du.subschemeι.ker ≤ g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hg, ← Scheme.IdealSheafData.map_ker,
      Scheme.IdealSheafData.le_map_iff_comap_le, ← hcomap, haP]
    exact fun U ↦ Ideal.mul_le_right
  let φ : P.left ⟶ Du.subscheme := IsClosedImmersion.lift Du.subschemeι g hle
  have hφ : φ ≫ Du.subschemeι = g := IsClosedImmersion.lift_fac _ _ _
  have hφq : φ ≫ Du.subschemeι ≫ pullback.snd f H'.hom = aP.left := by
    rw [← Category.assoc, hφ, pullback.lift_snd]
  -- the inverse: a point `(D, x)` of `D` gives `D = D' + Γ_x` by subtraction
  let T₁ : Over S := Over.mk (Du.subschemeι ≫ pullback.snd f H'.hom ≫ H'.hom)
  let y : T₁ ⟶ H' := Over.homMk (Du.subschemeι ≫ pullback.snd f H'.hom)
  let x₁ : T₁.left ⟶ X := Du.subschemeι ≫ pullback.fst f H'.hom
  have hx₁ : x₁ ≫ f = T₁.hom := by simp [x₁, T₁, pullback.condition]
  have hy : (pullback.lift x₁ (𝟙 T₁.left) (by rw [hx₁, Category.id_comp]) :
      T₁.left ⟶ pullback f T₁.hom) ≫ baseChangeMap f y = Du.subschemeι := by
    apply pullback.hom_ext
    · simp [x₁, y]
    · simp only [y, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Over.homMk_left]
      exact Category.id_comp _
  have hDT : (e'.homEquiv y).1 ≤ (pullback.lift x₁ (𝟙 T₁.left)
      (by rw [hx₁, Category.id_comp]) : T₁.left ⟶ pullback f T₁.hom).ker := by
    rw [hcomap, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, hy,
      Scheme.IdealSheafData.ker_subschemeι]
  obtain ⟨D', hD', hDeq⟩ := IsHilbertSubscheme.exists_eq_mul (d₁ := d) (d₂ := 1)
    (e'.homEquiv y).2 (isHilbertSubscheme_ker_lift_id f (T := T₁) x₁ hx₁) hDT
  let z₁ : T₁ ⟶ H := e.homEquiv.symm ⟨D', hD'⟩
  have hz₁ : (e.homEquiv z₁).1 = D' := by rw [Equiv.apply_symm_apply]
  let ψ : Du.subscheme ⟶ P.left := pullback.lift z₁.left x₁ (by rw [Over.w z₁, hx₁])
  have hψa : ψ ≫ aP.left = Du.subschemeι ≫ pullback.snd f H'.hom := by
    have h := hnat T₁ z₁ x₁ hx₁ (Over.homMk (ψ ≫ aP.left) (by
      rw [Category.assoc, Over.w aP]
      simpa [P, ψ] using hx₁))
      (by simp [ψ])
    rw [hz₁, ← hDeq] at h
    exact congr_arg CommaMorphism.left (e'.homEquiv.injective (Subtype.ext h))
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono Du.subschemeι, Category.assoc, hφ, Category.id_comp]
    apply pullback.hom_ext
    · simp [g, ψ, x₀, x₁]
    · simpa [g] using hψa
  have hφx₁ : φ ≫ x₁ = x₀ := by
    rw [← Category.assoc, hφ]
    exact pullback.lift_fst _ _ _
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    let w : P ⟶ T₁ := Over.homMk φ (by
      rw [← Over.w aP, ← hφq]
      rfl)
    have hwy : w ≫ y = aP := by
      ext1
      exact hφq
    have hwz : w ≫ z₁ = z₀ := by
      refine e.homEquiv.injective (Subtype.ext ?_)
      refine Scheme.IdealSheafData.IsInvertible.mul_right_cancel hΓ₀.isInvertible ?_
      rw [hilbertPresheaf_homEquiv_comp_val, hz₁]
      conv_lhs => rw [← ker_lift_id_comap_baseChangeMap f w x₁ hx₁ x₀ hx₀ hφx₁.symm,
        ← Scheme.IdealSheafData.comap_mul, ← hDeq, ← hilbertPresheaf_homEquiv_comp_val, hwy, haP]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact congr_arg CommaMorphism.left hwz
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact hφx₁
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have : IsFinite (Du.subschemeι ≫ pullback.snd f H'.hom) := hDu.1
  have : Flat (Du.subschemeι ≫ pullback.snd f H'.hom) := hDu.2.1
  have : LocallyOfFinitePresentation (Du.subschemeι ≫ pullback.snd f H'.hom) := hDu.2.2.1
  have ha : aP.left = φ ≫ Du.subschemeι ≫ pullback.snd f H'.hom := hφq.symm
  refine ⟨aP.left, Over.w aP, ?_, ?_, ?_, fun t ↦ ?_, hnat⟩
  · rw [ha]
    infer_instance
  · rw [ha]
    infer_instance
  · rw [ha]
    infer_instance
  · rw [ha, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrank t

/-- **The Hilbert scheme of degree zero is the base.** `Hilb^0_{X/S}(T)` has exactly one
element, the empty subscheme of `X_T`, so a scheme `H` representing it is terminal over `S`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, the case `d = 0`) -/
theorem isIso_of_representableBy_hilbertPresheaf_zero {X S : Scheme.{u}} (f : X ⟶ S)
    {H : Over S} (e : (hilbertPresheaf f 0).RepresentableBy H) : IsIso H.hom := by
  have hext : ∀ {T : Over S} (a b : T ⟶ H), a = b := fun a b ↦
    e.homEquiv.injective (Subsingleton.elim _ _)
  let s : Over.mk (𝟙 S) ⟶ H := e.homEquiv.symm ⟨⊤, isHilbertSubscheme_top f _⟩
  refine ⟨s.left, ?_, by simp⟩
  have := congrArg CommaMorphism.left (hext (Over.homMk (H.hom ≫ s.left) (by simp [Over.w s]) :
    H ⟶ H) (𝟙 H))
  simpa using this

/-- **Hilbert schemes of relative curves are smooth.** Let `f : X ⟶ S` be separated and smooth
of relative dimension `1`, such that all Hilbert functors `Hilb^e_{X/S}` are representable. Then
the scheme `H` representing `Hilb^d_{X/S}` is smooth of relative dimension `d` over `S`.

For `d = 0` the representing scheme is `S`; then one inducts with the addition morphism
`H_d ×[S] X ⟶ H_{d + 1}` of `exists_addition_hilbertPresheaf`, which is finite locally free of
positive degree, hence faithfully flat, along which smoothness descends
(`smoothOfRelativeDimension_of_comp_of_isFinite_of_surjective`).

(Stacks, Tag 0B9H; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem smoothOfRelativeDimension_of_representableBy_hilbertPresheaf [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (hrep : ∀ e, (hilbertPresheaf f e).IsRepresentable) (d : ℕ)
    (H : Over S) (e : (hilbertPresheaf f d).RepresentableBy H) :
    SmoothOfRelativeDimension d H.hom := by
  induction d generalizing H with
  | zero =>
    have := isIso_of_representableBy_hilbertPresheaf_zero f e
    infer_instance
  | succ d ih =>
    obtain ⟨H₀, ⟨e₀⟩⟩ := hrep d
    have := ih H₀ e₀
    obtain ⟨a, ha, hfin, hflat, hlfp, hrank, -⟩ := exists_addition_hilbertPresheaf f d H₀ H e₀ e
    have : Surjective a :=
      (Scheme.Hom.one_le_finrank_iff_surjective a).mp fun t ↦ by simp [hrank t]
    have : SmoothOfRelativeDimension (d + 1) (a ≫ H.hom) := by
      rw [ha, ← pullback.condition, add_comm]
      infer_instance
    exact smoothOfRelativeDimension_of_comp_of_isFinite_of_surjective a H.hom (d + 1)

/-- **The universal divisor.** Let `f : X ⟶ S` be smooth of relative dimension `1`, and let `H`
represent `Hilb^d_{X/S}`. The universal closed subscheme `D_univ ⊆ X ×[S] H`, the point of
`Hilb^d_{X/S}(H)` classified by `𝟙 H`, is a relative effective Cartier divisor over `H`, and for
every point `h : T ⟶ H` the line bundle of the divisor `D_h ⊆ X_T` classified by `h` is the
pullback of `𝒪(D_univ)` along `X_T ⟶ X ×[S] H`.

For `T = Spec k` a rational point `[D]` of `H`, this says that `𝒪(D_univ)` restricts on the
fibre `{[D]} × X ≅ X` to `𝒪_X(D)`.

(Stacks, Tag 0B9J; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem isRelativeEffectiveCartier_universal_hilbertPresheaf [SmoothOfRelativeDimension 1 f]
    {d : ℕ} {H : Over S} (e : (hilbertPresheaf f d).RepresentableBy H) :
    (e.homEquiv (𝟙 H)).1.IsRelativeEffectiveCartier (pullback.snd f H.hom) ∧
      ∀ (T : Over S) (h : T ⟶ H), Nonempty ((e.homEquiv h).1.toModulesᵛ ≅
        (Scheme.Modules.pullback (baseChangeMap f h)).obj (e.homEquiv (𝟙 H)).1.toModulesᵛ) := by
  obtain ⟨hfin, hflat, hlfp, -⟩ := (e.homEquiv (𝟙 H)).2
  have hD : (e.homEquiv (𝟙 H)).1.IsRelativeEffectiveCartier (pullback.snd f H.hom) :=
    Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite _
  refine ⟨hD, fun T h ↦ ?_⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have hsq : IsPullback (baseChangeMap f h) (pullback.snd f T.hom) (pullback.snd f H.hom)
      h.left := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f H.hom)
    rw [Over.w h]
    simpa using IsPullback.of_hasPullback f T.hom
  obtain ⟨-, hiso⟩ := hD.comap_of_isPullback hsq
  have hh := hilbertPresheaf_homEquiv_comp_val f e h (𝟙 H)
  rw [Category.comp_id] at hh
  rwa [hh]

end Relative

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A geometrically integral smooth curve has a non-closed point, its generic point: otherwise
it would be a single point, of dimension `0`. -/
lemma exists_not_isClosed_singleton_of_smoothOfRelativeDimension_one
    [SmoothOfRelativeDimension 1 f] [GeometricallyIntegral f] :
    ∃ x : X, ¬ IsClosed ({x} : Set X) := by
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hdim := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mp inferInstance
  refine ⟨genericPoint X, fun h ↦ ?_⟩
  have huniv : ({genericPoint X} : Set X) = Set.univ := by
    rw [← h.closure_eq, (genericPoint_spec X).def]
  have : Subsingleton X := ⟨fun a b ↦ by
    have ha : a ∈ ({genericPoint X} : Set X) := huniv ▸ trivial
    have hb : b ∈ ({genericPoint X} : Set X) := huniv ▸ trivial
    exact ha.trans hb.symm⟩
  have : DiscreteTopology X := inferInstance
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at this
  exact absurd this (by norm_num)

/-- **A rational function regular at finitely many given points.** Let `X` be an integral
`k`-scheme whose local rings are valuation rings, and which has a point whose local ring is not a
field. For every finite set `t` of points of `X` there is a rational function `c ∈ k(X)`,
transcendental over `k`, which is regular at every point of `t`.

Take any transcendental `a` (`exists_transcendental_functionField`) and a monic `P ∈ k[T]` with
`P(ā) ≠ 0` for the residue `ā` of `a` at every point of `t` where `a` is regular, for instance
`P = T · ∏ μ + 1` with `μ` running over the minimal polynomials of the algebraic residues. Then
`c = 1 / P(a)` works: where `a` is regular, `P(a)` is a unit; where `a` has a pole, `c` vanishes. -/
theorem exists_transcendental_mem_range_stalk {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsIntegral X] (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (x₀ : X)
    (hx₀ : ringKrullDim (X.presheaf.stalk x₀) ≠ 0) (t : Finset X) :
    ∃ c : X.functionField,
      (letI := (Scheme.functionFieldRingHom k X).toAlgebra; Transcendental k c) ∧
      ∀ x ∈ t, c ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  classical
  let K := X.functionField
  let := (Scheme.functionFieldRingHom k X).toAlgebra
  obtain ⟨a, ha⟩ := Scheme.exists_transcendental_functionField (k := k) x₀ hx₀
  -- the structure maps `k → 𝒪_{X,x}` and `k → κ(x)`
  let ι (x : X) : k →+* X.presheaf.stalk x :=
    (X.presheaf.germ ⊤ x trivial).hom.comp (Scheme.globalSectionsRingHom k (X := X))
  have hι (x : X) : (algebraMap (X.presheaf.stalk x) K).comp (ι x) =
      Scheme.functionFieldRingHom k X := by
    ext r
    simp only [RingHom.algebraMap_toAlgebra, Scheme.functionFieldRingHom, ι, RingHom.coe_comp,
      Function.comp_apply]
    rw [← CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  let ψ (x : X) : k →+* IsLocalRing.ResidueField (X.presheaf.stalk x) :=
    (IsLocalRing.residue _).comp (ι x)
  -- the residue of `a` at the points where it is regular
  let r (x : X) : IsLocalRing.ResidueField (X.presheaf.stalk x) :=
    if h : IsLocalization.IsInteger (X.presheaf.stalk x) a then IsLocalRing.residue _ h.choose
    else 0
  -- a monic polynomial killing the residue, if it is algebraic
  let g (x : X) : Polynomial k := if h : (ψ x).IsIntegralElem (r x) then h.choose else 1
  have hg (x : X) : (g x).Monic := by
    simp only [g]
    split_ifs with h
    · exact h.choose_spec.1
    · exact Polynomial.monic_one
  let P : Polynomial k := Polynomial.X * ∏ y ∈ t, g y + 1
  have hPm : P.Monic := by
    refine (Polynomial.monic_X.mul (Polynomial.monic_prod_of_monic _ _ fun y _ ↦ hg y)).add_of_left
      ?_
    have hq := Polynomial.monic_prod_of_monic t g fun y _ ↦ hg y
    rw [Polynomial.degree_one, Polynomial.degree_mul, Polynomial.degree_X,
      Polynomial.degree_eq_natDegree hq.ne_zero]
    norm_cast
    omega
  have hPr (x : X) (hx : x ∈ t) : Polynomial.eval₂ (ψ x) (r x) P ≠ 0 := by
    intro h0
    by_cases hint : (ψ x).IsIntegralElem (r x)
    · have hgx : Polynomial.eval₂ (ψ x) (r x) (g x) = 0 := by
        simp only [g, dite_eq_left hint]
        exact hint.choose_spec.2
      have : Polynomial.eval₂ (ψ x) (r x) (∏ y ∈ t, g y) = 0 := by
        rw [Polynomial.eval₂_finsetProd]
        exact Finset.prod_eq_zero hx hgx
      simp [P, Polynomial.eval₂_add, Polynomial.eval₂_mul, this] at h0
    · exact hint ⟨P, hPm, h0⟩
  have hPdeg : P.natDegree ≠ 0 := by
    have hq := Polynomial.monic_prod_of_monic t g fun y _ ↦ hg y
    have hdeg : 0 < (Polynomial.X * ∏ y ∈ t, g y).degree := by
      rw [Polynomial.degree_mul, Polynomial.degree_X, Polynomial.degree_eq_natDegree hq.ne_zero]
      norm_cast
      omega
    have h1 : (1 : Polynomial k).degree < (Polynomial.X * ∏ y ∈ t, g y).degree := by
      rwa [Polynomial.degree_one]
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt h1]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mpr hdeg).ne'
  have ha0 : a ≠ 0 := fun h ↦ ha (h ▸ isAlgebraic_zero)
  have hval' (x : X) {v : X.presheaf.stalk x} (hv : IsUnit v) :
      algebraMap (X.presheaf.stalk x) K ↑hv.unit⁻¹ = (algebraMap (X.presheaf.stalk x) K v)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, IsUnit.mul_val_inv, map_one])
  refine ⟨(Polynomial.aeval a P)⁻¹, fun hc ↦ ha ?_, fun x hx ↦ ?_⟩
  · refine IsAlgebraic.of_aeval P hPdeg ?_ (IsAlgebraic.inv_iff.mp hc)
    rw [hPm.leadingCoeff]
    exact one_mem _
  by_cases hint : IsLocalization.IsInteger (X.presheaf.stalk x) a
  · -- `a` is regular at `x`, so `P(a)` is a unit there
    have ha' : algebraMap _ K hint.choose = a := hint.choose_spec
    have hr : r x = IsLocalRing.residue _ hint.choose := by simp [r, dite_eq_left hint]
    have hv : IsUnit (Polynomial.eval₂ (ι x) hint.choose P) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, Polynomial.hom_eval₂, ← hr]
      exact hPr x hx
    refine ⟨↑hv.unit⁻¹, ?_⟩
    rw [hval', Polynomial.hom_eval₂, hι, ha']
    rfl
  · -- `a` has a pole at `x`, so `a⁻¹` lies in the maximal ideal and `1 / P(a)` vanishes there
    obtain ⟨b, hb⟩ := (ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) a).resolve_left
      hint
    have hbm : b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      refine (IsLocalRing.mem_maximalIdeal _).mpr fun hbu ↦ hint ⟨↑hbu.unit⁻¹, ?_⟩
      rw [hval', hb, inv_inv]
    have hw : IsUnit (Polynomial.eval₂ (ι x) b P.reverse) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, Polynomial.hom_eval₂,
        (IsLocalRing.residue_eq_zero_iff b).mpr hbm, Polynomial.eval₂_at_zero,
        Polynomial.coeff_zero_reverse, hPm.leadingCoeff, map_one]
      exact one_ne_zero
    let := invertibleOfNonzero ha0
    have key : Polynomial.aeval a P =
        algebraMap _ K (Polynomial.eval₂ (ι x) b P.reverse) * a ^ P.natDegree := by
      rw [Polynomial.hom_eval₂, hι, hb, ← invOf_eq_inv, Polynomial.eval₂_reverse_mul_pow]
      rfl
    refine ⟨↑hw.unit⁻¹ * b ^ P.natDegree, ?_⟩
    rw [map_mul, map_pow, hval', hb, key, mul_inv, inv_pow]

/-- **Points where the coordinate is regular lie in the affine chart.** Let `π : X ⟶ ℙ¹_k` be the
morphism of a rational function `c` (`exists_hom_projectiveLine_of_functionField`). If `c` is
regular at `x`, then `π(x)` lies in the affine chart `z ↦ [1 : z]`: the morphisms
`Spec 𝒪_{X,x} ⟶ X ⟶ ℙ¹_k` and `Spec 𝒪_{X,x} ⟶ 𝔸¹_k ⟶ ℙ¹_k`, `z ↦ c`, agree on the generic point,
hence agree, `ℙ¹_k` being separated and `𝒪_{X,x}` a valuation ring. -/
theorem mem_opensRange_infinityChart_of_mem_range_stalk {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsIntegral X] (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (c : X.functionField)
    (π : X ⟶ ProjectiveLine (Spec (.of k))) [π.IsOver (Spec (.of k))]
    (hπ : ∀ hs, X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
      (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (Scheme.functionFieldCoordinates c) hs)
    {x : X} (hx : c ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    π x ∈ (ProjectiveLine.infinityChart (Spec (.of k))).opensRange := by
  obtain ⟨c', rfl⟩ := hx
  have := hval x
  let R := X.presheaf.stalk x
  let K := X.functionField
  let φ : R ⟶ K := X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
  have hφ : Spec.map φ ≫ X.fromSpecStalk x = X.fromSpecFunctionField :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let i₂ : Spec R ⟶ Spec (.of k) := X.fromSpecStalk x ≫ X ↘ Spec (.of k)
  let b : Γ(Spec K, ⊤) := (Scheme.ΓSpecIso K).inv (φ c')
  have hπb : X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
      (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (ProjectiveLine.pairSections 1 b)
      (ProjectiveLine.span_range_one_pairSections b) := by
    have key : ∀ (v : ULift.{u} (Fin 2) → Γ(Spec K, ⊤))
        (_ : v = Scheme.functionFieldCoordinates (algebraMap R K c')) hs,
        X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
          (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) v hs := by
      rintro v rfl hs
      exact hπ hs
    refine key _ ?_ _
    funext ⟨i⟩
    fin_cases i
    · simp [ProjectiveLine.pairSections, Scheme.functionFieldCoordinates]
    · rfl
  -- the two lifts of the valuative square
  let l₁ : Spec R ⟶ ProjectiveLine (Spec (.of k)) := X.fromSpecStalk x ≫ π
  let l₂ : Spec R ⟶ ProjectiveLine (Spec (.of k)) :=
    AffineSpace.homOfVector i₂ (fun _ ↦ (Scheme.ΓSpecIso R).inv c') ≫
      ProjectiveLine.infinityChart (Spec (.of k))
  have hsq : CommSq (X.fromSpecFunctionField ≫ π)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) i₂ := ⟨by
    rw [Category.assoc, HomIsOver.comp_over, ← hφ, Category.assoc]
    rfl⟩
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₁ = X.fromSpecFunctionField ≫ π := by
    rw [← hφ, Category.assoc]
    rfl
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₂ =
      X.fromSpecFunctionField ≫ π := by
    have e₁ : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ =
        X.fromSpecFunctionField ≫ X ↘ Spec (.of k) := by
      rw [← hφ, Category.assoc]
      rfl
    have e₂ : (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop
        ((Scheme.ΓSpecIso R).inv c') = b :=
      congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K))).hom c').symm
    have key : ∀ {Z : Scheme.{u}} (g g' : Z ⟶ Spec (.of k)) (v v' : ULift.{u} (Fin 2) → Γ(Z, ⊤))
        hs hs', g = g' → v = v' →
        ProjectiveSpace.homOfSections g v hs = ProjectiveSpace.homOfSections g' v' hs' := by
      rintro Z g _ v _ hs hs' rfl rfl
      rfl
    rw [hπb, ← Category.assoc, AffineSpace.comp_homOfVector]
    simp only [Function.comp_def]
    rw [ProjectiveLine.homOfVector_comp_infinityChart]
    exact key _ _ _ _ _ _ e₁ (by rw [e₂])
  have hsep : ValuativeCriterion.Uniqueness (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    IsSeparated.valuativeCriterion _
  have hl : l₁ = l₂ := by
    have := hsep ⟨R, K, X.fromSpecFunctionField ≫ π, i₂, hsq⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim
      (⟨l₁, h₁, by simp only [l₁, i₂, Category.assoc, HomIsOver.comp_over]⟩ : hsq.LiftStruct)
      ⟨l₂, h₂, by simp only [l₂, i₂, Category.assoc, ProjectiveLine.infinityChart_over,
        AffineSpace.homOfVector_over]⟩)
  have hx : π x = l₂ (IsLocalRing.closedPoint R) := by
    rw [← hl]
    exact congrArg π Scheme.fromSpecStalk_closedPoint.symm
  rw [hx]
  exact ⟨_, rfl⟩

/-- **Finite sets of points of a curve lie in an affine open.** Let `X` be a geometrically
integral smooth proper curve over `k`. Every finite set `t` of points of `X` is contained in an
affine open of `X`.

Choose a rational function `c`, transcendental over `k` and regular at the points of `t`
(`exists_transcendental_mem_range_stalk`). The induced morphism `π : X ⟶ ℙ¹_k` is finite
(`isFinite_flat_of_hom_projectiveLine_of_functionField`) and maps `t` into the affine chart
(`mem_opensRange_infinityChart_of_mem_range_stalk`), whose preimage is affine.

The blueprint instead removes a closed point `Q ∉ t`, using that `𝒪_X(Q)` is ample by
Riemann–Roch; the argument here avoids Riemann–Roch.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 0) -/
theorem exists_affineOpens_forall_mem_of_curve [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (t : Finset X) : ∃ U : X.affineOpens, ∀ x ∈ t, x ∈ U.1 := by
  classical
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have hf : X ↘ Spec (.of k) = f := rfl
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) := by rw [hf]; infer_instance
  have : IsProper (X ↘ Spec (.of k)) := by rw [hf]; infer_instance
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  have hval := Scheme.valuationRing_stalk (X ↘ Spec (.of k))
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  obtain ⟨x₀, -, hx₀⟩ := (isClosed_univ (X := X)).exists_closed_singleton
    ⟨genericPoint X, trivial⟩
  have hdim : ringKrullDim (X.presheaf.stalk x₀) ≠ 0 := by
    rw [Scheme.ringKrullDim_stalk_eq_one_of_isClosed (X ↘ Spec (.of k)) hx₀]
    exact one_ne_zero
  obtain ⟨c, hc, hct⟩ := exists_transcendental_mem_range_stalk (k := k) hval x₀ hdim t
  obtain ⟨π, hπ, hπc⟩ := Scheme.exists_hom_projectiveLine_of_functionField c hc
  have := (Scheme.isFinite_flat_of_hom_projectiveLine_of_functionField c hc π hπc).1
  have hW : IsAffineOpen (ProjectiveLine.infinityChart (Spec (.of k))).opensRange :=
    isAffineOpen_opensRange _
  exact ⟨⟨π ⁻¹ᵁ _, hW.preimage π⟩, fun x hx ↦
    mem_opensRange_infinityChart_of_mem_range_stalk hval c π hπc (hct x hx)⟩

/-- **The Hilbert functors of a curve are representable.** For a geometrically integral smooth
proper curve `X` over `k`, every `Hilb^d_{X/k}` is representable: `X` is separated over `k`,
and every finite set of points lies in an affine open by
`exists_affineOpens_forall_mem_of_curve`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 1, representability) -/
theorem isRepresentable_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) : (hilbertPresheaf f d).IsRepresentable := by
  classical
  refine isRepresentable_hilbertPresheaf f d fun s t _ ↦ ?_
  obtain ⟨U, hU⟩ := exists_affineOpens_forall_mem_of_curve f (t.image (f.fiberι s).base)
  exact ⟨U, fun x hx ↦ hU _ (Finset.mem_image_of_mem _ hx)⟩

/-- **Hilbert schemes are separated.** If `f : X ⟶ S` is separated and `H` represents
`Hilb^d_{X/S}`, then `H` is separated over `S`: for the two points `Z₁, Z₂` of `Hilb^d_{X/S}` over
`H ×[S] H` the loci where `Z₁ ⊆ Z₂` and where `Z₂ ⊆ Z₁` are closed
(`exists_idealSheafData_le_ker_iff_comap_le`), and the diagonal of `H` is their intersection.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 1, separatedness) -/
theorem isSeparated_of_representableBy_hilbertPresheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] {d : ℕ} {H : Over S} (e : (hilbertPresheaf f d).RepresentableBy H) :
    IsSeparated H.hom := by
  let P : Over S := Over.mk (pullback.fst H.hom H.hom ≫ H.hom)
  let p₁ : P ⟶ H := Over.homMk (pullback.fst H.hom H.hom)
  let p₂ : P ⟶ H := Over.homMk (pullback.snd H.hom H.hom) pullback.condition.symm
  obtain ⟨K₁, hK₁⟩ := exists_idealSheafData_le_ker_iff_comap_le f (e.homEquiv p₁).2
    (e.homEquiv p₂).1
  obtain ⟨K₂, hK₂⟩ := exists_idealSheafData_le_ker_iff_comap_le f (e.homEquiv p₂).2
    (e.homEquiv p₁).1
  -- a morphism `φ` to `P` factors through `K₁ ⊔ K₂` iff `φ ≫ p₁ = φ ≫ p₂`
  have key (T' : Over S) (φ : T' ⟶ P) : K₁ ⊔ K₂ ≤ φ.left.ker ↔ φ ≫ p₁ = φ ≫ p₂ := by
    rw [sup_le_iff, hK₁, hK₂, ← le_antisymm_iff, ← hilbertPresheaf_homEquiv_comp_val,
      ← hilbertPresheaf_homEquiv_comp_val]
    refine ⟨fun h ↦ e.homEquiv.injective (Subtype.ext h.symm), fun h ↦ by rw [h]⟩
  set K := K₁ ⊔ K₂
  let c : Over.mk (K.subschemeι ≫ P.hom) ⟶ P := Over.homMk K.subschemeι
  have hc : c ≫ p₁ = c ≫ p₂ := (key _ c).mp (by simp [c, K.ker_subschemeι])
  let δ : Over.mk H.hom ⟶ P := Over.homMk (pullback.diagonal H.hom) (by simp [P])
  have hδ : K ≤ δ.left.ker := (key _ δ).mpr (by
    ext1
    simp [δ, p₁, p₂])
  let h : H.left ⟶ K.subscheme := δ.left.toImage ≫ Scheme.IdealSheafData.inclusion hδ
  have hh : h ≫ K.subschemeι = pullback.diagonal H.hom := by simp [h, δ]
  let g : K.subscheme ⟶ H.left := K.subschemeι ≫ pullback.fst H.hom H.hom
  have : IsIso h := by
    refine ⟨g, ?_, ?_⟩
    · simp [g, reassoc_of% hh]
    · rw [← cancel_mono K.subschemeι, Category.assoc, hh, Category.id_comp]
      apply pullback.hom_ext
      · simp [g]
      · have := congrArg CommaMorphism.left hc
        simp only [Over.comp_left, Over.homMk_left, c, p₁, p₂] at this
        simp [g, this]
  refine ⟨?_⟩
  rw [← hh]
  infer_instance

/-- A locally of finite type morphism to the spectrum of a field is universally open: it is flat
(every module over a field is flat) and locally of finite presentation (the base is
noetherian). -/
lemma universallyOpen_of_locallyOfFiniteType_spec_field {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType g] : UniversallyOpen g := by
  have : LocallyOfFinitePresentation g :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  infer_instance

/-- The identity of `Spec k` is geometrically irreducible. -/
lemma geometricallyIrreducible_id_spec_field : GeometricallyIrreducible (𝟙 (Spec (.of k))) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  rw [(asIso (pullback.snd (𝟙 _) y)).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

/-- **The Hilbert scheme of a curve is dominated by a power of the curve.** For a geometrically
integral smooth proper curve `X` over `k` and `H` representing `Hilb^d_{X/k}`, there is a
surjection onto `H` over `k` from a proper geometrically irreducible `k`-scheme, namely the
iterated addition `X^d ⟶ H`, `(x₁, …, x_d) ↦ x₁ + ⋯ + x_d`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 1, the morphism `π_d`) -/
theorem exists_surjective_of_representableBy_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIntegral f] (d : ℕ) (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf f d).RepresentableBy H) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (π : Y ⟶ H.left), IsProper q ∧
      GeometricallyIrreducible q ∧ Surjective π ∧ π ≫ H.hom = q := by
  induction d generalizing H with
  | zero =>
    have := isIso_of_representableBy_hilbertPresheaf_zero f e
    exact ⟨Spec (.of k), 𝟙 _, inv H.hom, inferInstance,
      geometricallyIrreducible_id_spec_field, inferInstance, by simp⟩
  | succ d ih =>
    obtain ⟨H₀, ⟨e₀⟩⟩ := isRepresentable_hilbertPresheaf_curve f d
    obtain ⟨Y, _, π, hq, hirr, hπ, rfl⟩ := ih H₀ e₀
    obtain ⟨a, ha, hfin, hflat, hlfp, hrank, -⟩ := exists_addition_hilbertPresheaf f d H₀ H e₀ e
    have hasurj : Surjective a :=
      (Scheme.Hom.one_le_finrank_iff_surjective a).mp fun t ↦ by simp [hrank t]
    have := universallyOpen_of_locallyOfFiniteType_spec_field f
    have := universallyOpen_of_locallyOfFiniteType_spec_field (π ≫ H₀.hom)
    refine ⟨pullback (π ≫ H₀.hom) f, pullback.fst _ _ ≫ π ≫ H₀.hom,
      (pullbackRightPullbackFstIso H₀.hom f π).inv ≫ pullback.snd _ _ ≫ a, inferInstance,
      GeometricallyIrreducible.comp _ _, inferInstance, ?_⟩
    rw [Category.assoc, Category.assoc, ha, pullbackRightPullbackFstIso_inv_snd_snd_assoc,
      pullback.condition]

/-- **The Hilbert scheme of a curve is proper and geometrically integral.** For a geometrically
integral smooth proper curve `X` over `k`, the scheme `H` representing `Hilb^d_{X/k}` is proper
and geometrically integral over `k`: it is separated, it is the image of the proper
geometrically irreducible `X^d`, and it is smooth, hence geometrically reduced.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 1) -/
theorem isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f] (d : ℕ)
    (H : Over (Spec (.of k))) (e : (hilbertPresheaf f d).RepresentableBy H) :
    IsProper H.hom ∧ GeometricallyIntegral H.hom := by
  have := isSeparated_of_representableBy_hilbertPresheaf f e
  have hsm := smoothOfRelativeDimension_of_representableBy_hilbertPresheaf f
    (isRepresentable_hilbertPresheaf_curve f) d H e
  have := SmoothOfRelativeDimension.smooth d H.hom
  obtain ⟨Y, _, π, hq, hirr, hπ, rfl⟩ :=
    exists_surjective_of_representableBy_hilbertPresheaf_curve f d H e
  have : UniversallyClosed H.hom := UniversallyClosed.of_comp_surjective π H.hom
  refine ⟨⟨⟩, ?_⟩
  have := Smooth.geometricallyReduced H.hom
  have : GeometricallyIrreducible H.hom := by
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
    have : IrreducibleSpace ↥(Limits.pullback (π ≫ H.hom) y) :=
      GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
    have hs : Surjective ((pullbackRightPullbackFstIso H.hom y π).inv ≫ pullback.snd _ _) :=
      inferInstance
    exact hs.surj.irreducibleSpace (Scheme.Hom.continuous _)
  exact .of_geometricallyReduced_of_geometricallyIrreducible _

/-- **The Hilbert scheme of a smooth projective curve.** For a geometrically integral smooth
proper curve `X` over `k` and `d : ℕ`, the functor `Hilb^d_{X/k}` is represented by a smooth
proper geometrically integral `k`-scheme `H` of dimension `d`, and `H ×[k] X` carries an
effective Cartier divisor `D` which is universal, in the sense that the point of `Hilb^d_{X/k}`
classified by a `k`-morphism `h : T ⟶ H` is the pullback of `D` along the induced morphism
`X_T ⟶ H ×[k] X`:

```
        X_T ──────────────▶ H ×[k] X ─────▶ X
         │  ⟨pr_T ≫ h, pr_X⟩    │            │
         │                      │            f
         ▼                      ▼            ▼
         T ─────── h ─────────▶ H ─── p ──▶ Spec k
```

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, parts (1) and (3)) -/
theorem hilbertPresheaf_curve_representable [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) :
    ∃ (H : Scheme.{u}) (p : H ⟶ Spec (.of k)), SmoothOfRelativeDimension d p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ ∃ e : (hilbertPresheaf f d).RepresentableBy (Over.mk p),
        ∃ D : (Limits.pullback p f).IdealSheafData, IsEffectiveCartierCenter D.subschemeι ∧
          ∀ (T : Over (Spec (.of k))) (h : T.left ⟶ H) (hh : h ≫ p = T.hom),
            D.comap (Limits.pullback.lift (Limits.pullback.snd f T.hom ≫ h)
                (Limits.pullback.fst f T.hom)
                (by rw [Category.assoc, hh, Limits.pullback.condition])) =
              (e.homEquiv (Over.homMk h hh)).1 := by
  obtain ⟨H, ⟨e⟩⟩ := isRepresentable_hilbertPresheaf_curve f d
  obtain ⟨hprop, hint⟩ :=
    isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve f d H e
  refine ⟨H.left, H.hom, smoothOfRelativeDimension_of_representableBy_hilbertPresheaf f
    (isRepresentable_hilbertPresheaf_curve f) d H e, hprop, hint, e,
    (e.homEquiv (𝟙 H)).1.comap (pullbackSymmetry H.hom f).hom, ?_, fun T h hh ↦ ?_⟩
  · have hD := (isRelativeEffectiveCartier_universal_hilbertPresheaf f e).1.1
    exact (hD.comap_of_flat _).isEffectiveCartierCenter
  · rw [← Scheme.IdealSheafData.comap_comp]
    have : Over.homMk (U := T) (V := Over.mk H.hom) h hh = Over.homMk h hh ≫ 𝟙 H := rfl
    rw [this, hilbertPresheaf_homEquiv_comp_val]
    congr 1
    apply pullback.hom_ext <;> simp

/-- **The points of the Hilbert scheme of a curve.** For a field extension `k'` of `k`, the
`k'`-points of `Hilb^d_{X/k}` are exactly the effective Cartier divisors of degree `d` on
`X_{k'}`. Since both sides are described by ideal sheaves on `X_{k'}`, the bijection is the
identity on underlying ideal sheaves, which is the naturality in `k'`.

An effective Cartier divisor `D` on `X_{k'}` is finite over `k'`, since `X_{k'}` is a proper curve
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_and_locallyOfFinitePresentation`),
and flat, since `k'` is a field; its degree is the rank `Scheme.Hom.finrank` of `D ⟶ Spec k'`,
the dimension of `Γ(D, 𝒪_D)` over `k'`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, part (2)) -/
theorem hilbertPresheaf_curve_points [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) (k' : Type u) [Field k'] [Algebra k k']
    (T : Over (Spec (.of k))) (hT : T = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (I : (Limits.pullback f T.hom).IdealSheafData) :
    (∃ Z : (hilbertPresheaf f d).obj (op T), Z.1 = I) ↔
      IsEffectiveCartierCenter I.subschemeι ∧
        ∀ t, (I.subschemeι ≫ Limits.pullback.snd f T.hom).finrank t = d := by
  constructor
  · rintro ⟨⟨I, hfin, hflat, hlfp, hrank⟩, rfl⟩
    exact ⟨(Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite
      (pullback.snd f T.hom)).1.isEffectiveCartierCenter, hrank⟩
  · rintro ⟨hI, hrank⟩
    subst hT
    have hI : I.IsInvertible := by
      rw [isEffectiveCartierCenter_iff_isInvertible_ker, Scheme.IdealSheafData.ker_subschemeι] at hI
      exact hI
    have hflat : Flat
        (I.subschemeι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
      Flat.of_field k' _
    obtain ⟨hfin, hlfp⟩ := hI.isFinite_and_locallyOfFinitePresentation _ hflat
    exact ⟨⟨I, hfin, hflat, hlfp, hrank⟩, rfl⟩

/-- For a geometrically integral smooth proper curve `X` over `k`, a scheme representing
`Hilb^d_{X/k}` is proper over `k`. -/
theorem isProper_of_representableBy_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIntegral f] (d : ℕ) (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf f d).RepresentableBy H) : IsProper H.hom := by
  have := isSeparated_of_representableBy_hilbertPresheaf f e
  have := smoothOfRelativeDimension_of_representableBy_hilbertPresheaf f
    (isRepresentable_hilbertPresheaf_curve f) d H e
  have := SmoothOfRelativeDimension.smooth d H.hom
  obtain ⟨Y, _, π, hq, -, hπ, rfl⟩ :=
    exists_surjective_of_representableBy_hilbertPresheaf_curve f d H e
  have : UniversallyClosed H.hom := UniversallyClosed.of_comp_surjective π H.hom
  exact ⟨⟩

/-- **The addition morphism is finite locally free.** For a geometrically integral smooth proper
curve `X` over `k`, let `H₁`, `H₂` and `H` represent `Hilb^{d₁}_{X/k}`, `Hilb^{d₂}_{X/k}` and
`Hilb^{d₁ + d₂}_{X/k}`, and let `α : H₁ ×[k] H₂ ⟶ H` be the addition morphism, the morphism
classifying the sum of the two universal divisors. Then `α` is finite, flat and locally of
finite presentation of degree `(d₁ + d₂).choose d₁`.

By induction on `d₂`; for `d₂ = 0` the morphism `α` is an isomorphism. For the inductive step,
let `a : H₂' ×[k] X ⟶ H₂` and `b : H₁₂ ×[k] X ⟶ H` be the addition morphisms
(`exists_addition_hilbertPresheaf`) and `α₀ : H₁ ×[k] H₂' ⟶ H₁₂` the addition morphism in
degrees `d₁` and `d₂ - 1`. By associativity of the sum of divisors, `α ∘ (1 × a) = b ∘ (α₀ × 1)`
on `H₁ ×[k] H₂' ×[k] X`. Here `1 × a` is finite locally free and surjective of degree `d₂`, and
`b ∘ (α₀ × 1)` is finite locally free of degree `(d₁ + d₂ - 1).choose d₁ * (d₁ + d₂)`. So `α`
is proper (`H₁ ×[k] H₂` is proper and `H` is separated) with finite fibres, hence finite; it is
flat by descent along `1 × a` (`AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective`), and its
degree `N` satisfies `d₂ N = (d₁ + d₂ - 1).choose d₁ * (d₁ + d₂)`, by multiplicativity of
degrees (`Scheme.Hom.finrank_comp_of_forall_finrank_eq`).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, Step 3) -/
theorem isFinite_flat_finrank_of_hilbertPresheaf_add [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIntegral f] (d₁ d₂ : ℕ) (H₁ H₂ H : Over (Spec (.of k)))
    (e₁ : (hilbertPresheaf f d₁).RepresentableBy H₁)
    (e₂ : (hilbertPresheaf f d₂).RepresentableBy H₂)
    (e : (hilbertPresheaf f (d₁ + d₂)).RepresentableBy H)
    (α : Over.mk (pullback.fst H₁.hom H₂.hom ≫ H₁.hom) ⟶ H)
    (hα : (e.homEquiv α).1 =
      (e₁.homEquiv (Over.homMk (pullback.fst H₁.hom H₂.hom))).1 *
        (e₂.homEquiv (Over.homMk (pullback.snd H₁.hom H₂.hom) pullback.condition.symm)).1) :
    IsFinite α.left ∧ Flat α.left ∧ LocallyOfFinitePresentation α.left ∧
      ∀ t, α.left.finrank t = (d₁ + d₂).choose d₁ := by
  induction d₂ generalizing H₂ H with
  | zero =>
    have := isIso_of_representableBy_hilbertPresheaf_zero f e₂
    rw [(e₂.homEquiv _).2.eq_top_of_zero, Scheme.IdealSheafData.mul_top] at hα
    let σ : H₁ ⟶ H := e.homEquiv.symm (e₁.homEquiv (𝟙 H₁))
    have : IsIso σ := (e₁.uniqueUpToIso e).isIso_hom
    have : IsIso σ.left := (Over.forget _).map_isIso σ
    have : IsIso (pullback.fst H₁.hom H₂.hom) := inferInstance
    have hαeq : α = Over.homMk (pullback.fst H₁.hom H₂.hom) ≫ σ := by
      apply e.homEquiv.injective
      apply Subtype.ext
      rw [hα, hilbertPresheaf_homEquiv_comp_val, Equiv.apply_symm_apply,
        ← hilbertPresheaf_homEquiv_comp_val, Category.comp_id]
    subst hαeq
    simp only [Over.comp_left, Over.homMk_left]
    refine ⟨inferInstance, inferInstance, inferInstance, fun t ↦ ?_⟩
    rw [Scheme.Hom.finrank_eq_one_of_isIso]
    simp
  | succ d₂ ih =>
    obtain ⟨H₂₀, ⟨e₂₀⟩⟩ := isRepresentable_hilbertPresheaf_curve f d₂
    obtain ⟨H₁₂, ⟨e₁₂⟩⟩ := isRepresentable_hilbertPresheaf_curve f (d₁ + d₂)
    -- the addition morphism `α₀ : H₁ ×[k] H₂₀ ⟶ H₁₂` in degrees `d₁` and `d₂`
    let P₀ : Over (Spec (.of k)) := Over.mk (pullback.fst H₁.hom H₂₀.hom ≫ H₁.hom)
    let q₁ : P₀ ⟶ H₁ := Over.homMk (pullback.fst H₁.hom H₂₀.hom)
    let q₂ : P₀ ⟶ H₂₀ := Over.homMk (pullback.snd H₁.hom H₂₀.hom) pullback.condition.symm
    let α₀ : P₀ ⟶ H₁₂ :=
      e₁₂.homEquiv.symm ⟨_, (e₁.homEquiv q₁).2.mul f (e₂₀.homEquiv q₂).2⟩
    have hα₀ : (e₁₂.homEquiv α₀).1 = (e₁.homEquiv q₁).1 * (e₂₀.homEquiv q₂).1 :=
      congrArg Subtype.val (e₁₂.homEquiv.apply_symm_apply _)
    obtain ⟨hfin₀, hflat₀, hlfp₀, hrank₀⟩ := ih H₂₀ H₁₂ e₂₀ e₁₂ α₀ hα₀
    -- the addition morphisms `a : H₂₀ ×[k] X ⟶ H₂` and `b : H₁₂ ×[k] X ⟶ H`
    obtain ⟨a, ha, hafin, haflat, halfp, harank, haeq⟩ :=
      exists_addition_hilbertPresheaf f d₂ H₂₀ H₂ e₂₀ e₂
    obtain ⟨b, hb, hbfin, hbflat, hblfp, hbrank, hbeq⟩ :=
      exists_addition_hilbertPresheaf f (d₁ + d₂) H₁₂ H e₁₂ e
    -- `Q = H₁ ×[k] (H₂₀ ×[k] X)`, and the two ways to `H`
    let Q := pullback H₁.hom (pullback.fst H₂₀.hom f ≫ H₂₀.hom)
    let πA : Q ⟶ H₁.left := pullback.fst _ _
    let πBC : Q ⟶ pullback H₂₀.hom f := pullback.snd _ _
    have hQ : πA ≫ H₁.hom = πBC ≫ pullback.fst H₂₀.hom f ≫ H₂₀.hom := pullback.condition
    let r : Q ⟶ P₀.left := pullback.lift πA (πBC ≫ pullback.fst H₂₀.hom f) (by simp [hQ])
    let x : Q ⟶ X := πBC ≫ pullback.snd H₂₀.hom f
    have hx : x ≫ f = πA ≫ H₁.hom := by simp [x, hQ, pullback.condition]
    let v : Q ⟶ pullback H₁.hom H₂.hom := pullback.lift πA (πBC ≫ a)
      (by rw [Category.assoc, ha, hQ, pullback.condition])
    let m : Q ⟶ pullback H₁₂.hom f := pullback.lift (r ≫ α₀.left) x
      (by
        rw [Category.assoc, Over.w α₀, hx]
        exact pullback.lift_fst_assoc _ _ _ _)
    have hr₁ : r ≫ pullback.fst H₁.hom H₂₀.hom = πA := pullback.lift_fst _ _ _
    have hr₂ : r ≫ pullback.snd H₁.hom H₂₀.hom = πBC ≫ pullback.fst H₂₀.hom f :=
      pullback.lift_snd _ _ _
    have hv₁ : v ≫ pullback.fst H₁.hom H₂.hom = πA := pullback.lift_fst _ _ _
    have hv₂ : v ≫ pullback.snd H₁.hom H₂.hom = πBC ≫ a := pullback.lift_snd _ _ _
    -- `v` is a base change of `a`, and `m` is a base change of `α₀`
    have pbv : IsPullback πBC v a (pullback.snd H₁.hom H₂.hom) := by
      refine IsPullback.of_bot ?_ hv₂.symm (IsPullback.of_hasPullback H₁.hom H₂.hom).flip
      have e₁' : a ≫ H₂.hom = pullback.fst H₂₀.hom f ≫ H₂₀.hom := by
        rw [ha, pullback.condition]
      rw [hv₁, e₁']
      exact (IsPullback.of_hasPullback _ _).flip
    have pbm : IsPullback r m α₀.left (pullback.fst H₁₂.hom f) := by
      refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
        (IsPullback.of_hasPullback H₁₂.hom f)
      have L : IsPullback r πBC (pullback.snd H₁.hom H₂₀.hom) (pullback.fst H₂₀.hom f) := by
        refine IsPullback.of_right ?_ hr₂ (IsPullback.of_hasPullback H₁.hom H₂₀.hom)
        rw [hr₁]
        exact IsPullback.of_hasPullback _ _
      have L' := L.paste_vert (IsPullback.of_hasPullback H₂₀.hom f)
      rw [← pullback.condition] at L'
      rw [pullback.lift_snd, Over.w α₀]
      exact L'
    -- the square `v ≫ α = m ≫ b`, by associativity of the sum of divisors
    let TQ : Over (Spec (.of k)) := Over.mk (πA ≫ H₁.hom)
    let V : TQ ⟶ Over.mk (pullback.fst H₁.hom H₂.hom ≫ H₁.hom) :=
      Over.homMk v (by simp [TQ, reassoc_of% hv₁])
    let R : TQ ⟶ P₀ := Over.homMk r (by simp [TQ, P₀, reassoc_of% hr₁])
    let z₀ : TQ ⟶ H₂₀ := Over.homMk (πBC ≫ pullback.fst H₂₀.hom f) (by simp [TQ, hQ])
    let ta : TQ ⟶ H₂ := Over.homMk (πBC ≫ a) (by
      rw [Category.assoc, ha]
      exact hx)
    let tb : TQ ⟶ H := Over.homMk (m ≫ b) (by
      rw [Category.assoc, hb, pullback.lift_snd_assoc]
      exact hx)
    have hlift : pullback.lift z₀.left x (by simp [z₀, x, pullback.condition]) = πBC :=
      pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    have hta := haeq TQ z₀ x hx ta (by simp [ta, hlift])
    have htb := hbeq TQ (R ≫ α₀) x hx tb rfl
    have hVα : V ≫ α = tb := by
      apply e.homEquiv.injective
      apply Subtype.ext
      have hV₂ : V ≫ Over.homMk (pullback.snd H₁.hom H₂.hom) pullback.condition.symm = ta := by
        ext1
        exact hv₂
      have hV₁ : V ≫ Over.homMk (pullback.fst H₁.hom H₂.hom) = R ≫ q₁ := by
        ext1
        simp [V, R, q₁, hv₁, hr₁]
      have hR₂ : R ≫ q₂ = z₀ := by
        ext1
        exact hr₂
      refine Eq.trans ?_ htb.symm
      rw [hilbertPresheaf_homEquiv_comp_val, hilbertPresheaf_homEquiv_comp_val, hα, hα₀,
        Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_mul,
        ← hilbertPresheaf_homEquiv_comp_val, ← hilbertPresheaf_homEquiv_comp_val,
        ← hilbertPresheaf_homEquiv_comp_val, ← hilbertPresheaf_homEquiv_comp_val, hV₁, hV₂,
        hR₂, hta, mul_assoc]
    have sq : v ≫ α.left = m ≫ b := congrArg CommaMorphism.left hVα
    -- properties of `v` and `m`
    have : IsFinite v := MorphismProperty.of_isPullback (P := @IsFinite) pbv hafin
    have : Flat v := MorphismProperty.of_isPullback (P := @Flat) pbv haflat
    have : LocallyOfFinitePresentation v :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) pbv halfp
    have hvrank (y : _) : v.finrank y = d₂ + 1 := by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ pbv, harank]
    have : Surjective v := (Scheme.Hom.one_le_finrank_iff_surjective v).mp fun y ↦ by
      simp [hvrank y]
    have : IsFinite m := MorphismProperty.of_isPullback (P := @IsFinite) pbm hfin₀
    have : Flat m := MorphismProperty.of_isPullback (P := @Flat) pbm hflat₀
    have : LocallyOfFinitePresentation m :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) pbm hlfp₀
    have hmrank (y : _) : m.finrank y = (d₁ + d₂).choose d₁ := by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ pbm, hrank₀]
    -- `α` is proper and quasi-finite, hence finite
    have := isProper_of_representableBy_hilbertPresheaf_curve f _ H₁ e₁
    have := isProper_of_representableBy_hilbertPresheaf_curve f _ H₂ e₂
    have := isProper_of_representableBy_hilbertPresheaf_curve f _ H e
    have := isSeparated_of_representableBy_hilbertPresheaf f e
    have : IsProper (α.left ≫ H.hom) := by
      rw [Over.w α]
      exact inferInstanceAs (IsProper (pullback.fst H₁.hom H₂.hom ≫ H₁.hom))
    have : IsProper α.left := IsProper.of_comp α.left H.hom
    have : LocallyQuasiFinite α.left := by
      refine .of_finite_preimage_singleton _ fun y ↦ ?_
      refine (((m ≫ b).finite_preimage_singleton y).image v).subset fun p hp ↦ ?_
      obtain ⟨q, rfl⟩ := v.surjective p
      refine ⟨q, ?_, rfl⟩
      rwa [Set.mem_preimage, ← sq, Scheme.Hom.comp_apply]
    have : IsFinite α.left := .of_isProper_of_locallyQuasiFinite _
    have : Flat (v ≫ α.left) := by
      rw [sq]
      infer_instance
    have : Flat α.left := Flat.of_comp_of_flat_of_surjective v α.left
    have : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
    refine ⟨inferInstance, inferInstance, inferInstance, fun t ↦ ?_⟩
    have h₁ := Scheme.Hom.finrank_comp_of_forall_finrank_eq v α.left hvrank t
    rw [sq, Scheme.Hom.finrank_comp_of_forall_finrank_eq m b hmrank t, hbrank] at h₁
    have h₂ := Nat.choose_mul_succ_eq (d₁ + d₂) d₁
    have h₃ : d₁ + d₂ + 1 - d₁ = d₂ + 1 := by omega
    rw [h₃] at h₂
    refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos d₂) ?_
    rw [← add_assoc]
    linarith

/-- **The addition morphism of the Hilbert schemes of a curve.** If `H₁`, `H₂` and `H`
represent `Hilb^{d₁}_{X/k}`, `Hilb^{d₂}_{X/k}` and `Hilb^{d₁ + d₂}_{X/k}`, then there is a
`k`-morphism `H₁ ×[k] H₂ ⟶ H`, which on points is addition of effective Cartier divisors —
i.e. the product of the corresponding ideal sheaves — and which is finite, flat and locally of
finite presentation of degree `(d₁ + d₂).choose d₁`.

The last clause is what identifies `α`: without it any finite flat morphism of the right degree
would do, and the descent argument of the blueprint needs to know which morphism it is.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, part (3)) -/
theorem hilbertPresheaf_curve_add [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d₁ d₂ : ℕ) (H₁ H₂ H : Over (Spec (.of k)))
    (e₁ : (hilbertPresheaf f d₁).RepresentableBy H₁)
    (e₂ : (hilbertPresheaf f d₂).RepresentableBy H₂)
    (e : (hilbertPresheaf f (d₁ + d₂)).RepresentableBy H) :
    ∃ α : Limits.pullback H₁.hom H₂.hom ⟶ H.left,
      α ≫ H.hom = Limits.pullback.fst H₁.hom H₂.hom ≫ H₁.hom ∧
        IsFinite α ∧ Flat α ∧ LocallyOfFinitePresentation α ∧
          (∀ t, α.finrank t = (d₁ + d₂).choose d₁) ∧
          ∀ (T : Over (Spec (.of k))) (t₁ : T ⟶ H₁) (t₂ : T ⟶ H₂) (t : T ⟶ H),
            t.left = Limits.pullback.lift t₁.left t₂.left
                (by rw [Over.w, Over.w]) ≫ α →
              (e.homEquiv t).1 = (e₁.homEquiv t₁).1 * (e₂.homEquiv t₂).1 := by
  let P : Over (Spec (.of k)) := Over.mk (pullback.fst H₁.hom H₂.hom ≫ H₁.hom)
  let p₁ : P ⟶ H₁ := Over.homMk (pullback.fst H₁.hom H₂.hom)
  let p₂ : P ⟶ H₂ := Over.homMk (pullback.snd H₁.hom H₂.hom) pullback.condition.symm
  let u : (hilbertPresheaf f (d₁ + d₂)).obj (op P) :=
    ⟨(e₁.homEquiv p₁).1 * (e₂.homEquiv p₂).1, (e₁.homEquiv p₁).2.mul f (e₂.homEquiv p₂).2⟩
  let α := e.homEquiv.symm u
  have hα : (e.homEquiv α).1 = (e₁.homEquiv p₁).1 * (e₂.homEquiv p₂).1 := by
    simp [α, u]
  obtain ⟨hfin, hflat, hlfp, hrank⟩ :=
    isFinite_flat_finrank_of_hilbertPresheaf_add f d₁ d₂ H₁ H₂ H e₁ e₂ e α hα
  refine ⟨α.left, Over.w α, hfin, hflat, hlfp, hrank, fun T t₁ t₂ t ht ↦ ?_⟩
  let s : T ⟶ P := Over.homMk (pullback.lift t₁.left t₂.left (by rw [Over.w, Over.w]))
    (by simp [P])
  obtain rfl : t = s ≫ α := by
    ext1
    exact ht
  have h₁ : t₁ = s ≫ p₁ := by
    ext1
    simp [s, p₁]
  have h₂ : t₂ = s ≫ p₂ := by
    ext1
    simp [s, p₂]
  rw [hilbertPresheaf_homEquiv_comp_val, hα, Scheme.IdealSheafData.comap_mul, h₁, h₂,
    hilbertPresheaf_homEquiv_comp_val, hilbertPresheaf_homEquiv_comp_val]

end Curve

end AlgebraicGeometry
