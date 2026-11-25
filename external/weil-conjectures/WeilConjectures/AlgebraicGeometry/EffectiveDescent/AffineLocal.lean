/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Affine
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant

/-!
# Effectivity on invariant affine opens over affine opens of the base

Let `p : X ⟶ Y` be affine, flat and surjective and let `D` be a descent datum on `V` over `X`
relative to `p`. If `U ⊆ V` is an invariant affine open subscheme lying over an affine open
`W ⊆ Y`, then the restriction of `D` to `U` is effective
(`CategoryTheory.Over.DescentDatum.isEffective_restrict_of_isAffineOpen`): it is a descent datum
relative to the morphism of affine schemes `p⁻¹ W ⟶ W`, which is effective by affine
faithfully flat descent.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}

section Localize

variable {W : Y.Opens} {U : V.left.Opens}

lemma range_ι_comp_hom_subset (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W) :
    Set.range (U.ι ≫ V.hom) ⊆ Set.range (p ⁻¹ᵁ W).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨u, rfl⟩
  exact hUW u.2

/-- The structure morphism of `U ⊆ V`, lifted to `p⁻¹ W`. -/
noncomputable def homToPreimage (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W) :
    U.toScheme ⟶ (p ⁻¹ᵁ W).toScheme :=
  IsOpenImmersion.lift (p ⁻¹ᵁ W).ι (U.ι ≫ V.hom) (range_ι_comp_hom_subset hUW)

@[reassoc (attr := simp)]
lemma homToPreimage_ι (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W) :
    homToPreimage hUW ≫ (p ⁻¹ᵁ W).ι = U.ι ≫ V.hom :=
  IsOpenImmersion.lift_fac _ _ _

lemma comp_ι_comp_eq {T : Scheme.{u}} {f₁ f₂ : T ⟶ (p ⁻¹ᵁ W).toScheme}
    (h : f₁ ≫ p ∣_ W = f₂ ≫ p ∣_ W) :
    (f₁ ≫ (p ⁻¹ᵁ W).ι) ≫ p = (f₂ ≫ (p ⁻¹ᵁ W).ι) ≫ p := by
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% h]

variable {D : DescentDatum p V} (hU : D.IsInvariant U)

/-- A point of `U` over `f : T ⟶ p⁻¹ W`, as a point of `U` over `T ⟶ X`. -/
noncomputable abbrev pointOfPreimage (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W) {T : Scheme.{u}}
    {f : T ⟶ (p ⁻¹ᵁ W).toScheme} (a : Over.mk f ⟶ Over.mk (homToPreimage hUW)) :
    Over.mk (f ≫ (p ⁻¹ᵁ W).ι) ⟶ Over.mk (U.ι ≫ V.hom) :=
  Over.homMk a.left (by
    have := Over.w_assoc a (p ⁻¹ᵁ W).ι
    simp only [Over.mk_hom, homToPreimage_ι] at this ⊢
    exact this)

/-- The restriction of `D` to `U ⊆ V`, as a descent datum relative to `p⁻¹ W ⟶ W`. -/
noncomputable def restrictBase (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W) :
    DescentDatum (p ∣_ W) (Over.mk (homToPreimage hUW)) where
  transport f₁ f₂ h a := Over.homMk ((D.restrict U hU).transport (f₁ ≫ (p ⁻¹ᵁ W).ι)
      (f₂ ≫ (p ⁻¹ᵁ W).ι) (comp_ι_comp_eq h) (pointOfPreimage hUW a)).left (by
    rw [← cancel_mono (p ⁻¹ᵁ W).ι]
    simp only [Over.mk_hom, Category.assoc, homToPreimage_ι]
    exact Over.w ((D.restrict U hU).transport _ _ _ _))
  transport_homMk_comp g f₁ f₂ h a := by
    refine Over.OverMorphism.ext ?_
    exact (D.restrict U hU).transport_left_eq_comp g _ _ _ _ _ (by simp) (by simp) _ (by simp)
  transport_self f a := by
    refine Over.OverMorphism.ext ?_
    have := congrArg CommaMorphism.left
      ((D.restrict U hU).transport_self (f ≫ (p ⁻¹ᵁ W).ι) (pointOfPreimage hUW a))
    exact this
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ a := by
    refine Over.OverMorphism.ext ?_
    refine ((D.restrict U hU).transport_left_congr' (comp_ι_comp_eq h₂₃) (comp_ι_comp_eq h₂₃)
      rfl rfl ((D.restrict U hU).transport _ _ (comp_ι_comp_eq h₁₂) (pointOfPreimage hUW a)) _
      rfl).trans ?_
    exact congrArg CommaMorphism.left ((D.restrict U hU).transport_transport _ _ _
      (comp_ι_comp_eq h₁₂) (comp_ι_comp_eq h₂₃) (pointOfPreimage hUW a))

end Localize

/-- **Effectivity on invariant affine opens.** Let `p : X ⟶ Y` be affine, flat and surjective,
`W ⊆ Y` an affine open and `U ⊆ V` an invariant affine open lying over `W`. Then the restriction
of a descent datum `D` on `V` to `U` is effective. -/
theorem isEffective_restrict_of_isAffineOpen [IsAffineHom p] [Flat p] [Surjective p]
    (D : DescentDatum p V) {U : V.left.Opens} (hU : D.IsInvariant U) (hUa : IsAffineOpen U)
    {W : Y.Opens} (hW : IsAffineOpen W) (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W) :
    (D.restrict U hU).IsEffective := by
  have : IsAffine W := hW
  have : IsAffine (p ⁻¹ᵁ W) := hW.preimage p
  have : IsAffine (Over.mk (homToPreimage hUW)).left := hUa
  have : Flat (p ∣_ W) := MorphismProperty.of_isPullback (isPullback_morphismRestrict p W).flip
    inferInstance
  have : Surjective (p ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p W).flip inferInstance
  obtain ⟨V₀, q, hq, hinv⟩ := (restrictBase hU hUW).isEffective_of_isAffine
  refine ⟨Over.mk (V₀.hom ≫ W.ι), q, ?_, fun {T} f₁ f₂ h a ↦ ?_⟩
  · simpa using hq.paste_vert (isPullback_morphismRestrict p W)
  · have e : f₁ = a.left ≫ U.ι ≫ V.hom := (Over.w a).symm
    have hr : Set.range f₂ ⊆ Set.range (p ⁻¹ᵁ W).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← h, e]
      exact hUW (a.left t).2
    let f₂' := IsOpenImmersion.lift (p ⁻¹ᵁ W).ι f₂ hr
    have hf₂' : f₂' ≫ (p ⁻¹ᵁ W).ι = f₂ := IsOpenImmersion.lift_fac _ _ _
    have hf₁ : (a.left ≫ homToPreimage hUW) ≫ (p ⁻¹ᵁ W).ι = f₁ := by
      rw [Category.assoc, homToPreimage_ι]
      exact e.symm
    have h' : (a.left ≫ homToPreimage hUW) ≫ p ∣_ W = f₂' ≫ p ∣_ W := by
      rw [← cancel_mono W.ι]
      simp only [Category.assoc, morphismRestrict_ι]
      rw [reassoc_of% hf₁, reassoc_of% hf₂', h]
    have e := (D.restrict U hU).transport_left_congr' h (comp_ι_comp_eq h') hf₁ hf₂' a
      (pointOfPreimage hUW (Over.homMk a.left rfl)) rfl
    rw [← e]
    exact hinv (a.left ≫ homToPreimage hUW) f₂' h' (Over.homMk a.left rfl)

end CategoryTheory.Over.DescentDatum
