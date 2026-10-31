import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Descent of functions along quasi-compact flat surjections -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.UnitCocycleDescent

/-- Global functions that agree along every pair of maps with equal composite descend
along an effective epimorphism. -/
theorem exists_appTop_eq_of_effectiveEpi {X Y : Scheme.{u}} (p : X ⟶ Y) [EffectiveEpi p]
    (s : Γ(X, ⊤))
    (hs : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → a.appTop s = b.appTop s) :
    ∃ t : Γ(Y, ⊤), p.appTop t = s := by
  let e : X ⟶ _ := (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ ↦ s)
  have he : ∀ {U : Scheme.{u}} (a b : U ⟶ X), a ≫ p = b ≫ p → a ≫ e = b ≫ e := by
    intro U a b h
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).injective
    funext i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, AffineSpace.toSpecMvPolyIntEquiv_comp]
    simp only [e, Equiv.apply_symm_apply]
    exact hs U a b h
  refine ⟨AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (EffectiveEpi.desc p e he)
    PUnit.unit, ?_⟩
  rw [← AffineSpace.toSpecMvPolyIntEquiv_comp, EffectiveEpi.fac]
  simp only [e, Equiv.apply_symm_apply]

/-- Pullback of global functions along an epimorphism of schemes is injective. -/
theorem appTop_injective_of_epi {X Y : Scheme.{u}} (p : X ⟶ Y) [Epi p] :
    Function.Injective p.appTop := by
  intro t t' h
  have : (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ ↦ t) =
      (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ ↦ t') := by
    rw [← cancel_epi p]
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).injective
    funext i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, AffineSpace.toSpecMvPolyIntEquiv_comp]
    simp only [Equiv.apply_symm_apply]
    exact h
  simpa using congrFun ((AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm.injective this)
    PUnit.unit

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- `appLE` only depends on the morphism, not on the inclusion proof. -/
lemma appLE_eq_of_eq {U Z : Scheme.{u}} {f g : U ⟶ Z} (h : f = g) (O : Z.Opens) (W : U.Opens)
    (e : W ≤ f ⁻¹ᵁ O) (e' : W ≤ g ⁻¹ᵁ O) : f.appLE O W e = g.appLE O W e' := by
  subst h
  rfl

/-- The pullback of global sections as an `appLE` with both opens the whole scheme. -/
lemma appTop_eq_appLE {U Z : Scheme.{u}} (c : U ⟶ Z) :
    c.appTop = c.appLE ⊤ ⊤ (Scheme.Hom.preimage_top c).ge := by
  change c.app ⊤ = c.app ⊤ ≫ U.presheaf.map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The pullback of sections along `p` over an open `V`, compared with the pullback of global
sections along the restriction `p ∣_ V` through the restriction maps to the open subschemes. -/
lemma app_comp_ι_appLE (V : Y.Opens) :
    p.app V ≫ (p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge =
      V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫ (p ∣_ V).appTop := by
  rw [appTop_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (morphismRestrict_ι p V).symm _ _ _ _

lemma ι_appLE_injective (O : X.Opens) :
    Function.Injective (O.ι.appLE O ⊤ O.ι_preimage_self.ge) :=
  (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).1

/-- A section over an open of `X` is invariant under pairs of maps with equal composite
to `Y` when its pullbacks along the two maps agree over every open where both are defined. -/
def IsPairInvariant (O : X.Opens) (f : Γ(X, O)) : Prop :=
  ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p →
    ∀ (V : U.Opens) (ha : V ≤ a ⁻¹ᵁ O) (hb : V ≤ b ⁻¹ᵁ O), a.appLE O V ha f = b.appLE O V hb f

variable [QuasiCompact p] [Flat p] [Surjective p]

instance (V : Y.Opens) : Surjective (p ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹Surjective p› V

/-- Pullback of sections along a quasi-compact flat surjection is injective over every open. -/
theorem app_injective (V : Y.Opens) : Function.Injective (p.app V) := by
  intro t t' h
  have h' := congrArg ((p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge) h
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, app_comp_ι_appLE,
    CommRingCat.comp_apply, CommRingCat.comp_apply] at h'
  exact ι_appLE_injective V (appTop_injective_of_epi (p ∣_ V) h')

/-- Pair-invariant sections over `p ⁻¹ᵁ V` descend to `V` along a quasi-compact flat
surjection. -/
theorem exists_app_eq_of_isPairInvariant (V : Y.Opens) (f : Γ(X, p ⁻¹ᵁ V))
    (hf : IsPairInvariant p (p ⁻¹ᵁ V) f) : ∃ g : Γ(Y, V), p.app V g = f := by
  set f' := (p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge f
  have hc : ∀ {U : Scheme.{u}} (c : U ⟶ p ⁻¹ᵁ V),
      c.appTop f' = (c ≫ (p ⁻¹ᵁ V).ι).appLE (p ⁻¹ᵁ V) ⊤ (by simp) f := by
    intro U c
    rw [appTop_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hinv : ∀ (U : Scheme.{u}) (a b : U ⟶ p ⁻¹ᵁ V), a ≫ (p ∣_ V) = b ≫ (p ∣_ V) →
      a.appTop f' = b.appTop f' := by
    intro U a b h
    have h' : (a ≫ (p ⁻¹ᵁ V).ι) ≫ p = (b ≫ (p ⁻¹ᵁ V).ι) ≫ p := by
      simp only [Category.assoc, ← morphismRestrict_ι, reassoc_of% h]
    rw [hc, hc]
    exact hf U _ _ h' ⊤ _ _
  obtain ⟨t, ht⟩ := exists_appTop_eq_of_effectiveEpi (p ∣_ V) f' hinv
  obtain ⟨g, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso (C := CommRingCat)
      (V.ι.appLE V ⊤ V.ι_preimage_self.ge)).2 t
  refine ⟨g, ι_appLE_injective (p ⁻¹ᵁ V) ?_⟩
  rw [← CommRingCat.comp_apply, app_comp_ι_appLE, CommRingCat.comp_apply, ht]
