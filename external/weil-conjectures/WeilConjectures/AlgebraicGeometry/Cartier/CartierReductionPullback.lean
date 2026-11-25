/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
import WeilConjectures.AlgebraicGeometry.Cartier.CartierClosedExchangeComparison
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryPullback
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Naturality of the normalized Cartier reduction

Source: blueprint main-20261015, sk-lem-geo-cartier.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mapExactFunctor

private theorem exact_functor_square
    {C D E F : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [Category E] [Abelian E] [Category F] [Abelian F]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D] [HasExt.{u + 1} E] [HasExt.{u + 1} F]
    [EnoughInjectives C]
    (V : C ⥤ E) (U : E ⥤ F) (H : C ⥤ D) (W : D ⥤ F)
    [V.Additive] [U.Additive] [H.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (s : V ⋙ U ≅ H ⋙ W) {X Y : C} (κ : Ext X Y 2) :
    (Ext.mk₀ (s.hom.app X)).comp
        ((κ.mapExactFunctor H).mapExactFunctor W) (zero_add 2) =
      ((κ.mapExactFunctor V).mapExactFunctor U).comp
        (Ext.mk₀ (s.hom.app Y)) (add_zero 2) := by
  have h₁ := Ext.mapExactFunctor_mapExactFunctor_of_iso V U (V ⋙ U) (Iso.refl _) κ
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    Ext.mk₀_id_comp, Ext.comp_mk₀_id] at h₁
  have h₂ := Ext.mapExactFunctor_mapExactFunctor_of_iso H W (V ⋙ U) s κ
  rw [h₂, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app, Ext.mk₀_id_comp, h₁]

private theorem transport_ext_square
    {C D E F : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [Category E] [Abelian E] [Category F] [Abelian F]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D] [HasExt.{u + 1} E] [HasExt.{u + 1} F]
    [EnoughInjectives C]
    (V : C ⥤ E) (U : E ⥤ F) (H : C ⥤ D) (W : D ⥤ F)
    [V.Additive] [U.Additive] [H.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (s : V ⋙ U ≅ H ⋙ W) {X Y : C} {X' Y' : D} {P : E} {Q : F}
    (a : V.obj X ≅ P) (b : W.obj X' ≅ Q)
    (e : H.obj X ⟶ X') (l : H.obj Y ⟶ Y') (χ : U.obj P ⟶ Q)
    (hχ : U.map a.hom ≫ χ = s.hom.app X ≫ W.map e ≫ b.hom)
    (κ : Ext X Y 2) (κ' : Ext X' Y' 2)
    (hκ : (Ext.mk₀ e).comp κ' (zero_add 2) =
      (κ.mapExactFunctor H).comp (Ext.mk₀ l) (add_zero 2)) :
    (Ext.mk₀ χ).comp
        ((Ext.mk₀ b.inv).comp (κ'.mapExactFunctor W) (zero_add 2)) (zero_add 2) =
      (((Ext.mk₀ a.inv).comp (κ.mapExactFunctor V) (zero_add 2)).mapExactFunctor U).comp
        (Ext.mk₀ (s.hom.app Y ≫ W.map l)) (add_zero 2) := by
  have h := congrArg
    (fun z : Ext (H.obj X) Y' 2 ↦
      (Ext.mk₀ (s.hom.app X)).comp (z.mapExactFunctor W) (zero_add 2)) hκ
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at h
  rw [← Ext.comp_assoc_of_third_deg_zero,
    exact_functor_square V U H W s κ, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀] at h
  simp only [Ext.mk₀_comp_mk₀_assoc] at h
  have h' := congrArg
    (fun z : Ext (U.obj (V.obj X)) (W.obj Y') 2 ↦
      (Ext.mk₀ (U.map a.inv)).comp z (zero_add 2)) h
  have hχ' : U.map a.inv ≫ s.hom.app X ≫ W.map e = χ ≫ b.inv := by
    have hh := congrArg (fun f ↦ U.map a.inv ≫ f ≫ b.inv) hχ
    simp only [← Category.assoc, ← Functor.map_comp, a.inv_hom_id] at hh
    rw [U.map_id P, Category.id_comp] at hh
    simpa only [Category.assoc, b.hom_inv_id, Category.comp_id] using hh.symm
  simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, hχ'] using h'

namespace AlgebraicGeometry.ProEtale

/-- Pullback of the integral pole extension commutes with its normalized reduction
when the inverse-image divisor is Cartier.
Source: blueprint sk-lem-geo-cartier.proof.md, paragraph 6 and opening comparison
paragraph (blueprint: lemma-cycle-class-cartier-divisor--2).
Proof: choose regular equations t for D. Their pullbacks are regular because the
inverse-image ideal is again Cartier. Sending u times t inverse to the pullback unit
and pulled-back inverse equation gives a map of pole extensions, independent of the
chosen equations. The finite-stalk formula makes closed exchange an isomorphism:
it is the identity on the constant stalk on D and the unique map between zero stalks
off D. Exact inverse image and naturality of the short exact triangle commute with
the extension boundary and its Kummer reduction. Flatness of the roots line and
tensor compatibility commute this equality with extension to A. Use the one fixed
roots-normalized finite-line transport for all schemes. Finally the comparison square
respects counits. Adjunction injectivity identifies its exchange with geoCartierExchange,
whose adjunct is inverse-image commutation followed by the pulled-back counit.
The resulting equality is an equality of derived morphisms by functoriality; stalks
were used only to identify the ordinary source exchange. Empty support and identity
base change give the zero and identity squares respectively. -/
theorem geoCartierCanonicalClass_pullback (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) :
    ∃ t : Etale.OrdinaryFiniteTwistTransport A n hA,
      ∀ {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
        [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (gD : D' ⟶ D)
        (sq : IsPullback gD i' i g) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
        (hZ : IsUnit (n : Γ(Z, ⊤))) (hZ' : IsUnit (n : Γ(Z', ⊤))),
        IsIso (geoCartierExchange A i i' g gD sq.toCommSq) ∧
        (Ext.mk₀ (geoCartierExchange A i i' g gD sq.toCommSq)).comp
            (geoCartierCanonicalClass A n hn hA i' hI' hZ') (zero_add 2) =
          ((geoCartierCanonicalClass A n hn hA i hI hZ).mapExactFunctor
            (upperStar (ModuleCat.{u + 1} A) g)).comp
            (Ext.mk₀ (geoCartierLinePullback A n hA t g hZ).hom) (add_zero 2) := by
  obtain ⟨r, c, p, hcover, hr, hc, hrest⟩ :=
    Scheme.etaleFiniteTwistPullback A n hn hA
  let t : Etale.OrdinaryFiniteTwistTransport A n hA :=
    { roots := r
      line := fun f hY ↦ c f hY (by simpa using hY.map f.appTop.hom) 1
      roots_normalization := hr
      line_normalization := fun f hY ↦
        hc f hY (by simpa using hY.map f.appTop.hom) }
  refine ⟨t, ?_⟩
  intro D D' Z Z' i i' _ _ g gD sq hI hI' hZ hZ'
  have he : IsIso (Etale.supportedConstantExchange A i i' g gD sq.toCommSq) := by
    let := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
    unfold Etale.supportedConstantExchange
    infer_instance
  have hx := geoCartier_closed_exchange_comparison A i i' g gD sq.toCommSq
  refine ⟨?_, ?_⟩
  · have : IsIso ((upperStar (ModuleCat.{u + 1} A) g).map
        (geoCartierSourceComparison A i) ≫ geoCartierExchange A i i' g gD sq.toCommSq) := by
      rw [hx]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((upperStar (ModuleCat.{u + 1} A) g).map (geoCartierSourceComparison A i)) _
  · have hκ := Etale.supported_kummer_boundary_pullback Z n hn A hA hZ i hI
      (Etale.geoCartierEtaleClass A n hn hA i hI hZ)
      (Etale.geoCartierEtaleClass_spec A n hn hA i hI hZ).1 t i' g gD sq hI'
      (Etale.geoCartierEtaleClass A n hn hA i' hI' hZ')
      (Etale.geoCartierEtaleClass_spec A n hn hA i' hI' hZ').1
    unfold geoCartierCanonicalClass geoCartierLinePullback
    exact transport_ext_square
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
      (upperStar (ModuleCat.{u + 1} A) g)
      (Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z')
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g)
      (asIso (geoCartierSourceComparison A i))
      (asIso (geoCartierSourceComparison A i'))
      (Etale.supportedConstantExchange A i i' g gD sq.toCommSq)
      (t.line g hZ).hom (geoCartierExchange A i i' g gD sq.toCommSq) hx _ _ hκ

end AlgebraicGeometry.ProEtale
