/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitSmoothSurface
public import WeilConjectures.AlgebraicGeometry.BlowupChartLimitSmooth
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Base change of a filtered colimit of étale ring maps

Let `D : K ⥤ CommRingCat` be a filtered diagram of rings with étale transition maps and colimit
`R`, let `k₁ : K`, and let `φ : D(k₁) → B` be a ring map such that `Spec B` is smooth of relative
dimension `2` over a field `k`. If `L` is the pushout of `B` and `R` over `D(k₁)`, then `Spec L` is
an étale limit of smooth surfaces over `k`: it is the limit, over the arrows `k₁ → l`, of the
spectra of the pushouts of `B` and `D(l)` over `D(k₁)`, which are étale over `Spec B`
(`AlgebraicGeometry.isEtaleLimitOfSmoothSurfaces_of_isPushout`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Base change of a filtered colimit of étale ring maps is an étale limit of smooth
surfaces.** Let `D : K ⥤ CommRingCat` be a filtered diagram with étale transition maps and
colimit cocone `c`, let `φ : D(k₁) → B` and `κ : k → B` with `Spec B` smooth of relative
dimension `2` over `k`, and let `L` be the pushout of `φ` and the colimit leg `D(k₁) → R`. Then
`Spec L` (over `k` via `κ`) is an étale limit of smooth surfaces. -/
theorem isEtaleLimitOfSmoothSurfaces_of_isPushout {k : Type u} [Field k] {K : Type u}
    [SmallCategory K] [IsFiltered K] {D : K ⥤ CommRingCat.{u}} {c : Cocone D}
    (hc : IsColimit c) (hD : ∀ ⦃i j : K⦄ (f : i ⟶ j), (D.map f).hom.Etale) (k₁ : K)
    {B L : CommRingCat.{u}} (φ : D.obj k₁ ⟶ B) (β : B ⟶ L) (γ : c.pt ⟶ L)
    (hsq : IsPushout φ (c.ι.app k₁) β γ) (κ : CommRingCat.of k ⟶ B)
    [SmoothOfRelativeDimension 2 (Spec.map κ)] :
    IsEtaleLimitOfSmoothSurfaces (Over.mk (Spec.map (κ ≫ β))) := by
  have : IsConnected (Under k₁) := IsFiltered.isConnected _
  -- the diagram `l ↦ B ⊗_{D(k₁)} D(l)` of rings under `B`
  let E' : Under k₁ ⥤ Under B := Under.post D ⋙ Under.pushout φ
  let E : Under k₁ ⥤ CommRingCat.{u} := E' ⋙ Under.forget B
  have hE' : IsColimit ((Under.pushout φ).mapCocone (c.underPost k₁)) :=
    isColimitOfPreserves (Under.pushout φ) (hc.underPost k₁)
  have hE : IsColimit ((Under.forget B).mapCocone ((Under.pushout φ).mapCocone (c.underPost k₁))) :=
    isColimitOfPreserves (Under.forget B) hE'
  -- its colimit is `L`
  let e : ((Under.forget B).mapCocone ((Under.pushout φ).mapCocone (c.underPost k₁))).pt ≅ L :=
    hsq.flip.isoPushout.symm
  let c₂ : Cocone E :=
    ((Under.forget B).mapCocone ((Under.pushout φ).mapCocone (c.underPost k₁))).extend e.hom
  have hc₂ : IsColimit c₂ := IsColimit.extendIso e.hom hE
  have hι (l : Under k₁) : (E'.obj l).hom ≫ c₂.ι.app l = β := by
    have h := Under.w (((Under.pushout φ).mapCocone (c.underPost k₁)).ι.app l)
    change ((E'.obj l).hom ≫ (((Under.pushout φ).mapCocone (c.underPost k₁)).ι.app l).right) ≫
      e.hom = β
    rw [h]
    exact hsq.flip.inr_isoPushout_inv
  -- the spectra, as a diagram over `Spec k`
  let Dk : (Under k₁)ᵒᵖ ⥤ Scheme.{u} := E.op ⋙ Scheme.Spec
  let s : Dk ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) :=
    { app l := Spec.map (κ ≫ (E'.obj l.unop).hom)
      naturality l l' f := by
        dsimp [Dk]
        rw [Category.comp_id, ← Spec.map_comp, Category.assoc]
        congr 2
        exact Under.w (E'.map f.unop) }
  let cS : Cone Dk := Scheme.Spec.mapCone c₂.op
  have hcS : IsLimit cS := isLimitOfPreserves Scheme.Spec hc₂.op
  have hp : ∀ l, cS.π.app l ≫ s.app l = Spec.map (κ ≫ β) := by
    intro l
    dsimp [cS, s]
    rw [← Spec.map_comp, Category.assoc, hι]
  have : Nonempty (Under k₁)ᵒᵖ := ⟨Opposite.op (Under.mk (𝟙 k₁))⟩
  refine ⟨(Under k₁)ᵒᵖ, inferInstance, inferInstance, Over.lift Dk s,
    Over.liftCone Dk s cS (Spec.map (κ ≫ β)) hp, ⟨Over.isLimitLiftCone _ _ _ _ hp hcS⟩,
    ⟨Iso.refl _⟩, fun l ↦ ?_, fun l l' f ↦ ⟨?_, ?_⟩⟩
  · -- each object is étale over `Spec B`, which is smooth over `k`
    have het : (E'.obj l.unop).hom.hom.Etale :=
      etale_of_isPushout (IsPushout.of_hasPushout (D.map l.unop.hom) φ)
        (hD l.unop.hom)
    have : Etale (Spec.map (E'.obj l.unop).hom) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr het
    change SmoothOfRelativeDimension 2 (Spec.map (κ ≫ (E'.obj l.unop).hom))
    rw [Spec.map_comp]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  · change IsAffineHom (Spec.map (E.map f.unop))
    infer_instance
  · change Etale (Spec.map (E.map f.unop))
    have het (l : (Under k₁)ᵒᵖ) : Etale (Spec.map (E'.obj l.unop).hom) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (etale_of_isPushout (IsPushout.of_hasPushout (D.map l.unop.hom) φ)
          (hD l.unop.hom))
    have hw : Spec.map (E.map f.unop) ≫ Spec.map (E'.obj l'.unop).hom =
        Spec.map (E'.obj l.unop).hom := by
      rw [← Spec.map_comp]
      congr 1
      exact Under.w (E'.map f.unop)
    have : Etale (Spec.map (E.map f.unop) ≫ Spec.map (E'.obj l'.unop).hom) := by
      rw [hw]
      exact het l
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _
      (Spec.map (E'.obj l'.unop).hom)
      (het l') this

/-- **Localized charts of blow-ups over a filtered colimit of étale ring maps.** Let
`D : K ⥤ CommRingCat` be a filtered diagram with étale transition maps and colimit `R`, a
`k`-algebra, and let `g : k[X₀, X₁] → D(k₁)` be étale and compatible with the `k`-algebra
structure of `R`. Then for `x = g(X₀)`, `y = g(X₁)` with images `x', y'` in `R`, and every `u`
in the chart `R[T]/(x'T - y')` coming from the chart over `D(k₁)`, the `k`-scheme
`Spec (R[T]/(x'T - y'))[1/u]` is an étale limit of smooth surfaces. -/
theorem isEtaleLimitOfSmoothSurfaces_blowupChart_away_of_isColimit {k : Type u} [Field k]
    {K : Type u} [SmallCategory K] [IsFiltered K] {D : K ⥤ CommRingCat.{u}} {c : Cocone D}
    (hc : IsColimit c) (hD : ∀ ⦃i j : K⦄ (f : i ⟶ j), (D.map f).hom.Etale) [Algebra k c.pt]
    (k₁ : K) (g : CommRingCat.of (MvPolynomial (Fin 2) k) ⟶ D.obj k₁) (hg : g.hom.Etale)
    (hk : ∀ r : k, (c.ι.app k₁).hom (g.hom (MvPolynomial.C r)) = algebraMap k c.pt r)
    {x' y' : c.pt} (hx : (c.ι.app k₁).hom (g.hom (MvPolynomial.X 0)) = x')
    (hy : (c.ι.app k₁).hom (g.hom (MvPolynomial.X 1)) = y')
    (uA : blowupChart (g.hom (MvPolynomial.X 0)) (g.hom (MvPolynomial.X 1))) :
    IsEtaleLimitOfSmoothSurfaces (Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k
        (Localization.Away (blowupChartMap (A' := c.pt) (c.ι.app k₁).hom hx hy uA)))))) := by
  have hsq := isPushout_blowupChart_away (R := c.pt) (c.ι.app k₁) hx hy uA
  have : SmoothOfRelativeDimension 2 (Spec.map (CommRingCat.ofHom (g.hom.comp MvPolynomial.C) ≫
      CommRingCat.ofHom ((algebraMap (blowupChart (g.hom (MvPolynomial.X 0))
        (g.hom (MvPolynomial.X 1))) (Localization.Away uA)).comp
          (algebraMap (D.obj k₁) _)))) := by
    rw [← CommRingCat.ofHom_comp]
    exact smoothOfRelativeDimension_blowupChart_away g hg rfl rfl uA
  have H := isEtaleLimitOfSmoothSurfaces_of_isPushout hc hD k₁ _ _ _ hsq
    (CommRingCat.ofHom (g.hom.comp MvPolynomial.C) ≫
      CommRingCat.ofHom ((algebraMap (blowupChart (g.hom (MvPolynomial.X 0))
        (g.hom (MvPolynomial.X 1))) (Localization.Away uA)).comp
          (algebraMap (D.obj k₁) _)))
  rw [Category.assoc, hsq.w] at H
  have heq : CommRingCat.ofHom (g.hom.comp MvPolynomial.C) ≫ c.ι.app k₁ ≫
      CommRingCat.ofHom ((algebraMap (blowupChart x' y')
        (Localization.Away (blowupChartMap (A' := c.pt) (c.ι.app k₁).hom hx hy uA))).comp
          (algebraMap c.pt (blowupChart x' y'))) =
      CommRingCat.ofHom (algebraMap k
        (Localization.Away (blowupChartMap (A' := c.pt) (c.ι.app k₁).hom hx hy uA))) := by
    ext r
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [hk, IsScalarTower.algebraMap_apply k (blowupChart x' y') (Localization.Away _) r,
      IsScalarTower.algebraMap_apply k c.pt (blowupChart x' y') r]
    rfl
  rw [heq] at H
  exact H

end AlgebraicGeometry
