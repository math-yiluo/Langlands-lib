/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.RingTheory.OpenFlatLocus

/-! Forward flatness comparison for a polynomial chart.

Source: Stacks Project, Tag 00RH, application of Tag 00R7.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-forward)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem isOpen_flat_stalks_spec
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    [LocallyOfFinitePresentation (Spec.map f)] :
    IsOpen {z : Spec S | ((Spec.map f).stalkMap z).hom.Flat} := by
  have hf : f.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance
  algebraize [f.hom]
  have : Algebra.FinitePresentation R S := hf
  have heq (z : PrimeSpectrum S) :
      ((Spec.map f).stalkMap z).hom.Flat ↔ Module.Flat R (Localization.AtPrime z.asIdeal) := by
    rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso f z)]
    algebraize [Localization.localRingHom (z.comap f.hom).asIdeal z.asIdeal f.hom rfl]
    have : IsScalarTower R (Localization.AtPrime (z.comap f.hom).asIdeal)
        (Localization.AtPrime z.asIdeal) :=
      .of_algebraMap_eq fun r ↦ (Localization.localRingHom_to_map _ _ _ rfl r).symm
    change Module.Flat (Localization.AtPrime (z.comap f.hom).asIdeal)
      (Localization.AtPrime z.asIdeal) ↔ _
    exact Module.flat_iff_of_isLocalization
      (Localization.AtPrime (z.comap f.hom).asIdeal) (z.comap f.hom).asIdeal.primeCompl
      (Localization.AtPrime z.asIdeal)
  have hflat (z : PrimeSpectrum S) :
      Module.Flat R (Localization.AtPrime z.asIdeal) ↔
        Module.Flat R (LocalizedModule z.asIdeal.primeCompl S) := by
    let e := (IsLocalizedModule.iso z.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime z.asIdeal))).restrictScalars R
    exact ⟨fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e, fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e.symm⟩
  change IsOpen {z : PrimeSpectrum S | ((Spec.map f).stalkMap z).hom.Flat}
  simpa only [heq, hflat] using
    (Module.isOpen_setOf_flat_localizedModule (R := R) (S := S) (M := S))

private theorem isOpen_flat_stalks_affine
    {E L : Scheme.{u}} (p : E ⟶ L) [IsAffine E] [IsAffine L]
    [LocallyOfFinitePresentation p] :
    IsOpen {z : E | (p.stalkMap z).hom.Flat} := by
  let p' := E.isoSpec.inv ≫ p ≫ L.isoSpec.hom
  have h' : IsOpen {z : Spec Γ(E, ⊤) | (p'.stalkMap z).hom.Flat} := by
    have : LocallyOfFinitePresentation (Spec.map (Spec.preimage p')) := by
      rw [Spec.map_preimage]
      dsimp [p']
      infer_instance
    rw [← Spec.map_preimage p']
    exact isOpen_flat_stalks_spec _
  convert h'.preimage E.isoSpec.hom.continuous using 1
  ext z
  change (p.stalkMap z).hom.Flat ↔
    ((E.isoSpec.inv ≫ p ≫ L.isoSpec.hom).stalkMap (E.isoSpec.hom z)).hom.Flat
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_left_isIso]
  have he : E.isoSpec.inv (E.isoSpec.hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [he]

private theorem flat_pullback_stalk
    {E L B : Scheme.{u}} (g : E ⟶ L) (h : B ⟶ L)
    [IsAffine E] [IsAffine L] [LocallyOfFinitePresentation g]
    (z : ↑(CategoryTheory.Limits.pullback g h))
    (hz : (g.stalkMap (CategoryTheory.Limits.pullback.fst g h z)).hom.Flat) :
    ((CategoryTheory.Limits.pullback.snd g h).stalkMap z).hom.Flat := by
  let V : E.Opens := ⟨{x | (g.stalkMap x).hom.Flat}, isOpen_flat_stalks_affine g⟩
  have hV : Flat (V.ι ≫ g) := by
    apply Flat.of_stalkMap
    intro v
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
    exact v.property
  have hzV : z ∈ Set.range
      (CategoryTheory.Limits.pullback.snd V.ι (CategoryTheory.Limits.pullback.fst g h)) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨⟨CategoryTheory.Limits.pullback.fst g h z, hz⟩, rfl⟩
  obtain ⟨w, rfl⟩ := hzV
  have hcomp : Flat (CategoryTheory.Limits.pullback.snd V.ι
      (CategoryTheory.Limits.pullback.fst g h) ≫ CategoryTheory.Limits.pullback.snd g h) := by
    rw [← CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd g h V.ι]
    infer_instance
  have hw := Flat.stalkMap
    (CategoryTheory.Limits.pullback.snd V.ι (CategoryTheory.Limits.pullback.fst g h) ≫
      CategoryTheory.Limits.pullback.snd g h) w
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso] at hw
  exact hw

/-- Flatness of the chart stalk map descends to the canonical closed-fibre map.

The proof uses the local tower of stalk rings, base change to the residue field,
and localization. The canonical fibre stalk identification transports flatness.
Source: Stacks Project, Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-forward) -/
theorem polynomial_chart_stalk_flat_comparison_forward
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (e.stalkMap x).hom.Flat → (PolynomialChart.stalkMap f U n e he x).Flat := by
  intro hx
  let p := f (U.ι x)
  let a := (CategoryTheory.Limits.pullback.congrHom
    (g₁ := T.fromSpecResidueField p) he.symm rfl).hom
  let b := (CategoryTheory.Limits.pullbackRightPullbackFstIso
    (AffineSpace (ULift.{u} (Fin n)) T ↘ T) (T.fromSpecResidueField p) e).inv
  let y := PolynomialChart.fibrePoint f U x
  have hz : CategoryTheory.Limits.pullback.fst e
      ((AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiberι p) (b (a y)) = x := by
    change (b ≫ CategoryTheory.Limits.pullback.fst e
      (CategoryTheory.Limits.pullback.fst _ _)) (a y) = x
    dsimp only [b]
    rw [CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst]
    change (a ≫ CategoryTheory.Limits.pullback.fst _ _) y = x
    simp only [CategoryTheory.Limits.pullback.congrHom_hom,
      CategoryTheory.Limits.limit.lift_π, CategoryTheory.Limits.PullbackCone.mk_π_app,
      Category.comp_id, a]
    exact (U.ι ≫ f).fiberι_fiberHomeo_symm _ _
  have hmap : ((PolynomialChart.fibreMap f U n e he p).stalkMap y).hom.Flat := by
    have h := flat_pullback_stalk e
      ((AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiberι p) (b (a y)) (by rwa [hz])
    change ((a ≫ b ≫ CategoryTheory.Limits.pullback.snd e
      ((AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiberι p)).stalkMap y).hom.Flat
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
    exact h
  have hcast := RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (eqToHom (congrArg (f.fiber p).presheaf.stalk
      (PolynomialChart.fibreInclusion_asFiber f U x))))
  have hinv := RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (inv ((PolynomialChart.fibreInclusion f U p).stalkMap y)))
  exact (hmap.comp hinv).comp hcast

end AlgebraicGeometry
