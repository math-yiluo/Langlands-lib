/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericSourceEtale

/-! # Properties of the explicit root-cover normalization

## References

* Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH
* Stacks Project, Tags 09EB, 0BRM and 0EYG, root-extension paragraph
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Finiteness lets source-local etaleness around the whole fibre give a target open.
private theorem etale_shrink_of_fibre_source_opens {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y)
    (h : ∀ x : X, f x = y → ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) :
    ∃ W : Y.Opens, y ∈ W ∧ Etale (f ∣_ W) := by
  classical
  let E : X.Opens := ⨆ V : {V : X.Opens // Etale (V.ι ≫ f)}, V.val
  let W : Y.Opens := ⟨(f '' (E : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ E.isOpen.isClosed_compl).isOpen_compl⟩
  have hy : y ∈ W := by
    rintro ⟨x, hx, hxy⟩
    obtain ⟨V, hxV, hV⟩ := h x hxy
    apply hx
    exact (le_iSup (fun V : {V : X.Opens // Etale (V.ι ≫ f)} ↦ V.val)
      ⟨V, hV⟩) hxV
  have hle : f ⁻¹ᵁ W ≤ E := by
    intro x hx
    by_contra hxE
    exact hx ⟨x, hxE, rfl⟩
  let g := f ∣_ W
  have hlocal (x : (f ⁻¹ᵁ W).toScheme) :
      ∃ V : (f ⁻¹ᵁ W).toScheme.Opens, x ∈ V ∧ Etale (V.ι ≫ g) := by
    have hxE : (f ⁻¹ᵁ W).ι x ∈ E := hle x.property
    obtain ⟨V, hxV⟩ := (TopologicalSpace.Opens.mem_iSup.mp hxE)
    let T := (f ⁻¹ᵁ W).ι ⁻¹ᵁ V.val
    have hT : Etale (T.ι ≫ (f ⁻¹ᵁ W).ι ≫ f) := by
      have hcomp : T.ι ≫ (f ⁻¹ᵁ W).ι ≫ f =
          ((f ⁻¹ᵁ W).ι ∣_ V.val) ≫ V.val.ι ≫ f := by
        simp only [← Category.assoc, morphismRestrict_ι]
        rfl
      rw [hcomp]
      let : Etale (V.val.ι ≫ f) := V.property
      infer_instance
    have hT' : Etale ((T.ι ≫ g) ≫ W.ι) := by
      simpa only [Category.assoc, g, morphismRestrict_ι] using hT
    let := hT'
    exact ⟨T, hxV, AlgebraicGeometry.Etale.of_comp (T.ι ≫ g) W.ι⟩
  choose V hxV hV using hlocal
  have htop : (⨆ x, V x) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  exact ⟨W, hy, IsZariskiLocalAtSource.of_iSup_eq_top V htop hV⟩

/-- Abhyankar's lemma gives an etale neighborhood of the divisor generic point
for the already finite, explicitly constructed relative normalization. -/
theorem GaloisCover.strict_hensel_root_normalization_generic_etale
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g → ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (O : N.Opens), j η ∈ O ∧ Etale (a.fromNormalization ∣_ O) := by
  dsimp only
  intro hg hN hp he hn D j hD hDi hj hV η hη
  have hQ := strictHenselization_regular_divisor_quotient R f barY b hb hg
  have : IsNoetherianRing (strictHenselization barY) := hQ.1
  have : IsRegularRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) := hQ.2.1
  have : IsDomain (strictHenselization barY ⧸ Ideal.span {b.hom f}) := hQ.2.2
  let : Algebra R (strictHenselization barY) := b.hom.toAlgebra
  have : Module.Flat R (strictHenselization barY) :=
    strictHenselization_structural_ringHom_flat R barY b hb
  have hgreg : IsSMulRegular (strictHenselization barY) (b.hom f) := hf.of_flat
  have hG' : IsUnit (Nat.card G : strictHenselization barY) := by
    simpa only [map_natCast] using hG.map b.hom
  have hroot (Q : Ideal (AdjoinRoot
      ((Polynomial.X : Polynomial (strictHenselization barY)) ^ Nat.card G -
        Polynomial.C (b.hom f)))) (hQp : Q.IsPrime) :
      AdjoinRoot.root ((Polynomial.X : Polynomial (strictHenselization barY)) ^
        Nat.card G - Polynomial.C (b.hom f)) ∈ Q →
      IsRegularLocalRing (Localization.AtPrime Q) := by
    have := hQp
    exact AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem
      (strictHenselization barY) (b.hom f) hgreg (Nat.card G)
      (Nat.card_pos) Q
  have := hN
  have := hp
  have := hn
  apply etale_shrink_of_fibre_source_opens _ (j η)
  exact root_normalization_generic_source_etale_point i G W R φ f β hβ
    (strictHenselization barY) b hG' hgreg hroot hN hp he hn D j hD hDi hj hV η hη


end AlgebraicGeometry.Scheme
