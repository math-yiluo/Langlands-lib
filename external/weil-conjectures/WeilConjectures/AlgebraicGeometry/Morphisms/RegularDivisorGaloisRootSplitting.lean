/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import WeilConjectures.Mathlib.CategoryTheory.Extensive
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Killing ramification by one root cover

## References

* Stacks Project, Tags 09EB and 0EYG, paragraphs on the strictly henselian base and the extension
  after adjoining a root
* Stacks Project, Tags 09EB and 0EYG, proof through the construction of B' and C
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem regular_divisor_properties_of_etale
    (R S : CommRingCat.{u}) (a : R ⟶ S) (ha : Etale (Spec.map a))
    [IsRegularRing R] (f : R) (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})] :
    IsRegularRing S ∧ IsSMulRegular S (a.hom f) ∧
      IsRegularRing (S ⧸ Ideal.span {a.hom f}) := by
  let : Algebra R S := a.hom.toAlgebra
  have : Algebra.Etale R S := by
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp ha)
  have hreg : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B],
      IsRegularRing B := by
    intro B _ _ _
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
    exact isRegularRing_iff.mpr fun p _ ↦
      IsRegularLocalRing.localization_of_etale (R := R) (A := B) p
  have hS : IsRegularRing S := hreg S
  have hg : IsSMulRegular S (a.hom f) := hf.of_flat
  let I := Ideal.span ({f} : Set R)
  let Q := R ⧸ I
  let T := TensorProduct R Q S
  have : IsRegularRing Q := inferInstance
  have : Algebra.Etale Q T := inferInstance
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing Q T
  have : IsRegularRing T :=
    isRegularRing_iff.mpr fun p _ ↦
      IsRegularLocalRing.localization_of_etale (R := Q) (A := T) p
  have hI : I.map (algebraMap R S) = Ideal.span ({a.hom f} : Set S) := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    rfl
  have hquot : IsRegularRing (S ⧸ Ideal.span {a.hom f}) := by
    rw [← hI]
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toRingEquiv
  exact ⟨hS, hg, hquot⟩

private theorem split_of_section
    {U X : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (W : GaloisCover G U) (s : X ⟶ W.P) :
    ∃ (δ : pullback W.π (s ≫ W.π) ≅ ∐ fun _ : Fin (Nat.card G) ↦ X),
      δ.hom ≫ Sigma.desc (fun _ : Fin (Nat.card G) ↦ 𝟙 X) =
        pullback.snd W.π (s ≫ W.π) := by
  classical
  let e := (Finite.equivFin G).symm
  let σ : Fin (Nat.card G) → (W.P ⟶ W.P) := fun j ↦ W.smul (e j)
  have hσ (j) : σ j ≫ W.π = W.π := W.smul_π _
  let D := Sigma.desc fun j ↦
    pullback.lift (f := W.π) (g := W.π) (𝟙 W.P) (σ j) (by simp [hσ])
  have hD : D = (Sigma.reindex e (fun _ : G ↦ W.P)).hom ≫
      (Sigma.desc fun j : G ↦ pullback.lift (f := W.π) (g := W.π)
        (W.smul j) (𝟙 W.P) (by simp [W.smul_π])) ≫
      (pullbackSymmetry W.π W.π).hom := by
    apply Sigma.hom_ext
    intro j
    have hr := Sigma.ι_reindex_hom (f := fun _ : G ↦ W.P) e j
    dsimp only [Function.comp_def] at hr
    apply pullback.hom_ext <;>
      simp only [D, Category.assoc, Sigma.ι_comp_desc, pullback.lift_fst,
        pullback.lift_snd, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    all_goals rw [← Category.assoc, ← Category.assoc, hr, Sigma.ι_comp_desc]
    all_goals simp [σ]
  have : IsIso D := by
    rw [hD]
    have := W.isIso_sigmaDesc
    infer_instance
  have := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp W.π σ hσ s
  let F := Sigma.desc fun j ↦
    pullback.lift (f := s ≫ W.π) (g := W.π) (𝟙 X) (s ≫ σ j) (by simp [hσ])
  let E := (asIso F).symm
  refine ⟨pullbackSymmetry W.π (s ≫ W.π) ≪≫ E, ?_⟩
  have hF : F ≫ pullback.fst (s ≫ W.π) W.π =
      Sigma.desc (fun _ : Fin (Nat.card G) ↦ 𝟙 X) := by
    apply Sigma.hom_ext
    intro j
    simp [F]
  have hE : E.hom ≫ Sigma.desc (fun _ : Fin (Nat.card G) ↦ 𝟙 X) =
      pullback.fst (s ≫ W.π) W.π := by
    rw [← hF]
    simp [E]
  simpa [Category.assoc] using congrArg
    (fun k ↦ (pullbackSymmetry W.π (s ≫ W.π)).hom ≫ k) hE

private theorem split_over_ambient_of_section
    {L U X : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (b : X ⟶ Spec R) (s : X ⟶ W.P) (hs : s ≫ W.π ≫ i = b ≫ φ) :
    ∃ (δ : pullback (W.π ≫ i) (b ≫ φ) ≅ ∐ fun _ : Fin (Nat.card G) ↦ X),
      δ.hom ≫ Sigma.desc (fun _ : Fin (Nat.card G) ↦ 𝟙 X) =
        pullback.snd (W.π ≫ i) (b ≫ φ) := by
  have : Mono (pullback.snd i φ) := by
    rw [← hβ]
    infer_instance
  let Q := pullback (W.π ≫ i) (b ≫ φ)
  let l₁ : Q ⟶ pullback i φ :=
    pullback.lift (pullback.fst (W.π ≫ i) (b ≫ φ) ≫ W.π)
      (pullback.snd (W.π ≫ i) (b ≫ φ) ≫ b) (by
        simpa only [Category.assoc] using pullback.condition (f := W.π ≫ i) (g := b ≫ φ))
  let l₂ : Q ⟶ pullback i φ :=
    pullback.lift (pullback.snd (W.π ≫ i) (b ≫ φ) ≫ s ≫ W.π)
      (pullback.snd (W.π ≫ i) (b ≫ φ) ≫ b) (by simp [hs, Category.assoc])
  have hl : l₁ = l₂ := (cancel_mono (pullback.snd i φ)).mp (by simp [l₁, l₂])
  have hU : pullback.fst (W.π ≫ i) (b ≫ φ) ≫ W.π =
      pullback.snd (W.π ≫ i) (b ≫ φ) ≫ s ≫ W.π := by
    simpa [l₁, l₂] using congrArg (fun k ↦ k ≫ pullback.fst i φ) hl
  let E : Q ≅ pullback W.π (s ≫ W.π) :=
    { hom := pullback.lift (pullback.fst (W.π ≫ i) (b ≫ φ))
        (pullback.snd (W.π ≫ i) (b ≫ φ)) hU
      inv := pullback.lift (pullback.fst W.π (s ≫ W.π))
        (pullback.snd W.π (s ≫ W.π)) (by
          rw [← Category.assoc, pullback.condition]
          simpa only [Category.assoc] using congrArg
            (fun k ↦ pullback.snd W.π (s ≫ W.π) ≫ k) hs)
      hom_inv_id := by apply pullback.hom_ext <;> simp
      inv_hom_id := by apply pullback.hom_ext <;> simp }
  obtain ⟨δ, hδ⟩ := split_of_section G W s
  refine ⟨E ≪≫ δ, ?_⟩
  simpa [E, Category.assoc] using congrArg (fun k ↦ E.hom ≫ k) hδ

/-- A prime-to-characteristic torsor splits after one punctured root cover, locally on the base.
-/
theorem GaloisCover.regular_divisor_root_splitting
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (y : Spec R) :
    ∃ (S : CommRingCat.{u}) (a : R ⟶ S) (z : Spec S),
      Etale (Spec.map a) ∧ (Spec.map a) z = y ∧
      let g := a.hom f
      ∃ (n : ℕ),
        (0 < n ∧ IsUnit (n : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S g ∧
        IsRegularRing (S ⧸ Ideal.span {g}) ∧
        let p := pullback.snd (W.π ≫ i) (Spec.map a ≫ φ)
        let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
        let N := Spec (CommRingCat.of A)
        let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
        let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
        ∃ (d : ℕ) (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
          δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
            pullback.snd p (V.ι ≫ q) := by
  classical
  let Ω := AlgebraicClosure ((Spec R).residueField y)
  let barY : Spec (.of Ω) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Spec R).residueField y) Ω)) ≫
      (Spec R).fromSpecResidueField y
  have hy (x : Spec (.of Ω)) : barY x = y := by
    exact (Spec R).fromSpecResidueField_apply y _
  let b : R ⟶ strictHenselization barY :=
    (Scheme.Spec.preimage (X := Opposite.op (strictHenselization barY))
      (Y := Opposite.op R) (strictLocalizationToBase barY)).unop
  have hb : Spec.map b = strictLocalizationToBase barY :=
    Scheme.Spec.map_preimage _
  have hs := W.strict_hensel_root_section i G R φ f hG hf β hβ barY b hb
  have : IsFinite W.π := W.isFinite
  have : Etale W.π := W.etale
  obtain ⟨S, a, z, ha, hz, s, hs⟩ :=
    punctured_root_section_etale_descent i W.π R φ f β hβ
      (Nat.card G) barY y hy b hb hs
  obtain ⟨hS, hg, hSg⟩ := regular_divisor_properties_of_etale R S a ha f hf
  have hnS : IsUnit (Nat.card G : S) := by
    simpa using hG.map a.hom
  refine ⟨S, a, z, ha, hz, Nat.card G, ⟨Nat.card_pos, hnS⟩, hS, hg, hSg, ?_⟩
  let g := a.hom f
  let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ Nat.card G - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
  let p := pullback.snd (W.π ≫ i) (Spec.map a ≫ φ)
  obtain ⟨δ, hδ⟩ := split_over_ambient_of_section i G W R φ f β hβ
    (V.ι ≫ q ≫ Spec.map a) s (by simpa only [Category.assoc] using hs)
  let E : pullback p (V.ι ≫ q) ≅ pullback (W.π ≫ i)
      ((V.ι ≫ q ≫ Spec.map a) ≫ φ) :=
    pullbackLeftPullbackSndIso (W.π ≫ i) (Spec.map a ≫ φ) (V.ι ≫ q) ≪≫
      pullback.congrHom rfl (by simp only [Category.assoc])
  refine ⟨Nat.card G, E ≪≫ δ, ?_⟩
  change (E ≪≫ δ).hom ≫ Sigma.desc (fun _ : Fin (Nat.card G) ↦ 𝟙 V.toScheme) =
    pullback.snd p (V.ι ≫ q)
  simpa [E, p, Category.assoc] using congrArg (fun k ↦ E.hom ≫ k) hδ

end AlgebraicGeometry.Scheme
