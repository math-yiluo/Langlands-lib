/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverPoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Finite etale descent along the punctured root cover

## References

* Stacks Project, Tags 02LA and 02VN, finite and etale fpqc descent applied to the punctured root
  cover in Tag 0EYG
* Stacks Project, Tags 02LA and 02VN, applied to the punctured cover in Tag 0EYG
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finiteness and etaleness descend from a splitting over a punctured root cover. -/
theorem root_split_factor_finite_etale
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    IsFinite j ∧ Etale j := by
  intro A N q V δ hδ
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen g
  have hrange : Set.range (V.ι ≫ q) ⊆ Set.range U.ι := by
    rintro _ ⟨v, rfl⟩
    rw [U.range_ι]
    change g ∉ (PrimeSpectrum.comap (algebraMap R A) v.1).asIdeal
    exact v.2
  let w : V.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι (V.ι ≫ q) hrange
  have hw : w ≫ U.ι = V.ι ≫ q := IsOpenImmersion.lift_fac _ _ _
  have : Etale (V.ι ≫ q) := root_split_away_cover_etale R g n hn
  have : Etale (w ≫ U.ι) := hw.symm ▸ ‹Etale (V.ι ≫ q)›
  have : Etale w := Etale.of_comp w U.ι
  have : Surjective w := by
    constructor
    intro y
    obtain ⟨v, hv⟩ := root_split_away_cover_point R g n hn.1 y.1 y.2
    refine ⟨v, ?_⟩
    apply (show Function.Injective U.ι from Subtype.val_injective)
    change (w ≫ U.ι) v = y.1
    rw [hw]
    exact hv
  have : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen g
  have : IsAffine V.toScheme :=
    @IsAffineOpen.Spec_basicOpen (CommRingCat.of A) (algebraMap R A g)
  have : QuasiCompact w := inferInstance
  have hpb : IsPullback (pullback.fst p (V.ι ≫ q))
      (pullback.snd p (V.ι ≫ q)) j w := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk
      (pullback.fst p (V.ι ≫ q)) (pullback.snd p (V.ι ≫ q)) ?_) ?_
    · rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hj, hw]
      exact pullback.condition
    · exact PullbackCone.isLimitOfFactors p (V.ι ≫ q) U.ι j w hj hw
        (pullback.cone p (V.ι ≫ q)) (pullback.isLimit p (V.ι ≫ q))
  have : IsFinite (pullback.snd p (V.ι ≫ q)) := by
    rw [← hδ]
    infer_instance
  have : Etale (pullback.snd p (V.ι ≫ q)) := by
    have : Etale (Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme)) :=
      IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)
    rw [← hδ]
    infer_instance
  have : MorphismProperty.DescendsAlong @IsFinite
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite)
      hpb.flip (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      hpb.flip (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance⟩


end AlgebraicGeometry.Scheme
