/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange
import WeilConjectures.RingTheory.RegularPrincipalPrimeLocalizationDvr
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationLocalizationComparison

/-! # Localization of the root normalization to a DVR model

## References

* Stacks Project, Tag 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem adjoinRoot_isLocalization_map (R : Type u) (S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (p : Polynomial R) :
    let g := AdjoinRoot.map (algebraMap R S) p (p.map (algebraMap R S)) dvd_rfl
    let := g.toAlgebra
    IsLocalization (M.map (AdjoinRoot.of p)) (AdjoinRoot (p.map (algebraMap R S))) := by
  let : Algebra (Polynomial R) (Polynomial S) := Polynomial.algebra R S
  let g := AdjoinRoot.map (algebraMap R S) p (p.map (algebraMap R S)) dvd_rfl
  let := g.toAlgebra
  let := Polynomial.isLocalization M S
  have h : (AdjoinRoot.mk (p.map (algebraMap R S))).comp
      (algebraMap (Polynomial R) (Polynomial S)) =
      (algebraMap (AdjoinRoot p) (AdjoinRoot (p.map (algebraMap R S)))).comp
        (AdjoinRoot.mk p) := by
    change (AdjoinRoot.mk _).comp (Polynomial.mapRingHom (algebraMap R S)) =
      g.comp (AdjoinRoot.mk p)
    ext x <;> simp [g]
  have hkR : RingHom.ker (AdjoinRoot.mk p) = Ideal.span {p} := by
    ext x
    simp [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  have hkS : RingHom.ker (AdjoinRoot.mk (p.map (algebraMap R S))) =
      Ideal.span {p.map (algebraMap R S)} := by
    ext x
    simp [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  have hk : RingHom.ker (AdjoinRoot.mk (p.map (algebraMap R S))) ≤
      (RingHom.ker (AdjoinRoot.mk p)).map
        (algebraMap (Polynomial R) (Polynomial S)) := by
    rw [hkR, hkS]
    change Ideal.span {p.map (algebraMap R S)} ≤
      (Ideal.span {p}).map (Polynomial.mapRingHom (algebraMap R S))
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton p))
  have hloc := IsLocalization.of_surjective (M.map Polynomial.C) (Polynomial S)
    (AdjoinRoot.mk p) (AdjoinRoot.mk_surjective (g := p))
    (AdjoinRoot.mk (p.map (algebraMap R S)))
    (AdjoinRoot.mk_surjective (g := p.map (algebraMap R S))) h hk
  have hm : M.map (AdjoinRoot.of p) = (M.map Polynomial.C).map (AdjoinRoot.mk p) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Polynomial.C a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  exact hm ▸ hloc

private theorem root_span_comap {H : Type u} [CommRing H]
    (n : ℕ) (hn : 0 < n) (g : H) :
    (Ideal.span {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)}).comap
       (algebraMap H (AdjoinRoot
        ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g))) = Ideal.span {g} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let F := (Polynomial.X : Polynomial H) ^ (m + 1) - Polynomial.C g
  let A := AdjoinRoot F
  let t : A := AdjoinRoot.root F
  have ht : t ^ (m + 1) = algebraMap H A g := by
    have he := AdjoinRoot.eval₂_root F
    simpa only [F, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using he
  let χ : A →+* H ⧸ Ideal.span {g} :=
    AdjoinRoot.lift (f := F) (Ideal.Quotient.mk _) 0 (by simp [F])
  have hχt : χ t = 0 := AdjoinRoot.lift_root _
  have hχr (r : H) : χ (algebraMap H A r) = Ideal.Quotient.mk _ r :=
    AdjoinRoot.lift_of _
  apply le_antisymm
  · intro r hr
    change algebraMap H A r ∈ Ideal.span {t} at hr
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg χ hc
    simpa only [map_mul, hχt, hχr, zero_mul] using he
  · apply Ideal.span_le.mpr
    intro r hr
    have hrg : r = g := Set.mem_singleton_iff.mp hr
    subst r
    change algebraMap H A g ∈ Ideal.span {t}
    rw [← ht, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton t))

set_option linter.unusedVariables false in
/-- The stalk of a root normalization is identified with the corresponding DVR model. -/
theorem root_normalization_dvr_comparison
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (H : CommRingCat.{u}) [IsNoetherianRing H] (b : R ⟶ H)
    (hG : IsUnit (Nat.card G : H)) (hg : IsSMulRegular H (b.hom f))
    [IsDomain (H ⧸ Ideal.span {b.hom f})] :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    let := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    let := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)} →
      let C := a.normalization.presheaf.stalk x
      let t := AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
        (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g))
      ∃ (B : CommRingCat.{u}) (hB : IsDomain B),
        letI := hB
        ∃ (hDvr : IsDiscreteValuationRing B),
          letI := hDvr
          ∃ (pi : B), Irreducible pi ∧ IsUnit (Nat.card G : B) ∧
          ∃ (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B)))),
            let A0 := AdjoinRoot
              ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
            let N0 := Spec (CommRingCat.of A0)
            let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
            let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
            let a0 := pullback.snd (T.π ≫ j0) q0
            ∃ (hqc : QuasiCompact a0) (hqs : QuasiSeparated a0),
              letI := hqc
              letI := hqs
              IsFinite a0.fromNormalization ∧
              ∃ (x0 : a0.normalization),
                (a0.fromNormalization x0).asIdeal = Ideal.span
                  {AdjoinRoot.root
                    ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)} ∧
                ∃ (e : a0.normalization.presheaf.stalk x0 ≃+* C),
                  e ((a0.fromNormalization.stalkMap x0).hom
                    (AlgebraicGeometry.StructureSheaf.toStalk A0 (a0.fromNormalization x0)
                      (AdjoinRoot.root
                        ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))) =
                    (a.fromNormalization.stalkMap x).hom t := by
  let : (Ideal.span {b.hom f}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  let B := CommRingCat.of (Localization.AtPrime (Ideal.span {b.hom f}))
  obtain ⟨hB, hDvr, hpi⟩ :=
    IsLocalization.regular_principal_prime_dvr (B := B) (b.hom f) hg
  let := hB
  let := hDvr
  let pi : B := algebraMap H B (b.hom f)
  have hn : IsUnit (Nat.card G : B) := by
    simpa using hG.map (algebraMap H B)
  let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
  let z := Spec.map (CommRingCat.ofHom (algebraMap H B))
  let r := j ≫ z ≫ Spec.map b
  have hr : Set.range r ⊆ Set.range
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f)) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change algebraMap B (FractionRing B) (algebraMap H B (b.hom f)) ∉ y.asIdeal
    have hunit : IsUnit (algebraMap B (FractionRing B) pi) := by
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_zero] using
        (IsFractionRing.injective B (FractionRing B)).ne hpi.ne_zero
    exact fun h ↦ y.isPrime.ne_top (y.asIdeal.eq_top_of_isUnit_mem h hunit)
  let d := IsOpenImmersion.lift
    (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f)) r hr
  let k := d ≫ β.inv ≫ pullback.fst i φ
  have hk : k ≫ i = j ≫ z ≫ Spec.map b ≫ φ := by
    dsimp only [k]
    rw [Category.assoc, Category.assoc, pullback.condition]
    rw [← hβ]
    simp only [← Category.assoc, β.inv_hom_id, Category.id_comp]
    rw [IsOpenImmersion.lift_fac]
    simp only [r, Category.assoc]
  have hchart : IsPullback (β.inv ≫ pullback.fst i φ)
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f)) i φ := by
    apply (IsPullback.of_hasPullback i φ).of_iso β (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simpa using hβ.symm
    · simp
    · simp
  have hbranch : IsPullback k (𝟙 _) i (j ≫ z ≫ Spec.map b ≫ φ) := by
    simpa only [k, r, Category.assoc] using
      (IsOpenImmersion.isPullback_lift_id r
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f)) hr).paste_horiz hchart
  obtain ⟨T, ρ, hT⟩ := GaloisCover.exists_baseChange G W k
  dsimp only
  intro hN hp hEtale hNorm x hx
  let := hN
  let := hp
  refine ⟨B, hB, hDvr, pi, hpi, hn, T, ?_⟩
  have hrootloc := adjoinRoot_isLocalization_map H B (Ideal.span {b.hom f}).primeCompl
    ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
  have hcontract := root_span_comap (Nat.card G) (Nat.card_pos (α := G)) (b.hom f)
  have hcomp := root_normalization_localization_comparison i G W H B (b.hom f)
    hpi (Spec.map b ≫ φ) k hk hbranch T ρ hT hrootloc hN hp hEtale hNorm x hx hcontract
  exact hcomp

end AlgebraicGeometry.Scheme
