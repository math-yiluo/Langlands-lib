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
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Ideal

import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericResidueDegreeDvd

/-! # RootNormalizationGenericStalkResidueSeparable

## References

* Stacks Project, Tags 09EB, 0BRM and 0EYG
* Stacks Project, 0BRM, 0307, and 09E7
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem sep_of_degree_dvd {K E : Type*} [Field K] [Field E] [Algebra K E]
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : K))
    (hd : Module.finrank K E ∣ n) : Algebra.IsSeparable K E := by
  have hpos : 0 < Module.finrank K E := Nat.pos_of_dvd_of_pos hd hn
  have : FiniteDimensional K E := FiniteDimensional.of_finrank_pos hpos
  apply (isSeparable_iff_finInsepDegree_eq_one K E).mpr
  generalize hqeq : ringExpChar K = q
  have hq : ExpChar K q := hqeq ▸ ringExpChar.expChar K
  let := hq
  obtain ⟨r, hr⟩ := finInsepDegree_eq_pow K E q
  have hi : Field.finInsepDegree K E ∣ n :=
    (dvd_of_mul_left_eq _ (Field.finSepDegree_mul_finInsepDegree K E)).trans hd
  cases hq with
  | zero => simpa using hr
  | prime hp =>
    by_cases hzero : r = 0
    · simpa [hzero] using hr
    · have hdiv : q ∣ n := (dvd_pow_self _ hzero).trans (hr ▸ hi)
      exact False.elim (hu.ne_zero ((CharP.cast_eq_zero_iff K q n).mpr hdiv))

/-- The residue-field extension at a normalization point above the root divisor
generic point is separable. -/
theorem root_normalization_generic_stalk_residue_separable
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
    (∀ (Q : Ideal A) (hQ : Q.IsPrime),
      letI := hQ
      AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g) ∈ Q →
        IsRegularLocalRing (Localization.AtPrime Q)) →
    ∀ (hN : IsLocallyNoetherian N),
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
      ∀ (x : a.normalization), a.fromNormalization x = j η →
        letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparable (N.residueField (a.fromNormalization x))
          (a.normalization.residueField x) := by
  dsimp only
  intro hroot hN hp he hn D j hD hDi hj hV η hη x hx
  have hd := root_normalization_generic_stalk_residue_degree_dvd i G W R φ f β hβ H b
    hg hroot hN hp he hn D j hD hDi hj hV η hη x hx
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
  let N := Spec (CommRingCat.of A)
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A (b.hom f))
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
  let a := p ≫ V.ι
  let K := N.residueField (a.fromNormalization x)
  let E := a.normalization.residueField x
  let := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
  let α : H →+* K :=
    ((ΓSpecIso (CommRingCat.of A)).inv ≫ N.Γevaluation (a.fromNormalization x)).hom.comp
      (algebraMap H A)
  have hu : IsUnit (Nat.card G : K) := by simpa using hG.map α
  exact sep_of_degree_dvd (Nat.card G) Nat.card_pos hu hd

end AlgebraicGeometry.Scheme
