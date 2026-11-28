import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # A Kummer root section of a Galois cover of a punctured regular local scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FiniteEtale.TameRootSection

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The open immersion `Spec R[1/t] ⟶ Spec R`. -/
abbrev puncture (t : R) : Spec (.of (Localization.Away t)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))

/-- **Abhyankar-type root section.** Let `R` be a regular local ring, `t ≠ 0` with `R/(t)`
regular, and `W` a Galois cover of `Spec R[1/t]` with finite group `G` of order invertible in
`R`. There is an étale `R`-algebra `S`, with a point `z` over the closed point of `Spec R`,
such that `W` acquires a section over the basic open `D(t)` of `Spec S[X]/(X ^ |G| - t)`,
compatible with the maps to `Spec R`. -/
theorem exists_root_section (t : R) (ht : t ≠ 0)
    [IsRegularLocalRing (R ⧸ Ideal.span {t})]
    (G : Type (u + 1)) [Group G] [Finite G] (hG : IsUnit (Nat.card G : R))
    (W : Scheme.GaloisCover G (Spec (.of (Localization.Away t)))) :
    ∃ (S : CommRingCat.{u}) (a : CommRingCat.of R ⟶ S) (z : Spec S),
      Etale (Spec.map a) ∧ (Spec.map a) z = IsLocalRing.closedPoint R ∧
      let g := a.hom t
      let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ Nat.card G - Polynomial.C g)
      let N := Spec (CommRingCat.of A)
      let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
      let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
      ∃ s : V.toScheme ⟶ W.P, s ≫ W.π ≫ puncture t = V.ι ≫ q ≫ Spec.map a := by
  classical
  have hRreg : IsRegularRing R :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal R)).2
  have hQreg : IsRegularRing (R ⧸ Ideal.span {t}) :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {t}))).2
  have hf : IsSMulRegular R t := by
    intro x y hxy
    simpa [smul_eq_mul, mul_right_inj' ht] using hxy
  let i := puncture t
  let β : pullback i (𝟙 (Spec (.of R))) ≅
      Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen t) :=
    asIso (pullback.fst i (𝟙 _)) ≪≫ (basicOpenIsoSpecAway (R := .of R) t).symm
  have hβ : β.hom ≫ Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen t) =
      pullback.snd i (𝟙 _) := by
    simp only [β, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc]
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of R) t, Iso.inv_hom_id_assoc,
      pullback.condition, Category.comp_id]
  let y : Spec (.of R) := IsLocalRing.closedPoint R
  let Ω := AlgebraicClosure ((Spec (.of R)).residueField y)
  let barY : Spec (.of Ω) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of R)).residueField y) Ω)) ≫
      (Spec (.of R)).fromSpecResidueField y
  have hy (x : Spec (.of Ω)) : barY x = y := (Spec (.of R)).fromSpecResidueField_apply y _
  let b : CommRingCat.of R ⟶ Scheme.strictHenselization barY :=
    (Scheme.Spec.preimage (X := Opposite.op (Scheme.strictHenselization barY))
      (Y := Opposite.op (CommRingCat.of R)) (Scheme.strictLocalizationToBase barY)).unop
  have hb : Spec.map b = Scheme.strictLocalizationToBase barY :=
    Scheme.Spec.map_preimage _
  have hs := W.strict_hensel_root_section i G (.of R) (𝟙 _) t hG hf β hβ barY b hb
  have : IsFinite W.π := W.isFinite
  have : Etale W.π := W.etale
  obtain ⟨S, a, z, ha, hz, s, hs⟩ :=
    Scheme.punctured_root_section_etale_descent i W.π (.of R) (𝟙 _) t β hβ
      (Nat.card G) barY y hy b hb hs
  refine ⟨S, a, z, ha, hz, s, ?_⟩
  simpa only [Category.comp_id] using hs

end Langlands.AlgebraicGeometry.FiniteEtale.TameRootSection
