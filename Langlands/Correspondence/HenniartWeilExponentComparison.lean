import Langlands.Correspondence.HenniartPadicArtinTransport
import Langlands.Correspondence.HenniartWeilSwanBreak
import Langlands.LocalFactor.Ramification.WeilExponent

/-!
# The Artin and Swan exponents of Weil representations against Henniart's numerical relations

For a representative `A` of an irreducible Weil class `σ` of rank `k + 1` over a p-adic field `K`,
the relation `HasArtinConductor K σ a` holds exactly for `a = Weil.Local.artinExponent K A`
(`hasArtinConductor_iff_artinExponent_eq`), and the Swan exponent `weilSwanExponent K σ`, defined by
choice as the Artin conductor minus the rank, is `Weil.Local.swanExponent K A`
(`weilSwanExponent_eq_swanExponent`).
-/

namespace Langlands.Henniart.Numerical

open Correspondence Ramification.Padic Weil.Local

universe uK uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- **`HasArtinConductor` is the Artin exponent**: for a representative `A` of an irreducible Weil
class `σ`, `HasArtinConductor K σ a` holds exactly when `a` is the Artin exponent of `A`. -/
theorem hasArtinConductor_iff_artinExponent_eq {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) (a : ℕ) :
    HasArtinConductor K σ a ↔ artinExponent K A = a := by
  rw [hasArtinConductor_iff_exists_padicPresentation]
  constructor
  · rintro ⟨B, P, hP, hB, ha⟩
    obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff A B).mp (hA.trans hB.symm)
    rw [artinExponent_eq_of_equiv e]
    exact_mod_cast (artinExponent_eq P hP).trans ha
  · intro h
    obtain ⟨P, hP, ha, -⟩ :=
      exists_presentation_of_isContinuous (weilRepresentative_continuous_irreducible K hA).1
    exact ⟨A, P, hP, hA, ha.trans (by rw [h])⟩

/-- A representative's Artin exponent satisfies `HasArtinConductor`. -/
theorem hasArtinConductor_artinExponent {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) :
    HasArtinConductor K σ (artinExponent K A) :=
  (hasArtinConductor_iff_artinExponent_eq K hA _).mpr rfl

/-- The chosen Swan exponent of a class is the Artin exponent of a representative minus the
rank. -/
theorem weilSwanExponent_eq_artinExponent_sub {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) :
    weilSwanExponent K σ = artinExponent K A - (k + 1) := by
  rw [weilSwanExponent, (hasArtinConductor_iff_artinExponent_eq K hA _).mp
    (Classical.choose_spec (weilArtinConductorExistence p K k σ))]

/-- **`weilSwanExponent` is the Swan exponent**: for a representative `A` of an irreducible Weil
class `σ`, the chosen Swan exponent of `σ` is the Swan exponent of `A`. -/
theorem weilSwanExponent_eq_swanExponent {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) :
    weilSwanExponent K σ = swanExponent K A := by
  obtain ⟨hc, hi⟩ := weilRepresentative_continuous_irreducible K hA
  obtain ⟨-, hn⟩ := weilRepresentative_break_rank K hA
  obtain ⟨P, hP, ha, hs⟩ := exists_presentation_of_isContinuous hc
  have hArtin := irreducible_artin_sub_rank_eq_rank_mul_lastBreak K A hc hi P hP ha
  have hSwan := irreducible_presentation_swan_eq_rank_mul_lastBreak K A hc hi P hP
  rw [hs, Rat.cast_natCast, ← hArtin, hn] at hSwan
  rw [weilSwanExponent_eq_artinExponent_sub K hA]
  exact_mod_cast hSwan.symm

/-- `HasWeilSwan` is the Swan exponent of a representative. -/
theorem hasWeilSwan_iff_swanExponent_eq {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uW} K k.succPNat}
    {A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (hA : FiniteRepresentation.classOf A = weilClassForget K σ) (s : ℕ) :
    HasWeilSwan K σ s ↔ swanExponent K A = s := by
  rw [← weilSwanExponent_eq_swanExponent K hA, weilSwanExponent_eq_artinExponent_sub K hA]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [(hasArtinConductor_iff_artinExponent_eq K hA a).mp ha]
  · intro h
    exact ⟨_, hasArtinConductor_artinExponent K hA, h⟩

end Langlands.Henniart.Numerical
