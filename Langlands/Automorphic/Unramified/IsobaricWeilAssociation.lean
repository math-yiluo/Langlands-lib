import Langlands.Automorphic.IsobaricData
import Langlands.Automorphic.Unramified.AbsoluteWeilAssociation

/-! # Weak association of Weil representations with isobaric constituent data

Representations of the relative Weil group `W_{E/F}` and of the absolute Weil group
`S.WeilGroup` are compared with isobaric constituent data through spectral systems attached
to the data. For data of a single cuspidal class the relation is the published cuspidal
class relation. No representation, isobaric sum or spectrum is constructed.
-/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.Global Langlands.Global.CompletionPadic Langlands.Unramified Langlands.Automorphic

universe u uV uW uP

namespace RelativeWeilGroup

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}

/-- Weak association depends only on Euler polynomials outside a finite set. -/
theorem IsWeaklyAssociated.of_sameEulerPolynomials {n : ℕ}
    {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {s t : SpectralSystem (FinitePlace F) n} (hA : IsWeaklyAssociated A s)
    (hst : s.SameEulerPolynomials t) : IsWeaklyAssociated A t := by
  rcases hA with ⟨hc, hn, hA⟩
  refine ⟨hc, hn, ?_⟩
  filter_upwards [hA, hst, t.exceptional.eventually_cofinite_notMem] with v hv hvst ht
  obtain ⟨hs, hm⟩ := hv
  exact ⟨ht, hvst hs ht ▸ hm⟩

variable [CompactSpace (AdeleQuotient F)]

/-- `A` is weakly associated with the isobaric constituent data `D`: some spectral system
attached to `D` is weakly associated with `A`. -/
def IsWeaklyAssociatedIsobaric (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (D : IsobaricData F) : Prop :=
  ∃ s : SpectralSystem (FinitePlace F) D.rank,
    IsobaricData.HasSpectralSystem.{u, uP} D s ∧ IsWeaklyAssociated A s

/-- For the data of one cuspidal class, isobaric association is cuspidal class association. -/
theorem isWeaklyAssociatedIsobaric_ofCuspidal_iff
    (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) {r : ℕ}
    (π : CuspidalOperatorRealization.IsoClass F r) :
    IsWeaklyAssociatedIsobaric.{u, uV, uP} A
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank π)) ↔
      IsWeaklyAssociatedClass.{u, uV, uP} A π := by
  constructor
  · rintro ⟨s, hs, hA⟩
    obtain ⟨t, ht, hts⟩ := hs.exists_ofCuspidal
    exact ⟨t, ht, hA.of_sameEulerPolynomials hts.symm⟩
  · rintro ⟨s, hs, hA⟩
    exact ⟨s, IsobaricData.hasSpectralSystem_ofCuspidal_of
      (c := PositiveRankCuspidalClass.ofFixedRank π)
      ((PositiveRankCuspidalClass.hasSpectralSystem_ofFixedRank π s).mpr hs)
      (SpectralSystem.sameEulerPolynomials_refl _), hA⟩

/-- Isobaric association depends only on the equivalence class of `A`. -/
theorem IsWeaklyAssociatedIsobaric.of_equiv
    {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {B : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)} {D : IsobaricData F}
    (φ : FiniteRepresentation.Equiv A B) (hA : IsWeaklyAssociatedIsobaric.{u, uV, uP} A D) :
    IsWeaklyAssociatedIsobaric.{u, uW, uP} B D := by
  obtain ⟨s, hs, hA⟩ := hA
  exact ⟨s, hs, hA.of_equiv φ⟩

end RelativeWeilGroup

namespace WeilMapSystem

variable {c : FundamentalClass.ClassFamily.{u}} {F : Type u} [Field F] [NumberField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] {h : FundamentalClass.Restriction c}
  (S : WeilMapSystem c F Ω h)

/-- Weak association depends only on Euler polynomials outside a finite set. -/
theorem IsWeaklyAssociated.of_sameEulerPolynomials {n : ℕ}
    {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
    {s t : SpectralSystem (FinitePlace F) n} (hA : S.IsWeaklyAssociated A s)
    (hst : s.SameEulerPolynomials t) : S.IsWeaklyAssociated A t := by
  rcases hA with ⟨hc, hn, hA⟩
  refine ⟨hc, hn, ?_⟩
  filter_upwards [hA, hst, t.exceptional.eventually_cofinite_notMem] with v hv hvst ht
  obtain ⟨hs, hm⟩ := hv
  exact ⟨ht, hvst hs ht ▸ hm⟩

variable [CompactSpace (AdeleQuotient F)]

/-- `A` is weakly associated with the isobaric constituent data `D`: some spectral system
attached to `D` is weakly associated with `A`. -/
def IsWeaklyAssociatedIsobaric (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (D : IsobaricData F) : Prop :=
  ∃ s : SpectralSystem (FinitePlace F) D.rank,
    IsobaricData.HasSpectralSystem.{u, uP} D s ∧ S.IsWeaklyAssociated A s

/-- For the data of one cuspidal class, isobaric association is cuspidal class association. -/
theorem isWeaklyAssociatedIsobaric_ofCuspidal_iff
    (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup) {r : ℕ}
    (π : CuspidalOperatorRealization.IsoClass F r) :
    S.IsWeaklyAssociatedIsobaric.{u, uV, uP} A
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank π)) ↔
      S.IsWeaklyAssociatedClass.{u, uV, uP} A π := by
  constructor
  · rintro ⟨s, hs, hA⟩
    obtain ⟨t, ht, hts⟩ := hs.exists_ofCuspidal
    exact ⟨t, ht, IsWeaklyAssociated.of_sameEulerPolynomials S hA hts.symm⟩
  · rintro ⟨s, hs, hA⟩
    exact ⟨s, IsobaricData.hasSpectralSystem_ofCuspidal_of
      (c := PositiveRankCuspidalClass.ofFixedRank π)
      ((PositiveRankCuspidalClass.hasSpectralSystem_ofFixedRank π s).mpr hs)
      (SpectralSystem.sameEulerPolynomials_refl _), hA⟩

/-- Isobaric association depends only on the equivalence class of `A`. -/
theorem IsWeaklyAssociatedIsobaric.of_equiv {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
    {B : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup} {D : IsobaricData F}
    (φ : FiniteRepresentation.Equiv A B) (hA : S.IsWeaklyAssociatedIsobaric.{u, uV, uP} A D) :
    S.IsWeaklyAssociatedIsobaric.{u, uW, uP} B D := by
  obtain ⟨s, hs, hA⟩ := hA
  exact ⟨s, hs, hA.of_equiv S φ⟩

/-- Relative isobaric association gives absolute isobaric association of the inflation,
provided local-to-global Weil maps exist at all but finitely many finite places. -/
theorem isWeaklyAssociatedIsobaric_inflate {K : FiniteGaloisIntermediateField F Ω}
    {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)} {D : IsobaricData F}
    (hA : RelativeWeilGroup.IsWeaklyAssociatedIsobaric.{u, uV, uP} A D)
    (hθ : ∀ᶠ v in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup, S.IsLocalWeilMap v θ) :
    S.IsWeaklyAssociatedIsobaric.{u, uV, uP} (S.inflate K A) D := by
  obtain ⟨s, hs, hA⟩ := hA
  exact ⟨s, hs, S.isWeaklyAssociated_inflate hA hθ⟩

end WeilMapSystem

end Langlands.ClassField.Global
