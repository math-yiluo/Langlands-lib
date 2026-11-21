import Langlands.Global.RankinSelberg.ComplexBruhatCutoff
import Langlands.Representation.Archimedean.PrincipalSeriesAdmissible

/-! # Localizing smooth principal-series functionals on complex Gauss charts -/

noncomputable section

open Set Filter TopologicalSpace
open scoped Classical Distributions Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatSectionLocality

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.Archimedean (continuous_unitary_toUnits complexPositionCharacter mem_principalSeries_iff)
open Langlands.Archimedean.PrincipalSeries (exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact)
open Langlands.Archimedean.UnitaryFinitePolynomial (compactSpace_unitary)
open Langlands.GeneralLinear (upperTriangularSubgroup)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (chartDomain chartCoordinates chartSection chartUpper chartUpper_mem
  continuous_chartSection chart_factorization)
open ComplexBruhatTestExtension (ChartTest chartSaturation mem_chartSaturation extendTest)
open ComplexBruhatCutoff (chartCutoff cutoffSection cutoffSection_apply complexBruhatCutoff)
open ComplexWhittakerSmoothExtension (SmoothStandard)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => upperTriangularSubgroup n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- The open sets used for section locality are preserved by left Borel multiplication. -/
def IsBorelSaturated (U : Set (G n)) : Prop :=
  ∀ (b : B n) (g : G n), g ∈ U → b.val * g ∈ U

/-- Saturating the representative preimage of a Borel-saturated set gives its intersection
with the chart. -/
theorem chartSaturation_preimage_section (w : Equiv.Perm (Fin n)) {U : Set (G n)}
    (hU : IsBorelSaturated U) : chartSaturation w (chartSection w ⁻¹' U) = chartDomain w ∩ U := by
  ext g
  rw [mem_chartSaturation]
  constructor
  · rintro ⟨hg, hz⟩
    let b : B n := ⟨chartUpper w g, chartUpper_mem w g hg⟩
    have he := hU b (chartSection w (chartCoordinates w g.val)) hz
    exact ⟨hg, (chart_factorization w g) ▸ he⟩
  · rintro ⟨hg, hUg⟩
    let b : B n := ⟨chartUpper w g, chartUpper_mem w g hg⟩
    have he : b.val⁻¹ * g = chartSection w (chartCoordinates w g.val) := by
      calc
        b.val⁻¹ * g = b.val⁻¹ * (b.val * chartSection w (chartCoordinates w g.val)) :=
          congrArg (b.val⁻¹ * ·) (chart_factorization w g).symm
        _ = _ := inv_mul_cancel_left _ _
    have hb := hU b⁻¹ g hUg
    change b.val⁻¹ * g ∈ U at hb
    rw [he] at hb
    exact ⟨hg, hb⟩

/-- A principal-series functional vanishes on all sections supported in the set. -/
def IsVanishingOnSections (L : SmoothStandard n ds →ₗ[ℂ] ℂ) (U : Set (G n)) : Prop :=
  ∀ F : SmoothStandard n ds, tsupport F.val ⊆ U → L F = 0

private theorem standard_eq_zero_of_unitary (F : SmoothStandard n ds)
    (hF : ∀ k : K n, F.val (Unitary.toUnits k) = 0) : F = 0 := by
  apply Subtype.ext
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  let κ : K n := ⟨k.val, hk⟩
  have he : Unitary.toUnits κ = k := Units.ext rfl
  have hk0 : F.val k = 0 := he ▸ hF κ
  change F.val (Langlands.GeneralLinear.Iwasawa.diagonalUnits a * u.val * k) = 0
  rw [((mem_principalSeries_iff ℂ n (complexPositionCharacter ds) F.val).mp F.2).2 a u k, hk0, mul_zero]

/-- Vanishing on chart extensions over an open chart section cover gives vanishing on
all smooth sections supported in the covered region. -/
def ComplexBruhatSectionLocalityStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (L : SmoothStandard n ds →ₗ[ℂ] ℂ) (U : Set (G n)),
    (∀ g ∈ U, ∃ (w : Equiv.Perm (Fin n)) (O : Set (Coordinates n)),
      IsOpen O ∧ g ∈ chartSaturation w O ∧
        ∀ φ : ChartTest n, tsupport φ ⊆ O → L (extendTest w ds φ) = 0) →
    IsVanishingOnSections L U

set_option maxHeartbeats 850000 in
theorem complexBruhatSectionLocality : ComplexBruhatSectionLocalityStatement := by
  intro n ds L U hLocal F hSupp
  let S : Set (K n) := (Unitary.toUnits : K n → G n) ⁻¹' tsupport F.val
  have hS : IsCompact S := ((isClosed_tsupport F.val).preimage continuous_unitary_toUnits).isCompact
  have hI (i : S) := hLocal (Unitary.toUnits i.val) (hSupp i.2)
  choose w O hO hSat hVan using hI
  have hBump (i : S) := complexBruhatCutoff n ds (w i) (O i) (Unitary.toUnits i.val) (hO i) (hSat i)
  choose η hη hEq hRecover using hBump
  have hN (i : S) : {g : G n | chartCutoff (w i) (η i) g = 1} ∈ 𝓝 (Unitary.toUnits i.val) := hEq i
  have hOpen (i : S) := mem_nhds_iff.mp (hN i)
  choose V hV hVo hVi using hOpen
  let W (i : S) : Set (K n) := (Unitary.toUnits : K n → G n) ⁻¹' V i
  have hW (i : S) : IsOpen (W i) := (hVo i).preimage continuous_unitary_toUnits
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover W hW (fun k hk => mem_iUnion.mpr ⟨⟨k, hk⟩, hVi ⟨k, hk⟩⟩)
  have hKill (i : S) (H : SmoothStandard n ds) : L (cutoffSection (w i) (η i) H) = 0 := by
    obtain ⟨φ, hφ, hH⟩ := hRecover i H
    rw [← hH]
    exact hVan i φ (hφ.trans (hη i))
  have hFinite (s : Finset S) (H : SmoothStandard n ds)
      (hCover : ∀ k : K n, H.val (Unitary.toUnits k) ≠ 0 →
        ∃ i ∈ s, chartCutoff (w i) (η i) (Unitary.toUnits k) = 1) : L H = 0 := by
    induction s using Finset.induction_on generalizing H with
    | empty =>
        have he : H = 0 := standard_eq_zero_of_unitary H (fun k => by
          by_contra h
          obtain ⟨i, hi, _⟩ := hCover k h
          exact Finset.notMem_empty i hi)
        rw [he, map_zero]
    | @insert i s hi ih =>
        let R := H - cutoffSection (w i) (η i) H
        have hR (k : K n) (hk : R.val (Unitary.toUnits k) ≠ 0) :
            ∃ j ∈ s, chartCutoff (w j) (η j) (Unitary.toUnits k) = 1 := by
          have hh : H.val (Unitary.toUnits k) ≠ 0 := fun he => hk (by
            change H.val (Unitary.toUnits k) - (cutoffSection (w i) (η i) H).val (Unitary.toUnits k) = 0
            rw [cutoffSection_apply, he, mul_zero, sub_self])
          obtain ⟨j, hj, he⟩ := hCover k hh
          rcases Finset.mem_insert.mp hj with hji | hj
          · subst j
            exfalso
            exact hk (by
              change H.val (Unitary.toUnits k) - (cutoffSection (w i) (η i) H).val (Unitary.toUnits k) = 0
              rw [cutoffSection_apply, he, one_mul, sub_self])
          · exact ⟨j, hj, he⟩
        have he := ih R hR
        dsimp only [R] at he
        rwa [map_sub, hKill i H, sub_zero] at he
  apply hFinite t F
  intro k hk
  have hkS : k ∈ S := subset_tsupport _ hk
  obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hkS)
  obtain ⟨hit, hki⟩ := mem_iUnion.mp hi
  exact ⟨i, hit, hV i hki⟩

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatSectionLocality
