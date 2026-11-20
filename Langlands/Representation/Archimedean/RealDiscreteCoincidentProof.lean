import Langlands.Representation.Archimedean.RealTiedDiscreteScalarCommutantCases
import Langlands.Representation.Archimedean.RealDiscreteMinorSelection
import Langlands.Representation.Archimedean.RealSphericalJacquet
import Langlands.Representation.Archimedean.RealBottomMinorShift
import Langlands.Representation.Archimedean.RealPrincipalSeriesScalarDetector

/-! # The scalar commutant for tied real discrete-series blocks at coincident exponents -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open RealCharacterCrossing (PL)
open RealDiscreteNestedAssembly RealDiscreteDonorShift RealDiscreteMinorSelection
open RealBottomMinorProducts RealBottomMinorTriangular RealBottomMinorJacquet RealBottomMinorShift
open RealSphericalJacquet

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

private theorem charData_recovers (d : RealCharacterData) :
    RealJacquetFrobenius.charData d.parity d.exponent = d := by
  rcases d with ⟨χ, e, τ, hχ⟩
  have h : (RealJacquetFrobenius.charData e τ).character = χ :=
    ContinuousMonoidHom.ext fun x => Units.ext (by
      rw [RealJacquetFrobenius.charData_character_apply, hχ]
      rfl)
  change RealJacquetFrobenius.charHom e τ = χ at h
  cases h
  rfl

private theorem PL_recovers {n : ℕ} (c : Fin n → RealCharacterData) :
    PL (fun i => (c i).exponent) (fun i => (c i).parity) =
      (List.ofFn c).map RealBlock.character := by
  simp only [PL, charData_recovers]

private theorem character_position_permutation {n : ℕ} {c d : Fin n → RealCharacterData}
    (h : (List.ofFn d).Perm (List.ofFn c)) : ∃ σ : Equiv.Perm (Fin n), ∀ i, c (σ i) = d i := by
  apply RealMinorWeightBound.exists_perm_of_multiset_eq
  have hm : ((List.ofFn d : List RealCharacterData) : Multiset RealCharacterData) = List.ofFn c :=
    Multiset.coe_eq_coe.mpr h
  simpa only [Finset.val_univ_fin, Multiset.map_coe, ← List.ofFn_eq_map] using hm

/-- The actual compact-finite tied real standard module has scalar commutant in the
coincident discrete-exponent case. -/
theorem realTiedDiscreteCoincidentScalarCommutant :
    RealTiedDiscreteCoincidentScalarCommutantStatement := by
  intro n ds hn ht ⟨x, hx, _⟩ _
  classical
  let r := realBlockExponent x
  obtain ⟨even, odd, bs, he, ho, hb, hsort, hlen, hQ, hJ⟩ :=
    exists_presentations hn (fun y hy => ht y hy x hx)
  obtain ⟨c, z, weights, hc, hreal, hpar, hmono, hchamber, hw, horder⟩ :=
    exists_donor_shift he ho hb hsort hlen
  let τ (i : Fin n) := (c i).exponent
  let e (i : Fin n) := (c i).parity
  let τ₀ (i : Fin n) := τ i - (weights i : ℂ)
  let receiver := receiverChars even bs odd
  have hlen' : receiver.length = n :=
    (donorChars_perm_receiverChars even bs odd).length_eq.symm.trans hlen
  let d (i : Fin n) := receiver.get (Fin.cast hlen'.symm i)
  have hd : List.ofFn d = receiver :=
    (List.ofFn_congr hlen' receiver.get).symm.trans (List.ofFn_get receiver)
  have hlist : (List.ofFn d).Perm (List.ofFn c) := by
    rw [hd, hc]
    exact (donorChars_perm_receiverChars even bs odd).symm
  obtain ⟨σ, hσ⟩ := character_position_permutation hlist
  have hdonor : PL τ e = (donorChars even bs odd).map RealBlock.character := by
    rw [← hc]
    exact PL_recovers c
  have hreceiver : PL (τ ∘ σ) (e ∘ σ) = (receiverChars even bs odd).map RealBlock.character := by
    have hcd : c ∘ σ = d := funext hσ
    calc
      PL (τ ∘ σ) (e ∘ σ) = (List.ofFn (c ∘ σ)).map RealBlock.character := PL_recovers _
      _ = _ := by rw [hcd, hd]
  rw [← hdonor] at hQ
  rw [← hreceiver] at hJ
  let q := (Finset.univ : Finset (Fin n)).sup weights
  have hbound (i : Fin n) : weights i ≤ q := Finset.le_sup (Finset.mem_univ i)
  let R := rows (q := q) weights
  have hR : RealMinorWeightBound.Nested (fun t => (R t).val) :=
    rows_subset_of_card_le weights
  have hRweight : columnWeight R = weights := columnWeight_rows weights hbound
  have hshift : ∀ a : Fin n → ℝˣ,
      principalSeriesCharacter ℝ n (realPositionCharacter (PL τ e)) a =
        principalSeriesCharacter ℝ n (realPositionCharacter (PL τ₀ 0)) a * diagonalFactor R a :=
    principalSeriesCharacter_levels weights hbound τ e hpar
  obtain ⟨v, hvK, hvOne⟩ := exists_spherical τ₀
  have hv₀ : v ≠ 0 := by
    intro hv
    rw [hv, map_zero] at hvOne
    exact zero_ne_one hvOne
  have hprincipal : ∀ (t : Fin n → ℂ) (s : Fin n → Fin 2), RealTiedMinorScalar.IsPrincipal (PL t s) :=
    fun _ _ => RealTiedMinorProduct.isPrincipal_map_character _
  refine RealPrincipalSeriesScalarDetector.hasScalarCommutant_of_coefficientDetector
    (hprincipal τ e) (hprincipal τ₀ 0) R (isBottom_rows hmono) hshift hQ hJ
    (permutedColumns σ R) v ?_
  intro U hU hUK hUL
  obtain ⟨C, hC, _, hCJacquet⟩ :=
    exists_minimal_isJacquet (R := R) (hBottom := isBottom_rows hmono) (hShift := hshift)
      (hds := hprincipal τ e) (hes := hprincipal τ₀ 0) U hU hUK hUL
  obtain ⟨hCv, hsign⟩ := spherical_jacquet hchamber hvK hv₀ hC hCJacquet
  have hCpar (i : Fin n) : (e (σ i)).val = columnWeight C i % 2 := by
    have h := congrArg Fin.val (congrFun hsign i)
    change ((e (σ i)).val + columnWeight C i) % 2 = 0 at h
    have hval := (e (σ i)).isLt
    omega
  have hparams := RealJacquetParameterSeparation.multiset_eq_of_principal hC hCJacquet
  have hnormalize : RealJacquetFrobenius.expo
      (fun j => jacquetExponent (τ ∘ σ) j - (columnWeight C j : ℂ)) =
      fun i => τ (σ i) - (columnWeight C i : ℂ) := by
    funext i
    simp only [RealJacquetFrobenius.expo, jacquetExponent, Function.comp_apply]
    ring
  rw [hnormalize] at hparams
  obtain ⟨p, hp⟩ := RealMinorWeightBound.exists_perm_of_multiset_eq hparams
  have hm (i : Fin n) : τ (σ i) - (columnWeight C i : ℂ) =
      τ (p i) - (weights (p i) : ℂ) := (hp i).symm
  have hCeq := eq_permutedColumns (r := r) hreal hpar hmono hw horder hR hRweight σ p hm hCpar
  rwa [hCeq] at hCv

end Langlands.Archimedean
