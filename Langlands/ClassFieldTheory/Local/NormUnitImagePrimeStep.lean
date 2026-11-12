import Langlands.ClassFieldTheory.Local.NormUnitImageTower
import Langlands.ClassFieldTheory.Local.PrimeRamificationBreakProof
import Langlands.ClassFieldTheory.Local.PrimeRamifiedNormReductionProof
import Langlands.ClassFieldTheory.Local.UnitNormProof
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport

/-! # Level claims for unramified and for prime-degree abelian extensions

The level claims of `NormUnitImageTower` hold for every unramified finite
abelian extension and for every abelian extension of prime degree.
-/

noncomputable section

namespace Langlands.LocalClassField.NormUnitImage

open Ramification Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime]

section Ceil

/-- If `ψ` is monotone and agrees on naturals with `P`, then
`⌈ψ a⌉₊ ≤ P ⌈a⌉₊`. -/
theorem ceil_le_of_eq_natCast {ψ : ℝ → ℝ} (hψ : Monotone ψ) {P : ℕ → ℕ}
    (hP : ∀ k : ℕ, ψ k = P k) (a : ℝ) : ⌈ψ a⌉₊ ≤ P ⌈a⌉₊ := by
  rw [Nat.ceil_le, ← hP]
  exact hψ (Nat.le_ceil a)

/-- If `ψ` is strictly monotone and agrees on naturals with `P`, then
`P (⌈a⌉₊ - 1) < ⌈ψ a⌉₊` whenever `⌈a⌉₊` is positive. -/
theorem lt_ceil_of_eq_natCast {ψ : ℝ → ℝ} (hψ : StrictMono ψ) {P : ℕ → ℕ}
    (hP : ∀ k : ℕ, ψ k = P k) {a : ℝ} (ha : 0 < ⌈a⌉₊) : P (⌈a⌉₊ - 1) < ⌈ψ a⌉₊ := by
  rw [Nat.lt_ceil, ← hP]
  apply hψ
  have ha0 : 0 ≤ a := (Nat.ceil_pos.mp ha).le
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr ha.ne'), Nat.cast_one]
  linarith [Nat.ceil_lt_add_one ha0]

end Ceil

section Upper

variable {L : PadicField.{v} p} (T : L.TopologicalData) (K : Type u) [Field K]
  [Algebra (Padic p) K] [Algebra K L.Carrier] [IsScalarTower (Padic p) K L.Carrier]

theorem herbrandPsi_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ Padic.herbrandPsi T K a := by
  rw [← Padic.herbrandPsi_zero T K]
  exact (Padic.herbrandPsi_strictMono T K).monotone ha

/-- At a nonnegative level the upper group is the lower group at the natural
ceiling of `ψ(a)`. -/
theorem upperRamificationGroup_eq_lowerRamificationGroup_ceil {a : ℝ} (ha : 0 ≤ a) :
    Padic.upperRamificationGroup T K a =
      Padic.lowerRamificationGroup T K ⌈Padic.herbrandPsi T K a⌉₊ := by
  rw [Padic.upperRamificationGroup_eq_lower, ← Padic.lowerRamificationGroupReal_nat,
    Padic.lowerRamificationGroupReal, Int.ceil_natCast,
    Int.natCast_ceil_eq_ceil (herbrandPsi_nonneg T K ha)]

/-- If all lower groups are trivial, then `ψ(a) = a` for `a ≥ 0`. -/
theorem herbrandPsi_eq_self_of_lower_eq_bot
    (hbot : ∀ i : ℕ, Padic.lowerRamificationGroup T K i = ⊥) {a : ℝ} (ha : 0 ≤ a) :
    Padic.herbrandPsi T K a = a := by
  have horder : ∀ i : ℕ, Padic.lowerGroupOrder T K i = 1 := by
    intro i
    rw [Padic.lowerGroupOrder, hbot i, Subgroup.card_bot]
  have hphi : Padic.herbrandPhi T K a = a := by
    rw [Padic.herbrandPhi_floor T K ha]
    simp only [horder, Nat.cast_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, div_one]
    ring
  have h := Padic.herbrandPsi_herbrandPhi T K a
  rwa [hphi] at h

end Upper

section Unramified

variable (K : PadicField.{u} p) (L : PadicField.{v} p) [Algebra K.Carrier L.Carrier]
  [IsScalarTower (Padic p) K.Carrier L.Carrier] [FiniteDimensional K.Carrier L.Carrier]

-- The instances under which `ArithmeticCoordinate.residueHom_injective` is stated.
local instance : NontriviallyNormedField K.Carrier := K.canonicalNormedField
local instance : NormedAlgebra (Padic p) K.Carrier := K.canonicalNormedAlgebra
local instance : IsUltrametricDist K.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := K.Carrier))
local instance : ProperSpace K.Carrier := FiniteDimensional.proper (Padic p) K.Carrier

/-- In an unramified Galois extension the inertia group is trivial. -/
theorem inertia_eq_bot_of_ramificationIndex_eq [IsGalois K.Carrier L.Carrier]
    (he : K.canonicalTopologicalData.ramificationIndex =
      L.canonicalTopologicalData.ramificationIndex) :
    Padic.inertia L.canonicalTopologicalData K.Carrier = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [← Padic.lowerRamificationGroup_zero, Padic.mem_lowerRamificationGroup] at hσ
  rw [Subgroup.mem_bot]
  apply ClassFieldTheory.Local.ArithmeticCoordinate.residueHom_injective K L he
  rw [map_one]
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  change IsLocalRing.residue _ (LocalGalois.integerAut _ _ σ x) = IsLocalRing.residue _ x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  let e := ClassFieldTheory.Local.ArithmeticCoordinate.extensionIntegerEquiv K L
  have h := hσ (e x)
  rw [zero_add, pow_one] at h
  have heq : e (LocalGalois.integerAut _ _ σ x - x) =
      Padic.integerAutomorphism L.canonicalTopologicalData K.Carrier σ (e x) - e x := by
    rw [map_sub]
    rfl
  rw [← heq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff] at h
  exact h

/-- The level claims for an unramified finite abelian extension. -/
theorem levelClaims_of_ramificationIndex_eq [IsAbelianGalois K.Carrier L.Carrier]
    (he : K.canonicalTopologicalData.ramificationIndex =
      L.canonicalTopologicalData.ramificationIndex) :
    LevelClaims K L := by
  intro a ha
  have hbot : ∀ i : ℕ, Padic.lowerRamificationGroup L.canonicalTopologicalData K.Carrier i = ⊥ := by
    intro i
    rw [eq_bot_iff, ← inertia_eq_bot_of_ramificationIndex_eq K L he,
      ← Padic.lowerRamificationGroup_zero]
    exact Padic.lowerRamificationGroup_antitone _ _ (Nat.zero_le i)
  rw [herbrandPsi_eq_self_of_lower_eq_bot _ _ hbot ha,
    upperRamificationGroup_eq_lowerRamificationGroup_ceil _ _ ha, hbot, Subgroup.card_bot,
    mul_one, unramifiedUnitNorms p K L _ _ he]
  refine ⟨le_rfl, by rw [Subgroup.relIndex_self], ?_⟩
  rw [← normSubgroup_index_eq_finrank K L]
  exact Subgroup.index_dvd_of_le le_sup_right

end Unramified

section Prime

variable (K : PadicField.{u} p) (L : PadicField.{v} p) [Algebra K.Carrier L.Carrier]
  [IsScalarTower (Padic p) K.Carrier L.Carrier] [FiniteDimensional K.Carrier L.Carrier]

/-- A prime-degree extension is unramified or totally ramified. -/
theorem ramificationIndex_eq_or_of_prime (hℓ : (Module.finrank K.Carrier L.Carrier).Prime) :
    K.canonicalTopologicalData.ramificationIndex =
        L.canonicalTopologicalData.ramificationIndex ∨
      L.canonicalTopologicalData.ramificationIndex =
        Module.finrank K.Carrier L.Carrier * K.canonicalTopologicalData.ramificationIndex := by
  set TK := K.canonicalTopologicalData
  set TL := L.canonicalTopologicalData
  set ℓ := Module.finrank K.Carrier L.Carrier
  have h1 := ramificationIndex_mul_ord_relative_algebraMap K L TK TL TK.uniformizer
  rw [TK.ord_uniformizer, mul_one] at h1
  have h2 := PadicField.ramificationIndex_mul_extensionResidueDegree K L
    (IsScalarTower.toAlgHom (Padic p) K.Carrier L.Carrier)
  rw [extensionDegree_suppliedAlgebra] at h2
  set c := TL.ord (algebraMap K.Carrier L.Carrier TK.uniformizer)
  set f := extensionResidueDegree K L (IsScalarTower.toAlgHom (Padic p) K.Carrier L.Carrier)
  have heK : (0 : ℤ) < TK.ramificationIndex := by exact_mod_cast TK.ramificationIndex_pos
  have hcf : c * f = ℓ := by
    have h3 : (TK.ramificationIndex : ℤ) * (c * f) = TK.ramificationIndex * ℓ := by
      have h2' : ((TL.ramificationIndex * f : ℕ) : ℤ) = ((ℓ * TK.ramificationIndex : ℕ) : ℤ) := by
        rw [h2]
      push_cast at h2'
      rw [← mul_assoc, h1, h2', mul_comm]
    exact mul_left_cancel₀ heK.ne' h3
  have hc0 : 0 < c := by
    by_contra hc
    have : c * f ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (Int.natCast_nonneg f)
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
    omega
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hc0.le
  rw [hd] at hcf h1
  have hdf : d * f = ℓ := by exact_mod_cast hcf
  rcases hℓ.eq_one_or_self_of_dvd d ⟨f, hdf.symm⟩ with hd' | hd'
  · left
    have : (TL.ramificationIndex : ℤ) = TK.ramificationIndex := by rw [← h1, hd']; ring
    exact_mod_cast this.symm
  · right
    have : (TL.ramificationIndex : ℤ) = ℓ * TK.ramificationIndex := by rw [← h1, hd']; ring
    exact_mod_cast this

/-- In characteristic `p`, a unit whose `p`th power is one is one. -/
theorem units_eq_one_of_pow_char_eq_one {k : Type*} [Field k] [CharP k p] {ξ : kˣ}
    (h : ξ ^ p = 1) : ξ = 1 := by
  apply Units.ext
  have h' : ((ξ : k) - 1) ^ p = 0 := by
    rw [sub_pow_char, ← Units.val_pow_eq_pow_val, h, Units.val_one, one_pow, sub_self]
  rw [Units.val_one, ← sub_eq_zero]
  exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h'

/-- The level claims for a totally ramified abelian extension of prime degree. -/
theorem levelClaims_of_totallyRamified [IsAbelianGalois K.Carrier L.Carrier]
    (hℓ : (Module.finrank K.Carrier L.Carrier).Prime)
    (htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank K.Carrier L.Carrier * K.canonicalTopologicalData.ramificationIndex) :
    LevelClaims K L := by
  set TK := K.canonicalTopologicalData
  set TL := L.canonicalTopologicalData
  set ℓ := Module.finrank K.Carrier L.Carrier
  set N := normUnits K.Carrier L.Carrier
  obtain ⟨t, hlow, htp, hψnat⟩ := primeTotallyRamifiedBreak p K L hℓ htot
  obtain ⟨hR1, hR2, hR3⟩ := primeRamifiedNormReduction p K L hℓ htot t hlow
  obtain ⟨-, hG2, -, hG4, hG5⟩ := primeRamifiedGradedNorm p K L hℓ htot t hlow
  set P : ℕ → ℕ := fun k => if k ≤ t then k else t + ℓ * (k - t) with hPdef
  have hP : ∀ k : ℕ, Padic.herbrandPsi TL K.Carrier k = P k := hψnat
  intro a ha
  have hupper := upperRamificationGroup_eq_lowerRamificationGroup_ceil TL K.Carrier ha
  have hmle := ceil_le_of_eq_natCast (Padic.herbrandPsi_strictMono TL K.Carrier).monotone hP a
  have hmgt := fun h => lt_ceil_of_eq_natCast (Padic.herbrandPsi_strictMono TL K.Carrier) hP
    (a := a) h
  set n := ⌈a⌉₊
  set m := ⌈Padic.herbrandPsi TL K.Carrier a⌉₊
  rw [hupper]
  rcases le_or_gt n t with hnt | htn
  · -- Below the break: `m = n` and the upper group is everything.
    have hPn : P n = n := ite_eq_left hnt
    have hm : m = n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · rw [hPn, hn] at hmle
        omega
      · have h1 := hmgt hn
        have hP1 : P (n - 1) = n - 1 := ite_eq_left (by omega)
        rw [hPn] at hmle
        rw [hP1] at h1
        omega
    rw [hm, hlow n, ite_eq_left hnt, Subgroup.card_top, IsGalois.card_aut_eq_finrank]
    have hC : (TL.unitFiltration n).map N ≤ TK.unitFiltration n := by
      rintro _ ⟨x, hx, rfl⟩
      have h := hG2 n ⟨x, by rw [show P n = n from hPn]; exact hx⟩
      simpa only [hPn] using h
    -- A unit of level `k ≤ t` whose norm has level `k` already has level `k`.
    have hlift : ∀ k : ℕ, k ≤ t → ∀ y : L.Carrierˣ, N y ∈ TK.unitFiltration k →
        y ∈ TL.unitFiltration k := by
      intro k
      induction k with
      | zero =>
        intro _ y hy
        rw [TK.unitFiltration_zero] at hy
        have h0 := (ClassFieldTheory.Local.mem_unitSubgroup_iff_ord_eq_zero K TK (N y)).mp hy
        rw [PrimeRamifiedNormReductionProof.ord_normUnits_of_totalRamification K L hℓ.pos htot]
          at h0
        exact TL.mem_unitFiltration_zero_of_ord_eq_zero y h0
      | succ k ih =>
        intro hk y hy
        have hNk : N y ∈ TK.unitFiltration k := TK.unitFiltration_antitone (Nat.le_succ k) hy
        have hyk : y ∈ TL.unitFiltration k := ih (by omega) y hNk
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · have hz := hG4 ⟨y, hyk⟩ ⟨N y, hNk⟩ rfl
          have h1 : TK.zeroUnitCoordinate ⟨N y, hNk⟩ = 1 := by
            rw [← MonoidHom.mem_ker, TK.zeroUnitCoordinate_ker]
            exact hy
          rw [h1, map_one] at hz
          have hℓp : Module.finrank K.Carrier L.Carrier = p := htp.mp (by omega)
          rw [hℓp] at hz
          let := TL.residueCharP
          have hξ := units_eq_one_of_pow_char_eq_one hz.symm
          have hker : (⟨y, hyk⟩ : TL.unitFiltration 0) ∈ TL.zeroUnitCoordinate.ker := hξ
          rw [TL.zeroUnitCoordinate_ker] at hker
          exact hker
        · obtain ⟨c, -, hc0, hcoef⟩ := (hG5 TK.uniformizer TK.ord_uniformizer TL.uniformizer
            TL.ord_uniformizer).1 k hk0 (by omega)
          have h := hcoef ⟨y, hyk⟩ ⟨N y, hNk⟩ rfl
          rw [(TK.residue_unitCoefficient_eq_zero_iff _ _ k _).mpr hy, map_zero] at h
          have hr := (map_ne_zero (PadicField.TopologicalData.relativeResidueMap TK TL)).mpr hc0
          have h' := (mul_eq_zero.mp h.symm).resolve_left hr
          exact (TL.residue_unitCoefficient_eq_zero_iff _ _ k _).mp
            ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp h')
    have hV : TK.unitFiltration n ⊓ normSubgroup K.Carrier L.Carrier ≤
        (TL.unitFiltration n).map N := by
      rintro x ⟨hxU, y, rfl⟩
      exact ⟨y, hlift n hnt y hxU, rfl⟩
    have heq : (TL.unitFiltration n).map N = TK.unitFiltration n ⊓ normSubgroup K.Carrier L.Carrier :=
      le_antisymm (le_inf hC (Subgroup.map_le_range _ _)) hV
    have hsup : TK.unitFiltration n ⊔ normSubgroup K.Carrier L.Carrier = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, z, hxz⟩ := hR3 x
      rw [hxz, mul_comm]
      exact Subgroup.mul_mem_sup (TK.unitFiltration_antitone hnt z.2) ⟨y, rfl⟩
    refine ⟨hC, ?_, ?_⟩
    · rw [heq, Subgroup.inf_relIndex_left, ← normSubgroup_index_eq_finrank K L]
      exact Subgroup.relIndex_dvd_index_of_normal _ _
    · rw [hsup, Subgroup.index_top, one_mul]
  · -- Above the break: the upper group is trivial and `N(U_L^m) = U_K^n`.
    have hn : 0 < n := by omega
    have h1 := hmgt hn
    have hPt : t ≤ P (n - 1) := by
      simp only [hPdef]
      split_ifs <;> omega
    rw [hlow m, ite_eq_right (by omega), Subgroup.card_bot, mul_one]
    have heq : (TL.unitFiltration m).map N = TK.unitFiltration n := by
      apply le_antisymm
      · calc (TL.unitFiltration m).map N ≤ (TL.unitFiltration (P (n - 1) + 1)).map N :=
              Subgroup.map_mono (TL.unitFiltration_antitone h1)
          _ = TK.unitFiltration (n - 1 + 1) := hR2 (n - 1) (by omega)
          _ = TK.unitFiltration n := by rw [Nat.sub_add_cancel hn]
      · calc TK.unitFiltration n = (TL.unitFiltration (P n)).map N := (hR1 n htn).symm
          _ ≤ (TL.unitFiltration m).map N :=
              Subgroup.map_mono (TL.unitFiltration_antitone hmle)
    rw [heq]
    refine ⟨le_rfl, by rw [Subgroup.relIndex_self], ?_⟩
    rw [← normSubgroup_index_eq_finrank K L]
    exact Subgroup.index_dvd_of_le le_sup_right

/-- The level claims for an abelian extension of prime degree. -/
theorem levelClaims_of_prime [IsAbelianGalois K.Carrier L.Carrier]
    (hℓ : (Module.finrank K.Carrier L.Carrier).Prime) : LevelClaims K L := by
  rcases ramificationIndex_eq_or_of_prime K L hℓ with he | htot
  · exact levelClaims_of_ramificationIndex_eq K L he
  · exact levelClaims_of_totallyRamified K L hℓ htot

end Prime

end Langlands.LocalClassField.NormUnitImage
