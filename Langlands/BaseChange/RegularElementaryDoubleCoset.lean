import Langlands.BaseChange.RegularElementaryOrbit
import Langlands.Group.GL.LeviCongruenceSubgroup
import Langlands.Group.GL.ParabolicQuotient
import Langlands.Group.GL.PrincipalLevelDominance
import Langlands.Group.GL.StrictPrincipalContraction
import Langlands.LocalFactor.Abelian.ZetaAnalysisHelpers
import Langlands.Representation.Jacquet.ContractingDoubleCoset
import Langlands.Representation.Unramified.StandardHeckeSum

/-! # Double coset for a regular elementary test -/

noncomputable section

namespace Langlands.BaseChange

open Filter _root_.Topology Matrix Langlands.Unramified Langlands.Conductor
open Langlands.Jacquet LocalFactor.PadicAbelian
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val torus IsUniformizingElement)
open Conductor.SphericalCyclicity (mem_principalLevelSubgroup_iff)
open scoped WithZero

universe u

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{u} p) {r : ℕ}

local notation "D" => E.canonicalTopologicalData
local notation "L" => GeneralLinear (r + 1) E.Carrier
local notation "B" => GeneralLinear.BlockShape.singletons (r + 1)
local notation "J" => principalLevelSubgroup E.Carrier r
set_option quotPrecheck false in
local notation "M" => (B).leviSubgroup E.Carrier
set_option quotPrecheck false in
local notation "N" => (B).unipotentSubgroup E.Carrier
set_option quotPrecheck false in
local notation "Nbar" => (B).oppositeUnipotentSubgroup E.Carrier
local notation "v" => ValuativeRel.valuation E.Carrier
local notation "ε" => IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E.Carrier

/-- The compact open subgroup whose reduction is the diagonal torus. -/
def regularElementaryCompactOpenSubgroup (rank : ℕ) :
    OpenSubgroup (GeneralLinear (rank + 1) E.Carrier) :=
  (GeneralLinear.BlockShape.singletons (rank + 1)).leviCongruenceOpenSubgroup E.Carrier

set_option quotPrecheck false in
local notation "I" => (regularElementaryCompactOpenSubgroup E r).toSubgroup

theorem regularElementaryCompactOpenSubgroup_le_spherical :
    I ≤ (sphericalOpenSubgroup E r).toSubgroup := by
  have h := (B).leviCongruenceSubgroup_le_integral E.Carrier
  rwa [principalLevelSubgroup_zero] at h

theorem regularElementaryCompactOpenSubgroup_isCompact :
    IsCompact (regularElementaryCompactOpenSubgroup E r : Set L) :=
  (B).isCompact_leviCongruenceOpenSubgroup E.Carrier

theorem mem_singletonLevi_iff_diagonalUnits (x : L) :
    x ∈ M ↔ ∃ a : Fin (r + 1) → E.Carrierˣ, x = diagonalUnits a := by
  constructor
  · intro hx
    have hOff (i j : Fin (r + 1)) (hij : i ≠ j) : x i j = 0 := by
      obtain ⟨m, rfl⟩ := hx
      have h := (B).leviEmbedding_apply_ne E.Carrier m (0 : Fin 1) (0 : Fin 1) hij
      have hi : (B).index i (0 : Fin 1) = i := GeneralLinear.BlockShape.singletons_index i 0
      have hj : (B).index j (0 : Fin 1) = j := GeneralLinear.BlockShape.singletons_index j 0
      rwa [hi, hj] at h
    have hxdiag : x.val = diagonal (fun i => x i i) := by
      ext i j
      by_cases h : i = j
      · subst j; simp
      · simp [h, hOff i j h]
    have hdiag (i : Fin (r + 1)) : x i i ≠ 0 := by
      intro hi
      have hn : x.val.det ≠ 0 := (GeneralLinear.determinant x).ne_zero
      rw [hxdiag, det_diagonal] at hn
      exact hn (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    exact ⟨fun i => Units.mk0 (x i i) (hdiag i), Units.ext (by
      rw [diagonalUnits_val]
      exact hxdiag)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨GeneralLinear.BlockShape.singletonLevi E.Carrier a, Units.ext ?_⟩
    exact GeneralLinear.BlockShape.leviEmbedding_singletonLevi_val E.Carrier a

theorem diagonalUnits_mem_regularElementaryCompactOpenSubgroup {a : Fin (r + 1) → E.Carrierˣ}
    (ha : diagonalUnits a ∈ sphericalOpenSubgroup E r) :
    diagonalUnits a ∈ regularElementaryCompactOpenSubgroup E r := by
  have hM := (mem_singletonLevi_iff_diagonalUnits E (diagonalUnits a)).2 ⟨a, rfl⟩
  have hJ : diagonalUnits a ∈ J 0 := by rwa [principalLevelSubgroup_zero]
  exact ((B).mem_leviCongruenceSubgroup_iff E.Carrier _).2 ⟨_, ⟨hJ, hM⟩, 1, one_mem _, by simp⟩

private theorem orderOne_isUniformizing {π : E.Carrierˣ} (hπ : (D).ord (π : E.Carrier) = 1) :
    IsUniformizingElement v π := by
  have hval : v (π : E.Carrier) = v ((D).uniformizerUnit : E.Carrier) := by
    apply (ε).injective
    change (D).discreteValuation (π : E.Carrier) = (D).discreteValuation ((D).uniformizerUnit : E.Carrier)
    rw [discreteValuation_eq_exp_neg_ord D π.ne_zero, hπ,
      discreteValuation_eq_exp_neg_ord D (D).uniformizerUnit.ne_zero]
    change WithZero.exp (-(1 : ℤ)) = WithZero.exp (-(D).ord (D).uniformizer)
    rw [(D).ord_uniformizer]
  unfold IsUniformizingElement
  rw [hval]
  exact uniformizerUnit_isUniformizingElement E

variable (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)

local notation "τG" => entrywiseAut τ (r + 1)

private theorem valuation_algEquiv (x : E.Carrier) : v (τ x) = v x := by
  apply (ε).injective
  change (D).discreteValuation (τ x) = (D).discreteValuation x
  by_cases hx : x = 0
  · simp [hx]
  rw [discreteValuation_eq_exp_neg_ord D ((map_ne_zero τ).mpr hx),
    discreteValuation_eq_exp_neg_ord D hx, LocalClassField.NYLL.ord_eq_of_algEquiv τ D D]

theorem entrywiseAut_mem_principalLevel_iff (π : E.Carrierˣ) (hπ : IsUniformizingElement v π)
    (a : ℕ) (g : L) : τG g ∈ J a ↔ g ∈ J a := by
  rw [mem_principalLevelSubgroup_iff hπ, mem_principalLevelSubgroup_iff hπ, ← map_inv]
  have he (x : L) (i j : Fin (r + 1)) :
      v (τG x i j - (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E.Carrier) i j) =
        v (x i j - (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E.Carrier) i j) := by
    rw [entrywiseAut_apply_apply, ← valuation_algEquiv E τ (x i j - _), map_sub τ]
    congr 2
    simp [Matrix.one_apply]
  simp only [he]

private theorem entrywiseAut_mem_singletonLevi {g : L} (hg : g ∈ M) : τG g ∈ M := by
  obtain ⟨a, rfl⟩ := (mem_singletonLevi_iff_diagonalUnits E g).mp hg
  refine (mem_singletonLevi_iff_diagonalUnits E _).2 ⟨fun i => Units.map τ.toRingHom (a i), ?_⟩
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalUnits_val]
  · simp [diagonalUnits_val, h]

private theorem entrywiseAut_mem_oppositeUnipotent {g : L} (hg : g ∈ Nbar) : τG g ∈ Nbar := by
  obtain ⟨hP, hd⟩ := ((B).mem_oppositeUnipotentSubgroup_iff E.Carrier g).mp hg
  refine ((B).mem_oppositeUnipotentSubgroup_iff E.Carrier _).mpr ⟨?_, ?_⟩
  · apply ((B).mem_oppositeParabolic_iff E.Carrier _).mpr
    intro i j a b hij
    simp only [entrywiseAut_apply_apply, ((B).mem_oppositeParabolic_iff E.Carrier _).mp hP i j a b hij,
      map_zero]
  · intro i a b
    rw [entrywiseAut_apply_apply, hd]
    by_cases h : a = b <;> simp [h]

theorem entrywiseAut_mem_regularElementaryCompactOpenSubgroup
    (π : E.Carrierˣ) (hπ : IsUniformizingElement v π) (g : L) (hg : g ∈ I) :
    τG g ∈ I := by
  obtain ⟨m, hm, w, hw, rfl⟩ := ((B).mem_leviCongruenceSubgroup_iff E.Carrier g).mp hg
  exact ((B).mem_leviCongruenceSubgroup_iff E.Carrier _).2
    ⟨τG m, ⟨(entrywiseAut_mem_principalLevel_iff E τ π hπ 0 m).2 hm.1,
      entrywiseAut_mem_singletonLevi E τ hm.2⟩,
      τG w, (entrywiseAut_mem_principalLevel_iff E τ π hπ 1 w).2 hw, map_mul _ _ _⟩

private theorem strict_ratio_le {π : E.Carrierˣ} (hπ : IsUniformizingElement v π)
    {ν : Fin (r + 1) → ℤ} (hν : StrictAnti ν) (i j : Fin (r + 1)) (hij : i < j) :
    v ((π ^ ν i * (π ^ ν j)⁻¹ : E.Carrierˣ) : E.Carrier) ≤ v (π : E.Carrier) := by
  have hν' := hν hij
  have he : (π ^ ν i * (π ^ ν j)⁻¹ : E.Carrierˣ) = π ^ (ν i - ν j) := by
    rw [_root_.zpow_sub]
  rw [he, Units.val_zpow_eq_zpow_val, map_zpow₀]
  conv_rhs => rw [← zpow_one (v (π : E.Carrier))]
  apply (zpow_right_strictAnti₀ (GeneralLinear.Iwasawa.valuation_pos v π) hπ.1).antitone
  omega

/-- The torus translate at a strict weight has a cofinal Iwahori filtration
starting with the inverse image of the diagonal torus in reduction. -/
def regularElementaryStrictFiltration (π : E.Carrierˣ) (hπ : (D).ord (π : E.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    StrictIwahoriFiltration I N M Nbar (torus π ν) τG := by
  let level : ℕ → Subgroup L
    | 0 => I
    | j + 1 => J (j + 1)
  have hp := orderOne_isUniformizing E hπ
  refine {
    level := level
    level_zero := rfl
    level_le := ?_
    normalizes := ?_
    stable := ?_
    cofinal := ?_
    factor := ?_
    upper := ?_
    lower := ?_ }
  · intro j
    cases j with
    | zero => exact le_rfl
    | succ j =>
      exact (principalLevelSubgroup_antitone E.Carrier r j.succ_pos).trans
        ((B).principalLevel_le_leviCongruenceSubgroup E.Carrier)
  · intro j
    cases j with
    | zero => exact Subgroup.le_normalizer
    | succ j =>
      exact ((B).leviCongruenceSubgroup_le_integral E.Carrier).trans
        (GeneralLinear.BlockShape.integral_le_normalizer_principalLevel E.Carrier (j + 1))
  · intro j g
    cases j with
    | zero =>
      exact ⟨fun hg => by
        have h := entrywiseAut_mem_regularElementaryCompactOpenSubgroup E τ.symm π hp (τG g) hg
        exact ((τG).symm_apply_apply g) ▸ h,
        entrywiseAut_mem_regularElementaryCompactOpenSubgroup E τ π hp g⟩
    | succ j => exact entrywiseAut_mem_principalLevel_iff E τ π hp (j + 1) g
  · intro U hU
    obtain ⟨a, ha, hAU⟩ := exists_pos_principalLevelOpenSubgroup_subset E.Carrier r hU
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    exact ⟨j + 1, hAU⟩
  · intro j g hg
    cases j with
    | zero => exact (B).exists_leviCongruence_factor E.Carrier hg
    | succ j => exact (B).exists_principalLevel_factor E.Carrier (j + 1) j.succ_pos hg
  · intro j g hg
    have hc {a : ℕ} (h : g ∈ J a ⊓ N) :
        torus π ν * g * (torus π ν)⁻¹ ∈ J (a + 1) := by
      rw [GeneralLinear.torus_eq_blockScalar]
      exact (B).upper_conj_mem_principalLevel_succ hp _ (strict_ratio_le E hp hν) h
    cases j with
    | zero =>
      change g ∈ (B).leviCongruenceSubgroup E.Carrier ⊓ N at hg
      rw [(B).leviCongruenceSubgroup_inf_upper E.Carrier] at hg
      exact principalLevelSubgroup_antitone E.Carrier r (by decide : 1 ≤ 1 + 1) (hc hg)
    | succ j => exact hc hg
  · intro j g hg
    have hc {a : ℕ} (h : g ∈ J a ⊓ Nbar) :
        (torus π ν)⁻¹ * (τG).symm g * torus π ν ∈ J (a + 1) := by
      rw [GeneralLinear.torus_eq_blockScalar]
      exact (B).lower_inv_conj_mem_principalLevel_succ hp _ (strict_ratio_le E hp hν)
        ⟨(entrywiseAut_mem_principalLevel_iff E τ.symm π hp a g).2 h.1,
          entrywiseAut_mem_oppositeUnipotent E τ.symm h.2⟩
    cases j with
    | zero =>
      change g ∈ (B).leviCongruenceSubgroup E.Carrier ⊓ Nbar at hg
      rw [(B).leviCongruenceSubgroup_inf_lower E.Carrier] at hg
      exact principalLevelSubgroup_antitone E.Carrier r (by decide : 1 ≤ 1 + 1) (hc hg)
    | succ j => exact hc hg

/-- The smaller compact double coset is the saturation of the weighted
integral diagonal units under the reduction-diagonal subgroup. -/
theorem regularElementary_doubleCoset_eq_twistedDiagonalSaturation (π : E.Carrierˣ)
    (hπ : (D).ord (π : E.Carrier) = 1) (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    DoubleCoset.doubleCoset (torus π ν) (I : Set L) (I : Set L) =
      twistedDiagonalSaturation τ I (elementaryDiagonalTuples E π ν) := by
  let h := regularElementaryStrictFiltration E τ π hπ ν hν
  have hM : IsCompact ((I ⊓ M : Subgroup L) : Set L) := by
    let := (D).fieldT2
    exact (regularElementaryCompactOpenSubgroup_isCompact E).inter_right
      ((B).isClosed_leviSubgroup E.Carrier)
  have hτ : Continuous τG := by
    let := E.canonicalNormedField
    let := E.canonicalNormedAlgebra
    exact (Weil.Local.extension_isometry E E τ.toAlgHom).continuous.generalLinearGroup_map
  rw [h.doubleCoset_eq_twistedLeviSaturation ((B).leviSubgroup_le_normalizer_unipotentSubgroup
    E.Carrier) (regularElementaryCompactOpenSubgroup_isCompact E) hM hτ]
  ext g
  constructor
  · rintro ⟨i, hi, m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_singletonLevi_iff_diagonalUnits E m).1 hm.2
    have ha := (diagonalUnits_mem_sphericalOpenSubgroup_iff E a).1
      (regularElementaryCompactOpenSubgroup_le_spherical E hm.1)
    refine ⟨i, hi, (fun j => π ^ ν j * a j), fun j _ => ⟨a j, ?_, rfl⟩, ?_⟩
    · exact (ClassFieldTheory.Local.mem_unitSubgroup_iff_ord_eq_zero E D _).2 (ha j)
    · change i⁻¹ * diagonalUnits ((fun j => π ^ ν j) * a) * τG i = _
      rw [map_mul, ← mul_assoc]
      rfl
  · rintro ⟨i, hi, a, ha, rfl⟩
    have hfactor (j : Fin (r + 1)) := ha j (Set.mem_univ j)
    choose m hm he using hfactor
    have hEq : diagonalUnits a = torus π ν * diagonalUnits m := by
      rw [torus, ← map_mul]
      exact congrArg (fun z : Fin (r + 1) → E.Carrierˣ => diagonalUnits z) (funext fun j => (he j).symm)
    have hmem : diagonalUnits m ∈ sphericalOpenSubgroup E r :=
      (diagonalUnits_mem_sphericalOpenSubgroup_iff E m).2
        fun j => (ClassFieldTheory.Local.mem_unitSubgroup_iff_ord_eq_zero E D _).1 (hm j)
    exact ⟨i, hi, diagonalUnits m, ⟨diagonalUnits_mem_regularElementaryCompactOpenSubgroup E hmem,
      (mem_singletonLevi_iff_diagonalUnits E _).2 ⟨m, rfl⟩⟩, by rw [hEq, mul_assoc i⁻¹]⟩

/-- Double-coset support identity for p-adic fields at a strict weight. -/
def RegularElementaryDoubleCosetStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) (r : ℕ)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ)
    (_ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ), StrictAnti ν →
    let C := (regularElementaryCompactOpenSubgroup E r).toSubgroup
    DoubleCoset.doubleCoset (torus π ν) (C : Set _) (C : Set _) =
      twistedDiagonalSaturation τ C (elementaryDiagonalTuples E π ν)

theorem regularElementaryDoubleCoset : RegularElementaryDoubleCosetStatement.{u} :=
  fun _ _ E _ τ π hπ ν hν => regularElementary_doubleCoset_eq_twistedDiagonalSaturation E τ π hπ ν hν

end Langlands.BaseChange
