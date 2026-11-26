import Langlands.BaseChange.RegularElementaryJacquetTraceStatement
import Langlands.BaseChange.RegularElementaryTraceReduction
import Langlands.BaseChange.DoubleCosetTwistedTrace
import Langlands.Representation.Jacquet.IwahoriModulusIndex
import Langlands.Representation.Geometric.ParabolicOrbitHaarComparison
import Langlands.Representation.Classification.ProductLeviNecessityTest
import Langlands.Group.GL.BlockContractionProof

/-!
# Iwahori contraction data for the regular elementary double coset

The subgroup with diagonal reduction and a strictly decreasing torus element
satisfy the abstract Iwahori contraction conditions relative to the upper
triangular Borel. The number of cosets of `I ∩ t I t⁻¹` in `I` is `q^{ρ(ν)}`,
and the Haar measure `sphericalHaar E r` on `GL_{r+1}(E)`, normalized by
`μ(GL_{r+1}(O_E)) = 1`, gives `I` the inverse of its index in `GL_{r+1}(O_E)`.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure Langlands.Unramified GeneralLinear.BlockShape
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val torus)
open ClassFieldTheory.Local
open scoped NNReal

universe u

section Modulus

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData) {n : ℕ}
  (C : GeneralLinear.BlockShape n)

/-- The Haar modulus of conjugation by an embedded Levi element on the ambient
upper block radical is the explicit block modulus. -/
theorem closedNormalizerCharacter_unipotentSubgroup_eq_leviModulus (l : C.Levi F.Carrier)
    (g : Subgroup.normalizer (C.unipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)))
    (hg : (g : GeneralLinear n F.Carrier) = C.leviEmbedding F.Carrier l) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    HaarModulus.closedNormalizerCharacter (C.unipotentSubgroup F.Carrier)
        (C.isClosed_unipotentSubgroup F.Carrier) g = T.leviModulus C l := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace (C.unipotentSubgroup F.Carrier) :=
    (C.isClosed_unipotentSubgroup F.Carrier).locallyCompactSpace
  let : MeasurableSpace (C.unipotentRadical F.Carrier) := borel _
  let : BorelSpace (C.unipotentRadical F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (C.unipotentSubgroup F.Carrier) := borel _
  let : BorelSpace (C.unipotentSubgroup F.Carrier) := ⟨rfl⟩
  let a := HaarModulus.normalizerConj (C.unipotentRadical F.Carrier)
    ⟨C.leviInParabolic F.Carrier l, by
      rw [Subgroup.normalizer_eq_top]
      trivial⟩
  let b := HaarModulus.normalizerConj (C.unipotentSubgroup F.Carrier) g
  have hc := Geometric.haarChar_eq_of_conjugacy (C.unipotentRadicalAmbientEquiv F.Carrier)
    a b (by
      intro u
      apply Subtype.ext
      show _ = (g : GeneralLinear n F.Carrier) * _ * (g : GeneralLinear n F.Carrier)⁻¹
      rw [hg]
      rfl)
  apply Units.ext
  change mulEquivHaarChar b = (T.leviModulus C l : ℝ≥0)
  rw [← hc, mulEquivHaarChar_eq haar a]
  have hscale : (haar : Measure (C.unipotentRadical F.Carrier)).map a =
      ((T.leviModulus C l : ℝ≥0)⁻¹) • haar := by
    have ha : (a : C.unipotentRadical F.Carrier → C.unipotentRadical F.Carrier) =
        C.leviAction F.Carrier l := by
      funext u
      apply Subtype.ext
      rfl
    rw [ha]
    exact glBlockModulusHaar p F T n C haar l
  have hs := mul_haarScalarFactor_smul
    (haar : Measure (C.unipotentRadical F.Carrier)) haar
    (c := (T.leviModulus C l : ℝ≥0)⁻¹) (inv_ne_zero (Units.ne_zero _))
  rw! [hscale]
  rw [haarScalarFactor_self] at hs
  exact ((inv_mul_eq_one₀ (Units.ne_zero _)).mp hs).symm

end Modulus

section Regular

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{u} p) {r : ℕ}

private local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n E.Carrier) :=
  E.canonicalGeneralLinearLocallyCompactSpace n

local notation "B" => singletons (r + 1)
local notation "D" => E.canonicalTopologicalData
local notation "G" => GeneralLinear (r + 1) E.Carrier
set_option quotPrecheck false in
local notation "M" => (B).leviSubgroup E.Carrier
set_option quotPrecheck false in
local notation "N" => (B).unipotentSubgroup E.Carrier
set_option quotPrecheck false in
local notation "Nbar" => (B).oppositeUnipotentSubgroup E.Carrier
local notation "I" => regularElementaryCompactOpenSubgroup E r

variable (π : E.Carrierˣ) (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
  (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν)

include hπ in
/-- The normalized absolute value of a power of an order-one unit. -/
theorem normalizedAbs_zpow_of_ord_eq_one (k : ℤ) :
    (D).normalizedAbs (((π ^ k : E.Carrierˣ)) : E.Carrier) =
      ((D).residueCardinality : ℝ) ^ (-k) := by
  rw [(D).normalizedAbs_of_ne_zero (Units.ne_zero _), Units.val_zpow_eq_zpow_val,
    (D).ord_zpow, hπ, mul_one]

include hπ hν in
/-- The weight powers of an order-one unit at a strict weight strictly contract
the upper radical. -/
theorem isStrictlyContracting_weightPowers :
    (B).IsStrictlyContracting D (fun i => π ^ ν i) := by
  intro i j hij
  have hq : (1 : ℝ) < (D).residueCardinality := by exact_mod_cast (D).residueCardinality_gt_one
  rw [GeneralLinear.BlockShape.blockScalarRatio_apply, PadicField.TopologicalData.normalizedAbsUnits_coe,
    show (π ^ ν i * (π ^ ν j)⁻¹ : E.Carrierˣ) = π ^ (ν i - ν j) by rw [_root_.zpow_sub],
    normalizedAbs_zpow_of_ord_eq_one E π hπ]
  apply zpow_lt_one_of_neg₀ hq
  have := hν hij
  linarith

/-- The torus element of any weight lies in the diagonal Levi. -/
theorem torus_mem_leviSubgroup : torus π ν ∈ M :=
  (mem_singletonLevi_iff_diagonalUnits E _).2 ⟨_, rfl⟩

include hπ hν in
/-- The subgroup with diagonal reduction and the torus element of a strict weight
satisfy the abstract Iwahori factorization and contraction conditions. -/
theorem regularElementary_isIwahoriContraction :
    Jacquet.IsIwahoriContraction I N M Nbar (torus π ν) := by
  let h := regularElementaryStrictFiltration E (1 : E.Carrier ≃ₐ[Padic p] E.Carrier) π hπ ν hν
  have hσ : ∀ x : G, (entrywiseAut (1 : E.Carrier ≃ₐ[Padic p] E.Carrier) (r + 1)).symm x = x := by
    intro x
    conv_lhs => rw [← entrywiseAut_one_apply (F := Padic p) x]
    exact MulEquiv.symm_apply_apply _ x
  have htM := torus_mem_leviSubgroup E π ν
  have hl0 : h.level 0 = (I).toSubgroup := h.level_zero
  have hNorm : torus π ν ∈ Subgroup.normalizer (N : Set G) :=
    (B).leviSubgroup_le_normalizer_unipotentSubgroup E.Carrier htM
  have hNormBar : (torus π ν)⁻¹ ∈ Subgroup.normalizer (Nbar : Set G) :=
    (B).leviSubgroup_le_normalizer_oppositeUnipotentSubgroup E.Carrier ((M).inv_mem htM)
  have hlower : ∀ j l, l ∈ h.level j ⊓ Nbar →
      (torus π ν)⁻¹ * l * torus π ν ∈ h.level (j + 1) ⊓ Nbar := by
    intro j l hl
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := h.lower j l hl
      rwa [hσ] at this
    · have := (Subgroup.mem_normalizer_iff.mp hNormBar l).mp hl.2
      simpa only [inv_inv] using this
  refine
    { mem_levi := htM
      factor := ?_
      upper := ?_
      levi := ?_
      lower := ?_
      exhaust := ?_
      contract := ?_ }
  · intro k hk
    have hk' : k ∈ h.level 0 := by rw [hl0]; exact hk
    obtain ⟨l, hl, m, hm, a, ha, he⟩ := h.factor 0 k hk'
    rw [hl0] at hl hm ha
    exact ⟨l, hl, m, hm, a, ha, he⟩
  · intro u hu
    have hu' : u ∈ h.level 0 ⊓ N := by rw [hl0]; exact hu
    exact ⟨h.level_le 1 (h.upper 0 u hu'), (Subgroup.mem_normalizer_iff.mp hNorm u).mp hu.2⟩
  · intro m hm
    obtain ⟨a, ha⟩ := (mem_singletonLevi_iff_diagonalUnits E m).1 hm.2
    have e : (torus π ν)⁻¹ * m * torus π ν = m := by
      rw [ha, torus, ← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
    rw [e]
    exact hm
  · intro l hl
    have hl' : l ∈ h.level 0 ⊓ Nbar := by rw [hl0]; exact hl
    have := hlower 0 l hl'
    exact ⟨h.level_le 1 this.1, this.2⟩
  · intro x hx
    obtain ⟨s, hs⟩ := GeneralLinear.BlockShape.strictPowers_eventually_mem_iwahori (B) D I
      (fun i => π ^ ν i) (isStrictlyContracting_weightPowers E π hπ ν hν) x 1 hx (Nbar).one_mem
    refine ⟨s, ?_⟩
    have := (hs s le_rfl).1
    rw [← GeneralLinear.torus_eq_blockScalar] at this
    exact this.1
  · intro L
    obtain ⟨j, hj⟩ := h.cofinal (L : Set G) (L.isOpen.mem_nhds L.one_mem)
    refine ⟨j, fun l hl => hj ?_⟩
    have key : ∀ s : ℕ, (torus π ν ^ s)⁻¹ * l * torus π ν ^ s ∈ h.level s ⊓ Nbar := by
      intro s
      induction s with
      | zero =>
        rw [hl0]
        simpa using hl
      | succ s ih =>
        have e : (torus π ν ^ (s + 1))⁻¹ * l * torus π ν ^ (s + 1) =
            (torus π ν)⁻¹ * ((torus π ν ^ s)⁻¹ * l * torus π ν ^ s) * torus π ν := by
          group
        rw [e]
        exact hlower s _ ih
    exact (key j).1

include hπ hν in
/-- The Iwahori index of the strict torus element is `q^{ρ(ν)}`. -/
theorem iwahoriIndex_regularElementary :
    ((Jacquet.iwahoriIndex I N (torus π ν) : ℕ) : ℝ) =
      ((D).residueCardinality : ℝ) ^ regularElementaryRho ν := by
  have hc := regularElementary_isIwahoriContraction E π hπ ν hν
  have hNorm : torus π ν ∈ Subgroup.normalizer (N : Set G) :=
    (B).leviSubgroup_le_normalizer_unipotentSubgroup E.Carrier hc.mem_levi
  have hmul := Jacquet.closedNormalizerCharacter_mul_iwahoriIndex
    (regularElementaryCompactOpenSubgroup_isCompact E) ((B).isClosed_unipotentSubgroup E.Carrier)
    hNorm hc.upper
  rw [closedNormalizerCharacter_unipotentSubgroup_eq_leviModulus D (B)
    ((B).blockScalarLevi E.Carrier (fun i => π ^ ν i)) ⟨torus π ν, hNorm⟩
    (GeneralLinear.torus_eq_blockScalar π ν)] at hmul
  have hval := ProductLeviNecessity.leviModulus_blockScalarLevi_of_abs D (B)
    (fun i => π ^ ν i) ν (fun l => normalizedAbs_zpow_of_ord_eq_one E π hπ (ν l))
  have hρ : (∑ l : Fin (B).length, ∑ l' ∈ Finset.univ.filter (fun l' => l < l'),
      (ν l - ν l') * (((B).size l * (B).size l' : ℕ) : ℤ)) = regularElementaryRho ν := by
    simp only [mul_one, Nat.cast_one]
    rfl
  rw [hρ] at hval
  have hmulR := congrArg (fun x : ℝ≥0 => (x : ℝ)) hmul
  simp only [NNReal.coe_mul, NNReal.coe_one, NNReal.coe_natCast] at hmulR
  rw [hval] at hmulR
  have hq : ((D).residueCardinality : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (D).residueCardinality := by exact_mod_cast (D).residueCardinality_gt_one
    positivity
  rw [zpow_neg] at hmulR
  field_simp at hmulR
  linarith

include hπ hν in
/-- The cosets of `I ∩ t I t⁻¹` in `I` number `q^{ρ(ν)}` for the strict torus element `t`. -/
theorem natCard_quotient_regularElementaryConjIntersection :
    ((Nat.card (I ⧸ conjIntersectionSubgroup I (torus π ν)) : ℕ) : ℂ) =
      ((D).residueCardinality : ℂ) ^ regularElementaryRho ν := by
  have hc := regularElementary_isIwahoriContraction E π hπ ν hν
  rw [natCard_quotient_conjIntersectionSubgroup hc
    ((B).leviSubgroup_le_normalizer_unipotentSubgroup E.Carrier)]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (iwahoriIndex_regularElementary E π hπ ν hν)
  simpa only [Complex.ofReal_natCast, Complex.ofReal_zpow] using h

/-- The Haar measure `sphericalHaar E r` on `GL_{r+1}(E)`, normalized by
`μ(GL_{r+1}(O_E)) = 1`, gives the subgroup with diagonal reduction the inverse
of its index in `GL_{r+1}(O_E)`. -/
theorem card_regularElementaryCosets_mul_measure :
    (Fintype.card (RegularElementaryCosets E r) : ℂ) *
      (((sphericalHaar E r) (I : Set G)).toReal : ℂ) = 1 := by
  let K := sphericalOpenSubgroup E r
  have hIK : (I).toSubgroup ≤ K.toSubgroup := regularElementaryCompactOpenSubgroup_le_spherical E
  have : Finite (↥K.toSubgroup ⧸ (I).toSubgroup.subgroupOf K.toSubgroup) :=
    regularElementaryCosetsFinite E r
  have h := Jacquet.relIndex_mul_measure (sphericalHaar E r) (I).toSubgroup K.toSubgroup hIK
    (I).isOpen.measurableSet
  have hK : (sphericalHaar E r) (K : Set G) = 1 :=
    RankinSelberg.normalizedCompactOpenHaar_self _ _
  change _ * _ = (sphericalHaar E r) (K : Set G) at h
  rw [hK] at h
  have hcard : (I).toSubgroup.relIndex K.toSubgroup =
      Fintype.card (RegularElementaryCosets E r) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at h
  have hR := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hR
  exact_mod_cast hR

end Regular

end Langlands.BaseChange
