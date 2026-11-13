import Langlands.ClassFieldTheory.Local.NYLL.InertiaFromGeometricStatement
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedInverseResiduePowerProof
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Mathlib.FieldTheory.Finite.Basic

/-! # The inertia clause from the geometric residue clause -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- Any isomorphism from the actual norm quotient to the actual Galois group
that satisfies the geometric residue clause also satisfies the order-zero
inertia clause. -/
theorem inertiaFromGeometric : InertiaFromGeometricStatement.{u, v} := by
  intro p _ F E _ _ _ TF TE r hgeom σ
  classical
  -- The residue action and the base residue cardinality.
  let ρ := Ramification.Padic.residueHom TE F.Carrier
  let q := TF.residueCardinality
  -- The congruence on the right is the triviality of the residue action.
  have inertia_iff (τ : Gal(E.Carrier/F.Carrier)) :
      ρ τ = 1 ↔ ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation (τ x - x) < 1 := by
    have h := suppliedInverseResiduePower F E TE τ⁻¹ 1
    simp only [map_inv, inv_inv, pow_one] at h
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_symm] at h
    rw [← h]
    constructor
    · intro h1 y
      change ρ τ y = y
      rw [h1]
      rfl
    · intro h1
      ext y
      exact h1 y
  -- Classes of order-one units act on residues as the inverse of the `q`-power map.
  have hfrob (a : F.Carrierˣ) (ha : TF.ord (a : F.Carrier) = 1) (y : TE.ResidueField) :
      (ρ (r (QuotientGroup.mk a)))⁻¹ y = y ^ q :=
    (suppliedInverseResiduePower F E TE (r (QuotientGroup.mk a)) q).mpr (hgeom a ha) y
  -- The chosen uniformizer of the supplied base valuation, as a unit.
  have hπ0 : TF.uniformizer ≠ 0 := by
    intro h
    have h1 := TF.ord_uniformizer
    rw [h, TF.ord_zero] at h1
    exact zero_ne_one h1
  let π : F.Carrierˣ := Units.mk0 TF.uniformizer hπ0
  have hπord : TF.ord (π : F.Carrier) = 1 := TF.ord_uniformizer
  -- Classes of order-zero units act trivially on residues.
  have hzero (a : F.Carrierˣ) (ha : TF.ord (a : F.Carrier) = 0) :
      ρ (r (QuotientGroup.mk a)) = 1 := by
    have hpa : TF.ord ((π * a : F.Carrierˣ) : F.Carrier) = 1 := by
      rw [Units.val_mul, TF.ord_mul π.ne_zero a.ne_zero, hπord, ha, add_zero]
    have heq : (ρ (r (QuotientGroup.mk (π * a))))⁻¹ = (ρ (r (QuotientGroup.mk π)))⁻¹ := by
      ext y
      rw [hfrob _ hpa, hfrob _ hπord]
    rw [inv_inj, QuotientGroup.mk_mul, map_mul, map_mul] at heq
    exact mul_eq_left.mp heq
  -- The residue action of every class is a power of that of the uniformizer.
  have hord (b : F.Carrierˣ) :
      ρ (r (QuotientGroup.mk b)) = (ρ (r (QuotientGroup.mk π))) ^ TF.ord (b : F.Carrier) := by
    have hu : TF.ord ((b * π ^ (-TF.ord (b : F.Carrier)) : F.Carrierˣ) : F.Carrier) = 0 := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val,
        TF.ord_mul b.ne_zero (zpow_ne_zero _ π.ne_zero), TF.ord_zpow, hπord]
      ring
    have h := hzero _ hu
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, map_mul, map_zpow, map_mul, map_zpow,
      zpow_neg] at h
    exact mul_inv_eq_one.mp h
  rw [← inertia_iff σ]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hzero a ha
  · intro hσ
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (r.symm σ)
    have hbσ : r (QuotientGroup.mk b) = σ := by
      rw [hb, MulEquiv.apply_symm_apply]
    let n := TF.ord (b : F.Carrier)
    let g := ρ (r (QuotientGroup.mk π))
    have hgn : g ^ n = 1 := by
      change g ^ TF.ord (b : F.Carrier) = 1
      rw [← hord b, hbσ]
      exact hσ
    -- The inverse of `g` raised to `|n|` is trivial.
    have hgm : g⁻¹ ^ n.natAbs = 1 := by
      have hdvd : (orderOf g : ℤ) ∣ n := orderOf_dvd_iff_zpow_eq_one.mpr hgn
      rw [inv_pow, orderOf_dvd_iff_pow_eq_one.mp (Int.natCast_dvd.mp hdvd), inv_one]
    -- Powers of `g⁻¹` are iterated `q`-power maps.
    have hpow (k : ℕ) (y : TE.ResidueField) : (g⁻¹ ^ k) y = y ^ (q ^ k) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', RingAut.mul_apply, ih, hfrob π hπord, ← pow_mul, ← pow_succ]
    -- Residue-degree divisibility.
    have hdvdE : TE.residueDegree ∣ TF.residueDegree * n.natAbs := by
      have := TE.finite_residueField
      let := Fintype.ofFinite TE.ResidueField
      have hp : p.Prime := Fact.out
      set N := TF.residueDegree * n.natAbs with hN
      have hall : ∀ x : TE.ResidueFieldˣ, x ^ (p ^ N - 1) = 1 := by
        intro x
        have hy : (x : TE.ResidueField) ^ (p ^ N) = x := by
          have h1 := hpow n.natAbs x
          rw [hgm, RingAut.one_apply] at h1
          have hq : q ^ n.natAbs = p ^ N := by
            change TF.residueCardinality ^ n.natAbs = p ^ N
            rw [TF.residueCardinality_eq_pow, ← pow_mul]
          rw [hq] at h1
          exact h1.symm
        have hpos : 1 ≤ p ^ N := Nat.one_le_pow _ _ hp.pos
        have h2 : x ^ (p ^ N - 1) * x = 1 * x := by
          rw [← pow_succ, Nat.sub_add_cancel hpos, one_mul]
          exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy)
        exact mul_right_cancel h2
      have hcard : Fintype.card TE.ResidueField = p ^ TE.residueDegree := by
        rw [← Nat.card_eq_fintype_card]
        exact TE.residueCardinality_eq_pow
      have hdiv := (FiniteField.forall_pow_eq_one_iff TE.ResidueField (p ^ N - 1)).mp hall
      rw [hcard] at hdiv
      have hg := Nat.pow_sub_one_gcd_pow_sub_one p TE.residueDegree N
      rw [Nat.gcd_eq_left hdiv] at hg
      have hpow_eq : p ^ TE.residueDegree = p ^ Nat.gcd TE.residueDegree N :=
        Nat.sub_one_cancel (pow_pos hp.pos _) (pow_pos hp.pos _) hg
      have hexp := Nat.pow_right_injective hp.two_le hpow_eq
      rw [hexp]
      exact Nat.gcd_dvd_right _ _
    -- A norm with the same order as `b`.
    have hdvdZ : (TE.residueDegree : ℤ) ∣ (TF.residueDegree : ℤ) * n := by
      apply Int.natCast_dvd.mpr
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact hdvdE
    obtain ⟨k, hk⟩ := hdvdZ
    obtain ⟨e, he, hek⟩ := TE.ord_surjective_nonzero k
    let c : F.Carrierˣ := Units.map (Algebra.norm F.Carrier (S := E.Carrier)) (Units.mk0 e he)
    have hcmem : c ∈ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range :=
      ⟨Units.mk0 e he, rfl⟩
    have hcord : TF.ord (c : F.Carrier) = n := by
      have h := residueDegree_mul_ord_relative_norm F E TF TE e
      have hfF : (TF.residueDegree : ℤ) ≠ 0 := by exact_mod_cast TF.residueDegree_pos.ne'
      apply mul_left_cancel₀ hfF
      change (TF.residueDegree : ℤ) * TF.ord (Algebra.norm F.Carrier e) = _
      rw [h, hek, ← hk]
    refine ⟨b * c⁻¹, ?_, ?_⟩
    · rw [Units.val_mul, Units.val_inv_eq_inv_val,
        TF.ord_mul b.ne_zero (inv_ne_zero c.ne_zero), TF.ord_inv, hcord]
      exact add_neg_cancel n
    · have hmk : (QuotientGroup.mk (b * c⁻¹) :
          F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range) =
          QuotientGroup.mk b := by
        rw [QuotientGroup.eq]
        have hbc : (b * c⁻¹)⁻¹ * b = c := by group
        rw [hbc]
        exact hcmem
      rw [hmk, hbσ]

end Langlands.LocalClassField.NYLL
