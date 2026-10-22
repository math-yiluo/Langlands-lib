import Langlands.ClassFieldTheory.Local.NormCompatibilityStatement
import Langlands.LocalField.Normalization.Proof
import Langlands.ClassFieldTheory.Local.Norms

namespace Langlands.LocalClassField

open IntermediateField

universe u v

private theorem norm_fieldNorm_eq_spectralNorm_pow
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) :
    ‖Algebra.norm K x‖ = spectralNorm K L x ^ Module.finrank K L := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hpow : spectralNorm K L x ^ (minpoly K x).natDegree =
      ‖(minpoly K x).coeff 0‖ := by
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div]
    exact Real.rpow_inv_natCast_pow (norm_nonneg _) (minpoly.natDegree_pos hx).ne'
  rw [Algebra.norm_eq_norm_adjoin K x, norm_pow,
    ← adjoin.powerBasis_gen hx, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    adjoin.powerBasis_gen, minpoly_gen]
  rw [← hpow, ← pow_mul, ← adjoin.finrank hx, Module.finrank_mul_finrank K K⟮x⟯ L]

variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (E : PadicField.{v} p)
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable [FiniteDimensional F.Carrier E.Carrier]
variable (TF : F.TopologicalData) (TE : E.TopologicalData)

theorem normalizedAbs_relative_norm (x : E.Carrier) :
    TF.normalizedAbs (Algebra.norm F.Carrier x) = TE.normalizedAbs x := by
  rw [TF.normalizedAbs_eq_canonicalNorm_pow_degree,
    TE.normalizedAbs_eq_canonicalNorm_pow_degree]
  change spectralNorm (Padic p) F.Carrier (Algebra.norm F.Carrier x) ^ _ =
    spectralNorm (Padic p) E.Carrier x ^ _
  rw [← norm_fieldNorm_eq_spectralNorm_pow, ← norm_fieldNorm_eq_spectralNorm_pow,
    Algebra.norm_norm]

theorem normalizedAbs_relative_algebraMap (x : F.Carrier) :
    TE.normalizedAbs (algebraMap F.Carrier E.Carrier x) =
      TF.normalizedAbs x ^ Module.finrank F.Carrier E.Carrier := by
  rw [TE.normalizedAbs_eq_canonicalNorm_pow_degree,
    TF.normalizedAbs_eq_canonicalNorm_pow_degree, ← pow_mul,
    Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier]
  change spectralNorm (Padic p) E.Carrier (algebraMap F.Carrier E.Carrier x) ^ _ =
    spectralNorm (Padic p) F.Carrier x ^ _
  rw [← spectralNorm.eq_of_tower]

private theorem normalizedAbs_eq_prime_zpow
    {G : PadicField p} (T : G.TopologicalData) {x : G.Carrier} (hx : x ≠ 0) :
    T.normalizedAbs x = (p : ℝ) ^ (-((T.residueDegree : ℤ) * T.ord x)) := by
  rw [T.normalizedAbs_of_ne_zero hx, T.residueCardinality_eq_pow,
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem residueDegree_mul_ord_relative_norm (x : E.Carrier) :
    (TF.residueDegree : ℤ) * TF.ord (Algebra.norm F.Carrier x) =
      (TE.residueDegree : ℤ) * TE.ord x := by
  by_cases hx : x = 0
  · simp [hx, Algebra.norm_zero, TF.ord_zero, TE.ord_zero]
  have hn : Algebra.norm F.Carrier x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have h := normalizedAbs_relative_norm F E TF TE x
  rw [normalizedAbs_eq_prime_zpow TF hn, normalizedAbs_eq_prime_zpow TE hx] at h
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact neg_injective ((zpow_right_inj₀ (lt_trans zero_lt_one hp) (ne_of_gt hp)).mp h)

theorem ramificationIndex_mul_ord_relative_algebraMap (x : F.Carrier) :
    (TF.ramificationIndex : ℤ) * TE.ord (algebraMap F.Carrier E.Carrier x) =
      (TE.ramificationIndex : ℤ) * TF.ord x := by
  by_cases hx : x = 0
  · simp [hx, TF.ord_zero, TE.ord_zero]
  have hm : algebraMap F.Carrier E.Carrier x ≠ 0 := (map_ne_zero _).mpr hx
  have h := normalizedAbs_relative_algebraMap F E TF TE x
  rw [normalizedAbs_eq_prime_zpow TE hm, normalizedAbs_eq_prime_zpow TF hx,
    ← zpow_natCast, ← zpow_mul] at h
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ho := (zpow_right_inj₀ (lt_trans zero_lt_one hp) (ne_of_gt hp)).mp h
  have hd : (TF.ramificationIndex : ℤ) * TF.residueDegree *
      Module.finrank F.Carrier E.Carrier =
      (TE.ramificationIndex : ℤ) * TE.residueDegree := by
    exact_mod_cast (by rw [TF.ramificationIndex_mul_residueDegree,
      TE.ramificationIndex_mul_residueDegree,
      Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier] :
      TF.ramificationIndex * TF.residueDegree * Module.finrank F.Carrier E.Carrier =
        TE.ramificationIndex * TE.residueDegree)
  apply mul_left_cancel₀ (show (TE.residueDegree : ℤ) ≠ 0 by
    exact_mod_cast TE.residueDegree_pos.ne')
  linear_combination -(TF.ramificationIndex : ℤ) * ho + TF.ord x * hd

theorem ord_relative_norm_units_eq_zero_iff (x : E.Carrierˣ) :
    TF.ord ((Units.map (Algebra.norm F.Carrier (S := E.Carrier)) x :
      F.Carrierˣ) : F.Carrier) = 0 ↔ TE.ord (x : E.Carrier) = 0 := by
  change TF.ord (Algebra.norm F.Carrier (x : E.Carrier)) = 0 ↔ _
  have h := residueDegree_mul_ord_relative_norm F E TF TE (x : E.Carrier)
  have hF : (TF.residueDegree : ℤ) ≠ 0 := by exact_mod_cast TF.residueDegree_pos.ne'
  have hE : (TE.residueDegree : ℤ) ≠ 0 := by exact_mod_cast TE.residueDegree_pos.ne'
  constructor
  · intro hx
    rw [hx, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hE
  · intro hx
    rw [hx, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hF

/-- In an unramified extension, the determinant norm multiplies order by the degree. -/
theorem ord_relative_norm_of_unramified
    (he : TF.ramificationIndex = TE.ramificationIndex) (x : E.Carrier) :
    TF.ord (Algebra.norm F.Carrier x) =
      (Module.finrank F.Carrier E.Carrier : ℤ) * TE.ord x := by
  have hd : TF.residueDegree * Module.finrank F.Carrier E.Carrier =
      TE.residueDegree := by
    apply Nat.eq_of_mul_eq_mul_left TF.ramificationIndex_pos
    rw [← mul_assoc, TF.ramificationIndex_mul_residueDegree,
      Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier,
      ← TE.ramificationIndex_mul_residueDegree, he]
  have h := residueDegree_mul_ord_relative_norm F E TF TE x
  rw [← hd, Nat.cast_mul, mul_assoc] at h
  exact mul_left_cancel₀ (show (TF.residueDegree : ℤ) ≠ 0 by
    exact_mod_cast TF.residueDegree_pos.ne') h

/-- The unramified norm-order specialization on the actual multiplicative-group norm. -/
theorem ord_normUnits_of_unramified
    (he : TF.ramificationIndex = TE.ramificationIndex) (x : E.Carrierˣ) :
    TF.ord (normUnits F.Carrier E.Carrier x : F.Carrier) =
      (Module.finrank F.Carrier E.Carrier : ℤ) * TE.ord (x : E.Carrier) :=
  ord_relative_norm_of_unramified F E TF TE he (x : E.Carrier)

/-- The full published relative norm/order target, in independent universes. -/
theorem relativeNormOrderLaws : RelativeNormOrderLaws.{u, v} := by
  intro p hp F E hFE htower hfinite TF TE
  exact ⟨residueDegree_mul_ord_relative_norm F E TF TE,
    ramificationIndex_mul_ord_relative_algebraMap F E TF TE,
    ord_relative_norm_units_eq_zero_iff F E TF TE⟩

end Langlands.LocalClassField
