import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceStatement
import Langlands.Representation.Unramified.SphericalFixedLineProof
import Langlands.Representation.Hecke.DoubleCosetSandwich
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Existence of spectra for the actual standard spherical Hecke operators -/

noncomputable section
namespace Langlands.Unramified
open Correspondence Polynomial
universe uF uV

namespace Eigenvalues

/-- A complex polynomial with constant coefficient one is an Euler polynomial,
with its degree recording every root multiplicity. -/
theorem exists_eulerPolynomial (P : ℂ[X]) (hP : P.eval 0 = 1) :
    ∃ s : Eigenvalues P.natDegree, eulerPolynomial s = P := by
  classical
  have hP0 : P ≠ 0 := by intro h; simp [h] at hP
  have hr (a : {a // a ∈ P.roots}) : (a : ℂ) ≠ 0 := by
    intro ha
    have h := (mem_roots hP0).mp a.property
    rw [IsRoot, ha, hP] at h
    exact one_ne_zero h
  let z (a : {a // a ∈ P.roots}) : ℂˣ := (Units.mk0 (a : ℂ) (hr a))⁻¹
  let s : Eigenvalues P.natDegree :=
    ⟨P.roots.attach.map z, by simp [IsAlgClosed.card_roots_eq_natDegree]⟩
  refine ⟨s, ?_⟩
  have hfactor (a : {a // a ∈ P.roots}) :
      X - C (a : ℂ) = C (-(a : ℂ)) * (1 - C (z a : ℂ) * X) := by
    simp only [z, Units.val_inv_eq_inv_val, Units.val_mk0]
    have hc : C (a : ℂ) * C (a : ℂ)⁻¹ = (1 : ℂ[X]) := by
      rw [← map_mul, mul_inv_cancel₀ (hr a), map_one]
    calc
      X - C (a : ℂ) = (C (a : ℂ) * C (a : ℂ)⁻¹) * X - C (a : ℂ) := by rw [hc, one_mul]
      _ = C (-(a : ℂ)) * (1 - C (a : ℂ)⁻¹ * X) := by rw [map_neg]; ring
  have heq := (IsAlgClosed.splits P).eq_prod_roots
  rw [← P.roots.attach_map_val, Multiset.map_map] at heq
  simp_rw [Function.comp_def, hfactor] at heq
  rw [Multiset.prod_map_mul] at heq
  have hc : (P.roots.attach.map fun a : {a // a ∈ P.roots} => C (-(a : ℂ))).prod =
      C ((P.roots.attach.map fun a : {a // a ∈ P.roots} => -(a : ℂ)).prod) := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  rw [hc, ← mul_assoc, ← map_mul] at heq
  have hconst := congrArg (Polynomial.eval 0) heq
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
    Function.comp_def, eval_sub, eval_one, eval_X, mul_zero, sub_zero,
    Multiset.map_const', Multiset.prod_replicate, one_pow, mul_one] at hconst
  rw [← hconst, hP, map_one, one_mul] at heq
  change ((P.roots.attach.map z).map fun z : ℂˣ => 1 - C (z : ℂ) * X).prod = P
  simpa only [Multiset.map_map, Function.comp_def] using heq.symm

end Eigenvalues

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup heckeGeneralLinearMeasurable heckeGeneralLinearBorel
  heckeGeneralLinearT2

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The last standard Hecke element is a unit: its inverse is the double coset
of the inverse scalar uniformizer. -/
theorem standardHeckeElement_last_isUnit (r : ℕ) :
    IsUnit (standardHeckeElement F r (Fin.last (r + 1))) := by
  let z := standardDiagonal F r (Fin.last (r + 1))
  have hz : z ∈ Subgroup.center (GeneralLinear (r + 1) F.Carrier) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Units.ext
    ext i j
    have hi : i.val ≤ r := by omega
    have hj : j.val ≤ r := by omega
    simp [z, standardDiagonal_val, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm, hi, hj]
  have hn : z ∈ Subgroup.normalizer ((sphericalOpenSubgroup F r).toSubgroup :
      Set (GeneralLinear (r + 1) F.Carrier)) := Subgroup.center_le_normalizer _ hz
  let D := Hecke.HeckeAlgebra.Corner.doubleCoset (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r)
  have hleft : D z * D z⁻¹ = 1 := by
    have h := Hecke.HeckeAlgebra.Corner.doubleCoset_mul_mul_of_mem_normalizer
      (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r)
      (sphericalHaar F r) hn (Subgroup.inv_mem _ hn) 1
    simpa [D] using h
  have hright : D z⁻¹ * D z = 1 := by
    have h := Hecke.HeckeAlgebra.Corner.doubleCoset_mul_mul_of_mem_normalizer
      (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r)
      (sphericalHaar F r) (Subgroup.inv_mem _ hn) hn 1
    simpa [D] using h
  exact ⟨⟨D z, D z⁻¹, hleft, hright⟩, rfl⟩

/-- Every actual irreducible admissible spherical representation has a spectrum
for all the standard spherical Hecke operators. -/
theorem sphericalHeckeSpectrumExistence : SphericalHeckeSpectrumExistenceStatement.{uF, uV} := by
  classical
  intro p _ F r A h0
  have hd := sphericalFixedLine p F r A h0
  let V := fixedVectors A.obj.representation (sphericalSubgroup F r)
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hscalar (i : Fin (r + 2)) :
      ∃ c : ℂ, standardHeckeOperator F A i = c • LinearMap.id :=
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd
      (standardHeckeOperator F A i)).exists
  choose c hc using hscalar
  have hc0 : c 0 = 1 := by
    apply smul_left_injective ℂ hv
    have h := LinearMap.congr_fun (hc 0) v
    rw [standardHeckeOperator_zero] at h
    change v = c 0 • v at h
    simpa only [one_smul] using h.symm
  have hunit : IsUnit (standardHeckeOperator F A (Fin.last (r + 1))) :=
    (standardHeckeElement_last_isUnit F r).map
      (@Hecke.cornerAction (GeneralLinear (r + 1) F.Carrier) _
        (F.canonicalGeneralLinearTopology (r + 1))
        (F.canonicalGeneralLinearTopologicalGroup (r + 1)) _ _ _ _ _
        (sphericalHaar F r) _ A.obj.representation A.obj.isSmooth
        (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r))
  have hclast : c (Fin.last (r + 1)) ≠ 0 := by
    intro h
    apply hunit.ne_zero
    rw [hc, h, zero_smul]
  let q : ℂ := (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ)
  have hq : q ≠ 0 := by
    have hpos : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
      exact_mod_cast Nat.zero_lt_of_lt F.canonicalTopologicalData.residueCardinality_gt_one
    change (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  let b (i : Fin (r + 2)) : ℂ := c i / q ^ (i.val * (r + 1 - i.val)) * (-1) ^ i.val
  let P : ℂ[X] := ∑ i : Fin (r + 2), monomial i.val (b i)
  have hcoeff (i : Fin (r + 2)) : P.coeff i.val = b i := by
    simp [P, coeff_monomial, Fin.val_inj]
  have hP0 : P.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, show 0 = (0 : Fin (r + 2)).val from rfl, hcoeff]
    simp [b, hc0]
  have hPdeg : P.natDegree = r + 1 := by
    apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro N hN
      simp only [P, finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_monomial, ite_eq_right (by omega)]
    · apply le_natDegree_of_ne_zero
      rw [show r + 1 = (Fin.last (r + 1)).val from rfl, hcoeff]
      simpa [b] using mul_ne_zero hclast (pow_ne_zero (r + 1) (neg_ne_zero.mpr one_ne_zero))
  obtain ⟨s, hs⟩ := Eigenvalues.exists_eulerPolynomial P hP0
  have hex : ∃ s : Eigenvalues (r + 1), Eigenvalues.eulerPolynomial s = P := by
    exact ⟨⟨(s : Multiset ℂˣ), s.prop.trans hPdeg⟩, hs⟩
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, h0, ?_⟩
  intro i w
  have heq : standardHeckeScalar F s i = c i := by
    change q ^ (i.val * (r + 1 - i.val)) * ((-1 : ℂ) ^ i.val *
      (Eigenvalues.eulerPolynomial s).coeff i.val) = c i
    rw [hs, hcoeff]
    dsimp only [b]
    have hsign : (-1 : ℂ) ^ i.val * (-1 : ℂ) ^ i.val = 1 := by
      rw [← mul_pow]; simp
    have hpow := pow_ne_zero (i.val * (r + 1 - i.val)) hq
    field_simp
    linear_combination c i * hsign
  rw [heq, hc]
  rfl

end Langlands.Unramified
