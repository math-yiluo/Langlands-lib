import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyScalarHeight

/-! # Scalar heights with the ramification and residue-field normalization -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable {π a : O} {u : Oˣ} {e p f h : ℕ}

/-- A scalar unit is an actual formal module automorphism. -/
def scalarUnitIso (M : ModuleLaw O R σ) (u : Oˣ) : Iso M M where
  hom := M.scalarHom u
  inv := M.scalarHom ↑u⁻¹
  inv_hom := by rw [← scalarHom_mul, Units.inv_mul, scalarHom_one]
  hom_inv := by rw [← scalarHom_mul, Units.mul_inv, scalarHom_one]

/-- Multiplication by a unit does not change the actual scalar kernel. -/
def scalarKernelIso_unit_mul (M : ModuleLaw O R σ) (u : Oˣ) (a : O) :
    (M.scalarHom a).kernelSetFunctor ≅ (M.scalarHom (↑u * a)).kernelSetFunctor :=
  Hom.kernelSetIsoOfIsoSquare _ _ (Iso.refl M) (M.scalarUnitIso u) (by
    change (M.scalarHom (↑u * a)).comp (Hom.id M) = (M.scalarHom ↑u).comp (M.scalarHom a)
    rw [Hom.comp_id, scalarHom_mul])

private theorem scalarPower_factor (ha : a = (↑u : O) * π ^ e) (n : ℕ) :
    a ^ n = (↑(u ^ n) : O) * π ^ (n * e) := by
  rw [ha, mul_pow, ← pow_mul π e n, mul_comm e n]
  rfl

/-- For a positive ramification exponent, divisibility by a unit times a uniformizer
power gives divisibility by the uniformizer once its power kernels are finite locally free. -/
theorem IsPiDivisible.of_unit_mul_pow (hA : M.IsPiDivisible a)
    (ha : a = (↑u : O) * π ^ e) (he : 0 < e)
    (hk : ∀ n : ℕ, (M.scalarHom (π ^ n)).HasFiniteLocallyFreeKernel) : M.IsPiDivisible π := by
  refine ⟨?_, ?_, ?_, hk⟩
  · obtain ⟨n, hn⟩ := hA.base_nilpotent
    refine ⟨n * e, ?_⟩
    rw [← map_pow, scalarPower_factor ha, map_mul, map_pow] at hn
    have hu := (u ^ n).isUnit.map (algebraMap O R)
    exact hu.smul_eq_zero.mp hn
  · intro A x
    obtain ⟨n, hn⟩ := hA.torsion A x
    rw [scalarPower_factor ha, mul_smul] at hn
    exact ⟨n * e, (u ^ n).isUnit.smul_eq_zero.mp hn⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    have hh : (M.scalarHom π).comp (M.scalarHom ((↑u : O) * π ^ m)) = M.scalarHom a := by
      rw [← scalarHom_mul, ha, pow_succ]
      congr 1
      ac_rfl
    exact Hom.IsFppfLocallySurjective.right_of_comp (hh.symm ▸ hA.scalar_locallySurjective)

/-- The scalar height for a unit times a uniformizer power uses the corresponding
ramification and residue exponents in the p-normalization. -/
theorem HasPiHeight.unit_mul_pow (hπ : M.HasPiHeight π (p ^ f) h) (hA : M.IsPiDivisible a)
    (ha : a = (↑u : O) * π ^ e) : M.HasPiHeight a p (e * f * h) := by
  refine ⟨hA, fun n => ?_⟩
  have hn := hπ.scalarPower_rank (n * e)
  have hpow : (p ^ f) ^ (n * e * h) = p ^ (n * (e * f * h)) := by
    rw [← pow_mul]
    congr 1
    ac_rfl
  rw [hpow] at hn
  rw [scalarPower_factor ha]
  exact (Hom.hasKernelRank_iff_of_kernelSetIso _ _ (M.scalarKernelIso_unit_mul (u ^ n) _) _).mp hn

private theorem scalarPower_fieldDegree_mul {k : Type v} [Field k] [Algebra O k]
    {L : ModuleLaw O k σ} (hL : L.IsPiDivisible π) (n e : ℕ) :
    (hL.scalarPower_isIsogeny (n * e)).fieldDegree = (hL.scalarPower_isIsogeny n).fieldDegree ^ e := by
  induction e with
  | zero =>
    calc
      _ = 1 := by
        apply Hom.IsIsogeny.fieldDegree_eq_of_rank
        rw [Nat.mul_zero, pow_zero, scalarHom_one]
        exact (Iso.refl L).hasKernelRank_one
      _ = _ := (pow_zero _).symm
  | succ e ih =>
    rw [Nat.mul_succ, hL.scalarPower_fieldDegree_add, ih, pow_succ, mul_comm]

/-- When the central uniformizer kernels are available, p-height determines their
actual uniformizer-normalized height by finite kernel ranks at residue fields. -/
theorem HasPiHeight.of_unit_mul_pow (hA : M.HasPiHeight a p (e * f * h)) (hπ : M.IsPiDivisible π)
    (ha : a = (↑u : O) * π ^ e) (he : 0 < e) : M.HasPiHeight π (p ^ f) h := by
  apply hπ.hasPiHeight_of_residueFields
  intro x
  let k := CommAlgCat.of R x.asIdeal.ResidueField
  let : Algebra O k := coefficientAlgebra k
  let : IsScalarTower O R k := coefficientScalarTower k
  let φ := IsScalarTower.toAlgHom O R k
  let L := M.map φ
  have hA' := hA.map φ
  have hπ' := hπ.map φ
  change L.HasPiHeight π (p ^ f) h
  refine ⟨hπ', fun n => ?_⟩
  have hn := hA'.scalarPower_rank n
  rw [scalarPower_factor ha] at hn
  have hr := (Hom.hasKernelRank_iff_of_kernelSetIso _ _ (L.scalarKernelIso_unit_mul (u ^ n) _) _).mpr hn
  have hd := (hπ'.scalarPower_isIsogeny (n * e)).fieldDegree_eq_of_rank hr
  rw [scalarPower_fieldDegree_mul hπ' n e] at hd
  have hpow : p ^ (n * (e * f * h)) = ((p ^ f) ^ (n * h)) ^ e := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ac_rfl
  rw [hpow] at hd
  have eq := Nat.pow_left_injective he.ne' hd
  exact eq ▸ (hπ'.scalarPower_isIsogeny n).hasKernelRank_fieldDegree

end Langlands.FormalGroup.ModuleLaw
