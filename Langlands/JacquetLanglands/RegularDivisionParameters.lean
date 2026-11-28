import Langlands.BaseChange.RegularOrbitParameters
import Langlands.BaseChange.RegularCyclicBasis
import Langlands.JacquetLanglands.DivisionMatching

/-! # Characteristic coefficients and polynomial centralizers for division units -/

noncomputable section

namespace Langlands.JacquetLanglands

open Set Matrix _root_.Polynomial _root_.Topology
open Langlands.BaseChange Langlands.CentralSimple Langlands.TraceFormula
open Langlands.BaseChange.SigmaLiftCharacterIdentity (coefficients continuous_charpoly_coefficient)
open scoped TensorProduct

universe u

variable (F D : Type u) [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]

local notation "d" => reducedDegree F D

/-- The coefficients below the leading term of the reduced characteristic polynomial. -/
def divisionCoefficients (a : Dˣ) : Fin d → F :=
  fun i => (reducedCharpoly F D a.val).coeff i

theorem polynomialOfCoefficients_divisionCoefficients (a : Dˣ) :
    polynomialOfCoefficients (divisionCoefficients F D a) = reducedCharpoly F D a.val := by
  conv_rhs => rw [(reducedCharpoly_monic F D a.val).as_sum, reducedCharpoly_natDegree]
  unfold polynomialOfCoefficients divisionCoefficients
  exact congrArg (X ^ d + ·)
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => C ((reducedCharpoly F D a.val).coeff i) * X ^ i) d)

/-- In a splitting chart, a division unit acts by a matrix unit. -/
private def splitUnit : Dˣ →* GeneralLinear d (finiteGaloisSplittingField F D) :=
  Units.map (((finiteGaloisSplittingChart F D).restrictScalars F).toMonoidHom.comp
    (Algebra.TensorProduct.includeRight.toMonoidHom))

private theorem charpoly_splitUnit (a : Dˣ) :
    (splitUnit F D a).val.charpoly =
      (reducedCharpoly F D a.val).map (algebraMap F (finiteGaloisSplittingField F D)) :=
  (reducedCharpoly_map_chart F D (finiteGaloisSplittingChart F D) a.val).symm

theorem reducedCharpoly_unit_conj (x a : Dˣ) :
    reducedCharpoly F D (x⁻¹ * a * x : Dˣ).val = reducedCharpoly F D a.val := by
  apply Polynomial.map_injective _ (algebraMap F (finiteGaloisSplittingField F D)).injective
  rw [← charpoly_splitUnit, ← charpoly_splitUnit, map_mul, map_mul, map_inv,
    charpoly_conj]

theorem divisionCoefficients_conj (x a : Dˣ) :
    divisionCoefficients F D (x⁻¹ * a * x) = divisionCoefficients F D a := by
  funext i
  simp only [divisionCoefficients, reducedCharpoly_unit_conj]

theorem divisionCoefficients_eq_iff {a b : Dˣ} :
    divisionCoefficients F D a = divisionCoefficients F D b ↔
      reducedCharpoly F D a.val = reducedCharpoly F D b.val := by
  constructor
  · intro h
    rw [← polynomialOfCoefficients_divisionCoefficients F D a,
      ← polynomialOfCoefficients_divisionCoefficients F D b, h]
  · intro h
    funext i
    exact congrArg (fun p : F[X] => p.coeff i) h

theorem corresponds_iff_coefficients_eq {g : GeneralLinear d F} {a : Dˣ}
    (ha : IsRegular F D a) : Corresponds F D g a ↔
      coefficients g = divisionCoefficients F D a := by
  constructor
  · intro h
    funext i
    exact congrArg (fun p : F[X] => p.coeff i) h.2.2
  · intro h
    have hpoly : g.val.charpoly = reducedCharpoly F D a.val := by
      rw [← polynomialOfCoefficients_coefficients g, h,
        polynomialOfCoefficients_divisionCoefficients]
    have hg : IsRegularSemisimple g := by
      unfold IsRegularSemisimple
      rw [hpoly]
      exact ha
    exact (corresponds_iff F D g a).2 ⟨hg, ha, hpoly⟩

/-- Every element commuting with a regular element is a linear combination of its powers. -/
theorem exists_sum_pow_of_commute_regular_division {a b : D}
    (ha : (reducedCharpoly F D a).Separable) (hb : Commute b a) :
    ∃ c : Fin d → F, b = ∑ i, c i • a ^ (i : ℕ) := by
  let L := finiteGaloisSplittingField F D
  let e := finiteGaloisSplittingChart F D
  let j : D →ₐ[F] L ⊗[F] D := Algebra.TensorProduct.includeRight
  let A := e (j a)
  have hA : A.charpoly.Separable :=
    (reducedCharpoly_map_chart F D e a) ▸ ha.map
  obtain ⟨v, hv⟩ := regularCyclicBasis L d A hA
  obtain ⟨c, hc⟩ := exists_sum_pow_of_commute hv ((hb.map j).map e)
  have hsum : (1 : L) ⊗ₜ[F] b = ∑ i, c i ⊗ₜ[F] (a ^ (i : ℕ)) := by
    apply e.injective
    change e (j b) = _
    rw [map_sum, hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht (k : L) (z : D) : (k ⊗ₜ[F] z) = k • ((1 : L) ⊗ₜ[F] z) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul]
    change c i • A ^ (i : ℕ) = c i • e (j (a ^ (i : ℕ)))
    rw [map_pow, map_pow]
  let s : F →ₗ[F] L := Algebra.linearMap F L
  obtain ⟨r, hr⟩ := s.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F L).injective)
  have h1 : r (1 : L) = 1 := by simpa [s] using LinearMap.congr_fun hr (1 : F)
  let p := (TensorProduct.lid F D).toLinearMap.comp
    (TensorProduct.map r (LinearMap.id : D →ₗ[F] D))
  have hp (x : L) (y : D) : p (x ⊗ₜ[F] y) = r x • y := by simp [p]
  refine ⟨fun i => r (c i), ?_⟩
  simpa only [map_sum, hp, h1, one_smul] using congrArg p hsum

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]
  [TopologicalSpace D] [IsModuleTopology F D]

/-- The reduced characteristic coefficients are continuous in the module topology. -/
theorem continuous_divisionCoefficients : Continuous (divisionCoefficients F D) := by
  let L := finiteGaloisSplittingField F D
  let : TopologicalSpace L := moduleTopology F L
  let : IsModuleTopology F L := ⟨rfl⟩
  let : IsTopologicalRing L := IsModuleTopology.isTopologicalRing F L
  let M := Matrix (Fin d) (Fin d) L
  let : IsModuleTopology F M := inferInstanceAs (IsModuleTopology F (Fin d → Fin d → L))
  let j : D →ₐ[F] M := ((finiteGaloisSplittingChart F D).restrictScalars F).toAlgHom.comp
    Algebra.TensorProduct.includeRight
  have hj : Continuous (j : D → M) := IsModuleTopology.continuous_of_linearMap j.toLinearMap
  have hsplit : Continuous (splitUnit F D) := hj.units_map j.toMonoidHom
  let s : F →ₗ[F] L := Algebra.linearMap F L
  obtain ⟨r, hr⟩ := s.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F L).injective)
  have hleft : Function.LeftInverse r s := LinearMap.congr_fun hr
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  refine continuous_pi fun i => ?_
  have heq : (fun a : Dˣ => divisionCoefficients F D a i) =
      r ∘ (fun g : GeneralLinear d L => g.val.charpoly.coeff i) ∘ splitUnit F D := by
    funext a
    change divisionCoefficients F D a i = r ((splitUnit F D a).val.charpoly.coeff i)
    rw [charpoly_splitUnit, Polynomial.coeff_map]
    exact (hleft _).symm
  rw [heq]
  exact hrc.comp ((continuous_charpoly_coefficient (R := L) (n := d) i).comp hsplit)

end Topology

end Langlands.JacquetLanglands
