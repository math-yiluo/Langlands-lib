import Langlands.ClassFieldTheory.Global.IdeleLocalSupport
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.NormReduction
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

/-! # Principal units are quadratic norms at almost every finite place -/

noncomputable section

open NumberField IsDedekindDomain Filter
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.ClassFieldTheory.Global

open Langlands.Global.AdelicFunctoriality

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem eventually_principal_valuation_one (a : Kˣ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite,
      Valued.v (algebraMap K (w.adicCompletion K) (a : K)) = 1 := by
  let z := Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom a
  have h := (finite_setOf_ideleCoordinate_not_mem_localUnits z).eventually_cofinite_notMem
  filter_upwards [h] with w hw
  have hw' : ideleCoordinate w z ∈ localUnits w := by simpa using hw
  rw [mem_localUnits_iff, ideleCoordinate_val] at hw'
  exact hw'

/-- Away from the finite ramification and principal divisor supports, a local
coordinate of a field unit is a norm from the whole completed tensor algebra. -/
theorem eventually_principal_tensor_norm (a : Kˣ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite,
      ∃ b : w.adicCompletion K ⊗[K] L,
        Algebra.norm (w.adicCompletion K) b = algebraMap K (w.adicCompletion K) (a : K) := by
  classical
  filter_upwards [eventually_ramificationIdx_eq_one K L,
    eventually_principal_valuation_one a] with w he ha
  let q := placeAbove L w
  let x := Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom a
  obtain ⟨b, _, hb⟩ := FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one w q.1
    (he q.1 q.2) x ha
  let f := AlgEquiv.ofBijective (finiteTensorMap (L := L) w) ((completedTensorComparison K L).1 w)
  let y : ∀ s : FinitePlacesAbove L w, s.1.adicCompletion L := Function.update 1 q (b : q.1.adicCompletion L)
  refine ⟨f.symm y, ?_⟩
  rw [← Algebra.norm_eq_of_algEquiv f, f.apply_symm_apply,
    norm_pi (w.adicCompletion K) (FinitePlacesAbove L w) (fun s => s.1.adicCompletion L)]
  rw [Finset.prod_eq_single q]
  · dsimp only [y]
    rw [Function.update_self]
    exact hb
  · intro s _ hs
    dsimp only [y]
    rw [Function.update_of_ne hs, Pi.one_apply, map_one]
  · intro h
    exact (h (Finset.mem_univ _)).elim

section QuadraticAlgebra

open scoped QuadraticAlgebra

private def quadraticBaseChange {F R : Type u} [Field F] [CommRing R] [Algebra F R]
    (d : F) : R ⊗[F] QuadraticAlgebra F d 0 ≃ₐ[R]
      QuadraticAlgebra R (algebraMap F R d) (algebraMap F R 0) := by
  let f := AlgHom.liftEquiv F R (QuadraticAlgebra F d 0)
    (QuadraticAlgebra R (algebraMap F R d) (algebraMap F R 0)) (QuadraticAlgebra.baseChange R d 0)
  let b := (QuadraticAlgebra.basis d (0 : F)).baseChange R
  let c := QuadraticAlgebra.basis (algebraMap F R d) (algebraMap F R 0)
  let e := b.equiv c (Equiv.refl (Fin 2))
  have h : f.toLinearMap = e.toLinearMap := by
    apply b.ext
    intro i
    have hi : e (b i) = c i := b.equiv_apply i c (Equiv.refl (Fin 2))
    change f (b i) = e (b i)
    rw [hi]
    simp only [b, Module.Basis.baseChange_apply]
    fin_cases i
    · change f ((1 : R) ⊗ₜ[F] QuadraticAlgebra.basis d 0 0) =
        QuadraticAlgebra.basis (algebraMap F R d) (algebraMap F R 0) 0
      simp only [QuadraticAlgebra.basis_apply_zero, ← Algebra.TensorProduct.one_def, map_one]
    · change f ((1 : R) ⊗ₜ[F] QuadraticAlgebra.basis d 0 1) =
        QuadraticAlgebra.basis (algebraMap F R d) (algebraMap F R 0) 1
      simp only [QuadraticAlgebra.basis_apply_one]
      change (1 : R) • QuadraticAlgebra.baseChange R d 0 ω = ω
      rw [one_smul]
      ext <;> simp [QuadraticAlgebra.baseChange, QuadraticAlgebra.mapRingHom]
  have hbij : Function.Bijective f.toLinearMap := by
    rw [h]
    exact e.bijective
  exact AlgEquiv.ofBijective f hbij

/-- The quadratic norm form of any nonzero scalar represents any field unit
at cofinitely many finite places of a number field. -/
theorem eventually_quadratic_norm_form (d : K) (hd : d ≠ 0) (a : Kˣ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite,
      ∃ x y : w.adicCompletion K,
        x ^ 2 - algebraMap K (w.adicCompletion K) d * y ^ 2 = algebraMap K (w.adicCompletion K) (a : K) := by
  by_cases hs : IsSquare d
  · obtain ⟨r, hr⟩ := hs
    have hr0 : r ≠ 0 := fun h => hd (by simp [hr, h])
    apply Filter.Eventually.of_forall
    intro w
    have : CharZero (w.adicCompletion K) := Algebra.charZero_of_charZero K _
    let f := algebraMap K (w.adicCompletion K)
    have hr' : f r ≠ 0 := (map_ne_zero_iff f f.injective).mpr hr0
    refine ⟨(f a + 1) / 2, (f a - 1) / (2 * f r), ?_⟩
    change ((f a + 1) / 2) ^ 2 - f d * ((f a - 1) / (2 * f r)) ^ 2 = f a
    rw [hr, map_mul]
    field_simp [hr']
    ring
  · let : Fact (¬ IsSquare d) := ⟨hs⟩
    let L' := QuadraticAlgebra K d 0
    let : NumberField L' := NumberField.of_module_finite K L'
    filter_upwards [eventually_principal_tensor_norm (L := L') a] with w hw
    obtain ⟨z, hz⟩ := hw
    let f := quadraticBaseChange (R := w.adicCompletion K) d
    refine ⟨(f z).re, (f z).im, ?_⟩
    have h := Algebra.norm_eq_of_algEquiv f z
    rw [hz, Algebra.norm_apply] at h
    change (DistribSMul.toLinearMap (w.adicCompletion K) _ (f z)).det = _ at h
    rw [QuadraticAlgebra.det_toLinearMap_eq_norm] at h
    simpa only [QuadraticAlgebra.norm_def, map_zero, zero_mul, add_zero, pow_two, mul_assoc] using h

end QuadraticAlgebra

end Langlands.ClassFieldTheory.Global
