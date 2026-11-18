import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Descent of membership in a linear range along flat pointwise covers -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Cohomology

/-- Membership of an element in the range of a linear map descends along any family of
flat algebras whose prime spectra jointly cover the base: if for every prime `p` of `R`
some flat `R`-algebra `K` with a prime over `p` contains `1 ⊗ v` in the range of
`K ⊗ δ`, then `v` lies in the range of `δ`. No finiteness of the modules is needed. -/
theorem mem_range_of_flat_cover {R : Type u} [CommRing R] {P Q : Type u}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (δ : P →ₗ[R] Q) (v : Q)
    (h : ∀ p : PrimeSpectrum R, ∃ (K : Type u) (_ : CommRing K) (_ : Algebra R K),
      Module.Flat R K ∧ (∃ q : PrimeSpectrum K, PrimeSpectrum.comap (algebraMap R K) q = p) ∧
        (1 : K) ⊗ₜ[R] v ∈ LinearMap.range (δ.lTensor K)) :
    v ∈ LinearMap.range δ := by
  by_contra hv
  let C := Q ⧸ LinearMap.range δ
  let x : C := Submodule.mkQ _ v
  have hx : x ≠ 0 := by
    intro h0
    exact hv ((Submodule.Quotient.mk_eq_zero _).1 h0)
  let I : Ideal R := Ideal.torsionOf R C x
  have hI : I ≠ ⊤ := fun htop => hx ((Ideal.torsionOf_eq_top_iff (R := R) x).1 htop)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨K, _, _, hflat, ⟨q, hq⟩, hmem⟩ := h ⟨m, hm.isPrime⟩
  have h0 : (1 : K) ⊗ₜ[R] x = 0 := by
    obtain ⟨w, hw⟩ := hmem
    have hc := congrArg ((Submodule.mkQ (LinearMap.range δ)).lTensor K) hw
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp] at hc
    have hz : (Submodule.mkQ (LinearMap.range δ)).comp δ = 0 := by
      ext y
      simp
    rw [hz, LinearMap.lTensor_zero] at hc
    simpa [x] using hc.symm
  let N : Submodule R C := R ∙ x
  let xN : N := ⟨x, Submodule.mem_span_singleton_self x⟩
  have h1 : (1 : K) ⊗ₜ[R] xN = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective
    simpa [xN] using h0
  have hker : (I : Submodule R R) ≤ LinearMap.ker (Algebra.linearMap R (K ⧸ q.asIdeal)) := by
    intro r hr
    have hrm : r ∈ m := hIm hr
    have hrq : algebraMap R K r ∈ q.asIdeal := by
      have : r ∈ (PrimeSpectrum.comap (algebraMap R K) q).asIdeal := by
        rw [hq]; exact hrm
      exact this
    rw [LinearMap.mem_ker, Algebra.linearMap_apply, IsScalarTower.algebraMap_apply R K,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hrq
  let φ : N →ₗ[R] K ⧸ q.asIdeal :=
    ((I : Submodule R R).liftQ (Algebra.linearMap R (K ⧸ q.asIdeal)) hker).comp
      (Ideal.quotTorsionOfEquivSpanSingleton R C x).symm.toLinearMap
  have hφ : φ xN = 1 := by
    have he : (Ideal.quotTorsionOfEquivSpanSingleton R C x) (Submodule.Quotient.mk 1) = xN := by
      rw [Ideal.quotTorsionOfEquivSpanSingleton_apply_mk, one_smul]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply, Algebra.linearMap_apply,
      map_one]
  let ψ : K ⊗[R] N →ₗ[R] K ⧸ q.asIdeal :=
    TensorProduct.lift ((LinearMap.mul R (K ⧸ q.asIdeal)).compl₁₂
      (Ideal.Quotient.mkₐ R q.asIdeal).toLinearMap φ)
  have hψ : ψ ((1 : K) ⊗ₜ[R] xN) = 1 := by
    simp only [ψ, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, map_one, hφ, mul_one]
  have : Nontrivial (K ⧸ q.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr q.isPrime.ne_top
  rw [h1, map_zero] at hψ
  exact zero_ne_one hψ

end Langlands.GroupScheme.Cohomology
