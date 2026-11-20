import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.VerticalGenericFibre
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Contraction of vertical primes under an integral map -/

open TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Localization

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]

private theorem disjoint_map_of_under {M : Submonoid R} {Q : Ideal C}
    (h : Disjoint (M : Set R) ((Q.under R : Ideal R) : Set R)) :
    Disjoint (Algebra.algebraMapSubmonoid C M : Set C) (Q : Set C) := by
  rw [Set.disjoint_left] at h ⊢
  rintro _ ⟨r, hr, rfl⟩ hrQ
  exact h hr hrQ

/-- A prime disjoint from the localization denominators extends to a prime in
the tensor product with the localized base. -/
def primeTensorLocalization (M : Submonoid R) (Q : Ideal C) [Q.IsPrime]
    (h : Disjoint (M : Set R) ((Q.under R : Ideal R) : Set R)) :
    PrimeSpectrum (Localization M ⊗[R] C) := by
  let S := Localization M ⊗[R] C
  let : Algebra C S := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid C M) S := IsLocalization.tensorRight _ M
  exact ⟨Q.map (algebraMap C S), IsLocalization.isPrime_of_isPrime_disjoint _ _ Q
    inferInstance (disjoint_map_of_under h)⟩

/-- The extended prime contracts to the original prime. -/
theorem primeTensorLocalization_under (M : Submonoid R) (Q : Ideal C) [Q.IsPrime]
    (h : Disjoint (M : Set R) ((Q.under R : Ideal R) : Set R)) :
    letI : Algebra C (Localization M ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
    (primeTensorLocalization M Q h).asIdeal.under C = Q := by
  let S := Localization M ⊗[R] C
  let : Algebra C S := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid C M) S := IsLocalization.tensorRight _ M
  exact IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance (disjoint_map_of_under h)

end Localization

section GoingDown

variable (R C G : Type*) [CommRing R] [CommRing C] [CommRing G]
    [Algebra R C] [Algebra R G] [Algebra C G] [IsScalarTower R C G]
    [Algebra.IsIntegral R C] [Module.Flat R G]

/-- An integral algebra embedded in a flat algebra over a ring with normal
prime localizations satisfies going down. -/
theorem hasGoingDown_of_normal_localizations_of_flat_embedding
    (hNormal : ∀ (q : Ideal R) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (hinj : Function.Injective (algebraMap C G)) : Algebra.HasGoingDown R C := by
  constructor
  intro p hp Q hQ hle
  let q := Q.under R
  let M := q.primeCompl
  let A := Localization.AtPrime q
  let D := A ⊗[R] C
  let H := A ⊗[R] G
  obtain ⟨hDomain, hClosed⟩ := hNormal q
  have : Module.Flat R A := IsLocalization.flat A M
  have : Module.Flat A H := inferInstance
  let : Algebra C D := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R C D := Algebra.TensorProduct.right_isScalarTower
  let f : C →ₐ[R] G := IsScalarTower.toAlgHom R C G
  let g : D →ₐ[A] H := Algebra.TensorProduct.map (AlgHom.id A A) f
  have hinjg : Function.Injective g := by
    change Function.Injective (LinearMap.lTensor A f.toLinearMap)
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hinj
  have hregular : Algebra.algebraMapSubmonoid D (nonZeroDivisors A) ≤ nonZeroDivisors D := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_nonZeroDivisors_iff_left.mpr
    intro x hx
    apply hinjg
    rw [map_zero]
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := H) ha
    change a • (g x) = a • (0 : H)
    have hg : algebraMap A H a * g x = 0 := by
      rw [← g.commutes, ← map_mul, hx, map_zero]
    exact (Algebra.smul_def a (g x)).trans (hg.trans (smul_zero a).symm)
  have : Algebra.HasGoingDown A D := hasGoingDown_of_regularScalars A D hregular
  have hd : Disjoint (M : Set R) (q : Set R) := Set.disjoint_left.mpr fun _ h => h
  let Q' := (primeTensorLocalization M Q hd).asIdeal
  have hQ' : Q'.IsPrime := (primeTensorLocalization M Q hd).isPrime
  have hQc : Q'.under C = Q := primeTensorLocalization_under M Q hd
  have hQa : (Q'.under A).under R = q := by
    calc
      (Q'.under A).under R = Q'.under R := Ideal.under_under _
      _ = (Q'.under C).under R := (Ideal.under_under _).symm
      _ = q := congrArg (Ideal.under R) hQc
  let P' := p.map (algebraMap R A)
  have hP' : P'.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime q hle.le
  have hP'r : P'.under R = p := Ideal.under_map_of_isLocalizationAtPrime q hle.le
  have hle' : P' ≤ Q'.under A := by
    apply Ideal.map_le_iff_le_comap.mpr
    change p ≤ (Q'.under A).under R
    rw [hQa]
    exact hle.le
  obtain ⟨J, hJ, hJp, hJP⟩ := Ideal.exists_ideal_le_liesOver_of_le Q' hle'
  refine ⟨J.under C, (Ideal.comap_mono hJ).trans_eq hQc, inferInstance, ⟨?_⟩⟩
  calc
    p = P'.under R := hP'r.symm
    _ = (J.under A).under R := congrArg (Ideal.under R) hJP.over
    _ = J.under R := Ideal.under_under _
    _ = (J.under C).under R := (Ideal.under_under _).symm

end GoingDown

/-- In an algebra with going down, a prime minimal over an extended ideal
contracts to a prime minimal over the original ideal. -/
theorem minimalPrime_under_of_hasGoingDown {R C : Type*} [CommRing R] [CommRing C]
    [Algebra R C] [Algebra.HasGoingDown R C] (I : Ideal R) (Q : Ideal C) [Q.IsPrime]
    (hQ : (I.map (algebraMap R C)).IsMinimalPrime Q) : I.IsMinimalPrime (Q.under R) := by
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mp hQ.le⟩, ?_⟩
  intro p hp hle
  have : p.IsPrime := hp.1
  obtain ⟨P, hPle, hP, hPR⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  have hI : I.map (algebraMap R C) ≤ P := by
    apply Ideal.map_le_iff_le_comap.mpr
    change I ≤ P.under R
    rw [← hPR.over]
    exact hp.2
  have hQP : Q ≤ P := hQ.2 ⟨hP, hI⟩ hPle
  exact (Ideal.comap_mono hQP).trans_eq hPR.over.symm

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
