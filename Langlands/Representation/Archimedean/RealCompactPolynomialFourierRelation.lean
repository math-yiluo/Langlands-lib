import Langlands.Representation.Archimedean.RealPolynomialFourierPropagation
import Langlands.Representation.Archimedean.RealIntegralGenericPolynomial
import Langlands.Representation.Archimedean.RealAmbientOrthogonalUncertainty

/-! # Exact polynomial Fourier relations on a common compact model -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealCompactPolynomialFourierRelation

open Polynomial Complex RealKTypeCount RealBlockFourierFinite
open RealOrthogonalUncertainty RealPolynomialFourierPropagation

local notation "K3" => Matrix.unitaryGroup (Fin 3) ℝ
local notation "G3" => Langlands.GeneralLinear 3 ℝ

abbrev vector {N : ℕ} (f : G3 → ℂ) (hN : restrictLinear 3 f ∈ degreeLE 3 N) :
    degreeLE 3 N :=
  ⟨restrictLinear 3 f, hN⟩

/-- Finitely many continuous compact-finite functions have one common polynomial degree bound. -/
theorem exists_common_degree {ι : Type*} [Fintype ι] (fs : ι → G3 → ℂ)
    (hc : ∀ i, Continuous (fs i))
    (hK : ∀ i, fs i ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G3) (unitaryCompact ℝ 3)) :
    ∃ N, ∀ i, restrictLinear 3 (fs i) ∈ degreeLE 3 N := by
  classical
  choose Ns hNs using fun i => exists_degreeLE (hc i) (hK i)
  refine ⟨Finset.univ.sup Ns, fun i => degreeLE_mono ?_ (hNs i)⟩
  exact Finset.le_sup (Finset.mem_univ i)

/-- Two polynomial Fourier expressions agree exactly when their compact operators agree. -/
theorem relation_iff {N p : ℕ} (hp : p + 1 < 3)
    (f g : G3 → ℂ) (hNf : restrictLinear 3 f ∈ degreeLE 3 N)
    (hNg : restrictLinear 3 g ∈ degreeLE 3 N) (P Q : ℂ[X]) :
    (∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      P.eval (j : ℂ) * blockFourierCoefficient 3 p j f x =
        Q.eval (j : ℂ) * blockFourierCoefficient 3 p j g x) ↔
    aeval (-I • gen N hp) P (vector f hNf) =
      aeval (-I • gen N hp) Q (vector g hNg) := by
  constructor
  · intro hrel
    have hproj : ∀ j, proj N hp j (aeval (-I • gen N hp) P (vector f hNf)) =
        proj N hp j (aeval (-I • gen N hp) Q (vector g hNg)) := by
      intro j
      rw [proj_aeval (isModeDecomposition N hp), proj_aeval (isModeDecomposition N hp)]
      apply Subtype.ext
      funext x
      change P.eval (j : ℂ) * ((proj N hp j (vector f hNf) : degreeLE 3 N) : K3 → ℂ) x =
        Q.eval (j : ℂ) * ((proj N hp j (vector g hNg) : degreeLE 3 N) : K3 → ℂ) x
      rw [proj_restrict_apply hp j hNf, proj_restrict_apply hp j hNg]
      linear_combination (2 * (Real.pi : ℂ))⁻¹ * hrel j (Unitary.toUnits x) x.2
    rw [← sum_proj_apply N hp (aeval (-I • gen N hp) P (vector f hNf)),
      ← sum_proj_apply N hp (aeval (-I • gen N hp) Q (vector g hNg))]
    exact Finset.sum_congr rfl fun j _ => hproj j
  · intro heq j x hx
    let κ : K3 := ⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩
    have hpj := congrArg (fun w : degreeLE 3 N => proj N hp j w) heq
    rw [proj_aeval (isModeDecomposition N hp), proj_aeval (isModeDecomposition N hp)] at hpj
    have hval := congrFun (congrArg Subtype.val hpj) κ
    change P.eval (j : ℂ) * ((proj N hp j (vector f hNf) : degreeLE 3 N) : K3 → ℂ) κ =
      Q.eval (j : ℂ) * ((proj N hp j (vector g hNg) : degreeLE 3 N) : K3 → ℂ) κ at hval
    rw [proj_restrict_apply hp j hNf, proj_restrict_apply hp j hNg] at hval
    have hh : P.eval (j : ℂ) * blockFourierCoefficient 3 p j f (Unitary.toUnits κ) =
        Q.eval (j : ℂ) * blockFourierCoefficient 3 p j g (Unitary.toUnits κ) := by
      apply mul_left_cancel₀ (inv_ne_zero two_pi_ne_zero)
      linear_combination hval
    simpa only [κ, RealKTypeCount.toUnits_mk hx] using hh

open RealOrthogonalBlock in
/-- The same exact relation on any three-coordinate compact coset in ambient rank. -/
theorem ambient_relation {n a r N : ℕ} (ha : a + 3 ≤ n) (hr : r + 1 < 3)
    (f g : Langlands.GeneralLinear n ℝ → ℂ)
    (x : Langlands.GeneralLinear n ℝ) (hx : x ∈ unitaryCompact ℝ n)
    (hNf : restrictLinear 3 (restrictCoset a ha x f) ∈ degreeLE 3 N)
    (hNg : restrictLinear 3 (restrictCoset a ha x g) ∈ degreeLE 3 N) (P Q : ℂ[X])
    (hrel : ∀ j : ℤ, ∀ y ∈ unitaryCompact ℝ n,
      P.eval (j : ℂ) * blockFourierCoefficient n (a + r) j f y =
        Q.eval (j : ℂ) * blockFourierCoefficient n (a + r) j g y) :
    aeval (-I • gen N hr) P (vector (restrictCoset a ha x f) hNf) =
      aeval (-I • gen N hr) Q (vector (restrictCoset a ha x g) hNg) := by
  apply (relation_iff hr _ _ hNf hNg P Q).mp
  intro j k hk
  rw [blockFourierCoefficient_restrictCoset a ha hr,
    blockFourierCoefficient_restrictCoset a ha hr]
  exact hrel j _ ((unitaryCompact ℝ n).mul_mem (block_mem_unitaryCompact a ha hk) hx)

open RealOrthogonalBlock in
theorem ambient_common_degree {ι : Type*} [Fintype ι] {n a : ℕ} (ha : a + 3 ≤ n)
    (fs : ι → Langlands.GeneralLinear n ℝ → ℂ)
    (hc : ∀ i, Continuous (fs i))
    (hK : ∀ i, fs i ∈ kFiniteVectors
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)) (unitaryCompact ℝ n))
    (x : Langlands.GeneralLinear n ℝ) (hx : x ∈ unitaryCompact ℝ n) :
    ∃ N, ∀ i, restrictLinear 3 (restrictCoset a ha x (fs i)) ∈ degreeLE 3 N :=
  exists_common_degree (fun i => restrictCoset a ha x (fs i))
    (fun i => continuous_restrictCoset a ha x (hc i))
    (fun i => restrictCoset_mem_kFiniteVectors a ha hx (hK i))

open Langlands.LocalFactor.Archimedean RealBlockFrobeniusMap RealBlockMultiplier
  RealStandardFiltration RealTailMultiplierPolynomial

/-- An actual normalized integral generic map satisfies an exact polynomial operator equation. -/
theorem generic_operator {N p ℓ : ℕ} {ds es : List RealBlock} {ε : ℤ} {τ : ℂ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - ε))
    (hdata : IsBlockFrobData 3 ds es p ε τ (genericMultiplier (ℓ : ℂ) ε))
    (f : KF 3 ds) (hNf : restrictLinear 3 (f : G3 → ℂ) ∈ degreeLE 3 N)
    (hNg : restrictLinear 3 (blockFrobMap hdata f : G3 → ℂ) ∈ degreeLE 3 N) :
    aeval (-I • gen N hdata.lt) (tailPolynomial ℓ)
        (vector (blockFrobMap hdata f) hNg) =
      (tailPolynomial ℓ).eval (ε : ℂ) • vector (f : G3 → ℂ) hNf := by
  have hh := (relation_iff hdata.lt (blockFrobMap hdata f) f hNg hNf
    (tailPolynomial ℓ) (C ((tailPolynomial ℓ).eval (ε : ℂ)))).mp
      (fun j x hx => by
        simpa only [eval_C] using
          RealIntegralGenericPolynomial.generic_frob_relation hℓ hε hpar hdata f j hx)
  simpa only [aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
    Module.End.one_apply] using hh

/-- An actual differential-sign tail is polynomial evaluation on the compact model. -/
theorem tail_operator {N p ℓ : ℕ} {ds es : List RealBlock} {ε : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (hdata : IsBlockFrobData 3 ds es p ε ((-1 : ℂ) ^ ℓ)
      (tailMultiplier ℓ ε ((-1 : ℂ) ^ ℓ)))
    (f : KF 3 ds) (hNf : restrictLinear 3 (f : G3 → ℂ) ∈ degreeLE 3 N)
    (hNg : restrictLinear 3 (blockFrobMap hdata f : G3 → ℂ) ∈ degreeLE 3 N) :
    vector (blockFrobMap hdata f) hNg =
      aeval (-I • gen N hdata.lt) (tailPolynomial ℓ) (vector (f : G3 → ℂ) hNf) := by
  have hh := (relation_iff hdata.lt (blockFrobMap hdata f) f hNg hNf
    1 (tailPolynomial ℓ)).mp (fun j x hx => by
      simp only [eval_one, one_mul]
      rw [blockFourierCoefficient_blockFrobMap hdata f hx]
      by_cases hj : Even (j - ε)
      · rw [tailPolynomial_eq hℓ hε hpar j hj]
      · rw [RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even
          hdata.lt hdata.par f hj x, mul_zero, mul_zero])
  simpa only [map_one, Module.End.one_apply] using hh

end Langlands.Archimedean.RealCompactPolynomialFourierRelation

namespace Langlands.Archimedean

open Polynomial Complex RealKTypeCount RealOrthogonalUncertainty
  RealCompactPolynomialFourierRelation in
/-- Exact equivalence between polynomial Fourier relations and compact generator equations. -/
def RealCompactPolynomialFourierRelationStatement : Prop :=
  ∀ (N p : ℕ) (hp : p + 1 < 3)
    (f g : Langlands.GeneralLinear 3 ℝ → ℂ)
    (hNf : restrictLinear 3 f ∈ degreeLE 3 N) (hNg : restrictLinear 3 g ∈ degreeLE 3 N)
    (P Q : ℂ[X]),
    (∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      P.eval (j : ℂ) * blockFourierCoefficient 3 p j f x =
        Q.eval (j : ℂ) * blockFourierCoefficient 3 p j g x) ↔
      aeval (-I • gen N hp) P (vector f hNf) =
        aeval (-I • gen N hp) Q (vector g hNg)

theorem realCompactPolynomialFourierRelation :
    RealCompactPolynomialFourierRelationStatement :=
  fun _ _ hp f g hNf hNg P Q =>
    RealCompactPolynomialFourierRelation.relation_iff hp f g hNf hNg P Q

end Langlands.Archimedean
