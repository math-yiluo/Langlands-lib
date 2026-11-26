import Langlands.BaseChange.TwistedCharacter.AdjointMultiplicity
import Langlands.BaseChange.TwistedCharacter.RegularLine
import Langlands.BaseChange.TwistedCharacter.SemidirectReduction

/-! # Comparison with Clozel regularity on the generator component -/

noncomputable section

namespace Langlands.BaseChange

open Filter Matrix Module _root_.Polynomial
open scoped SemidirectProduct

section Pencil

variable {R S : Type*} [CommRing R] [CommRing S]
  {I : Type*} [Fintype I] [DecidableEq I]

private def pencilDet (B A : Matrix I I R) : R[X] :=
  ((X : R[X]) • B.map (C : R →+* R[X]) - A.map (C : R →+* R[X])).det

private theorem pencilDet_map (f : R →+* S) (B A : Matrix I I R) :
    (pencilDet B A).map f = pencilDet (B.map f) (A.map f) := by
  change mapRingHom f (pencilDet B A) = _
  unfold pencilDet
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.smul_apply, smul_eq_mul]

private theorem pencilDet_mul (B A : Matrix I I R) :
    pencilDet B (B * A) = C B.det * A.charpoly := by
  unfold pencilDet Matrix.charpoly
  rw [RingHom.map_det, ← Matrix.det_mul]
  apply congrArg Matrix.det
  have hscalar : Matrix.scalar I (X : R[X]) = (X : R[X]) • (1 : Matrix I I R[X]) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.scalar, Matrix.smul_apply]
  rw [Matrix.charmatrix, hscalar, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← map_mul]
  rfl

end Pencil

section Multiplicity

universe u v

variable {F : Type u} [Field F] [CharZero F] {E : Type v} [CommRing E] [Algebra F E]
  {l n : ℕ} (σ : E ≃ₐ[F] E)

local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "G" => GeneralLinear n E

/-- On the full generator component the adjoint eigenvalue `1` has algebraic
multiplicity at least `n`. -/
theorem le_rootMultiplicity_twistedMatrixConj (hE : IsCyclicAlgebra σ l) (g₀ : G) :
    haveI : Module.Finite F E := hE.1
    n ≤ (LinearMap.charpoly (twistedMatrixConj σ g₀).toLinearMap).rootMultiplicity 1 := by
  have : Module.Finite F E := hE.1
  obtain ⟨g₁, h₁⟩ := exists_sigmaRegular_of_cyclic (n := n) σ hE
  let b := Module.finBasis F Mat
  let e := LinearMap.toMatrixAlgEquiv b
  let right : Mat →ₗ[F] End F Mat := (LinearMap.mul F Mat).flip
  let left : Mat →ₗ[F] End F Mat :=
    { toFun := fun a => (Algebra.lmul F Mat a).comp σ.mapMatrix.toLinearMap
      map_add' := fun a b => by simp [LinearMap.add_comp]
      map_smul' := fun c a => by simp [LinearMap.smul_comp] }
  let R := e.toLinearMap.comp right
  let A := e.toLinearMap.comp (left - right)
  let T (g : G) : End F Mat := (twistedMatrixConj σ g).toLinearMap
  let p := pencilDet (matrixLinePolynomial (R g₀.val) (R g₁.val))
    (matrixLinePolynomial (A g₀.val) (A g₁.val))
  have hA (g : G) : A g.val = R g.val * e (T g - 1) := by
    change e ((left - right) g.val) = e (right g.val) * e (T g - 1)
    rw [← map_mul]
    apply congrArg e
    apply LinearMap.ext
    intro X
    change g.val * σ.mapMatrix X - X * g.val = (twistedMatrixConj σ g X - X) * g.val
    simp only [twistedMatrixConj_apply, sub_mul, mul_assoc, Units.inv_mul, mul_one]
  have hp (t : F) (g : G) (hg : g.val = g₀.val + t • (g₁.val - g₀.val)) :
      p.map (evalRingHom t) = C (R g.val).det * (T g - 1).charpoly := by
    have hl (f : Mat →ₗ[F] Matrix (Fin (finrank F Mat)) (Fin (finrank F Mat)) F) :
        (matrixLinePolynomial (f g₀.val) (f g₁.val)).map (evalRingHom t) = f g.val := by
      rw [matrixLinePolynomial_eval, hg, map_add, map_smul, map_sub]
    dsimp only [p]
    rw [pencilDet_map, hl R, hl A, hA, pencilDet_mul]
    congr 1
    exact LinearMap.charpoly_toMatrix (T g - 1) b
  have htrail (g : G) : (T g - 1).charpoly.natTrailingDegree = (T g).charpoly.rootMultiplicity 1 := by
    rw [rootMultiplicity_eq_natTrailingDegree, ← LinearMap.charpoly_sub_smul, one_smul]
  have hdet : (R g₀.val).det ≠ 0 := by
    apply isUnit_iff_ne_zero.1
    apply (Matrix.isUnit_iff_isUnit_det _).1
    change IsUnit (e (right g₀.val))
    apply IsUnit.map e.toAlgHom
    exact (Module.End.isUnit_iff _).2 (g₀.mulRightLinearEquiv F).bijective
  change n ≤ (T g₀).charpoly.rootMultiplicity 1
  rw [← htrail]
  apply le_natTrailingDegree (LinearMap.charpoly_monic _).ne_zero
  intro k hk
  have hvan : ∀ᶠ t : F in cofinite, (p.coeff k).eval t = 0 := by
    filter_upwards [eventually_sigmaRegular_on_matrixLine σ hE g₀ g₁ h₁] with t ht
    obtain ⟨g, hg, hreg⟩ := ht
    have hcoeff : (T g - 1).charpoly.coeff k = 0 := by
      apply coeff_eq_zero_of_lt_natTrailingDegree
      rwa [htrail, rootMultiplicity_twistedMatrixConj_of_sigmaRegular σ hE g hreg]
    change evalRingHom t (p.coeff k) = 0
    rw [← coeff_map, hp t g hg, coeff_C_mul, hcoeff, mul_zero]
  have hzero : p.coeff k = 0 := by
    by_contra hne
    obtain ⟨t, ht, ht'⟩ := (hvan.and (eventually_eval_ne_zero_cofinite hne)).exists
    exact ht' ht
  have hzero₀ : (p.map (evalRingHom 0)).coeff k = 0 := by
    rw [coeff_map, hzero, map_zero]
  rw [hp 0 g₀ (by simp), coeff_C_mul] at hzero₀
  exact (mul_eq_zero.mp hzero₀).resolve_left hdet

end Multiplicity

theorem sigmaRegularCyclicGLComparison.{u, v} : SigmaRegularCyclicGLComparisonStatement.{u, v} := by
  intro F _ _ E _ _ σ l n hE
  have : NeZero l := ⟨hE.pos.ne'⟩
  have : Module.Finite F E := hE.1
  intro δ hδ y hy
  have hy' : y.right = cyclicGenerator l := hy
  change (LinearMap.charpoly
    (twistedMatrixConj (cyclicPowerHom σ hE.pow_eq_one (cyclicGenerator l)) δ).toLinearMap
    ).rootMultiplicity 1 ≤ (cyclicGLAdjoint y).charpoly.rootMultiplicity 1
  unfold cyclicGLAdjoint
  rw [hy', cyclicPowerHom_generator, rootMultiplicity_twistedMatrixConj_of_sigmaRegular σ hE δ hδ]
  exact le_rootMultiplicity_twistedMatrixConj σ hE y.left

/-- The character theorem on the cyclic semidirect model implies the full twisted
integrability proposition. -/
def TwistedCharacterFromCyclicGLStatement.{u, v, uW} : Prop :=
  CyclicGLCharacterRegularityStatement.{u, v, uW} →
    TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}

theorem twistedCharacterFromCyclicGL.{u, v, uW} : TwistedCharacterFromCyclicGLStatement.{u, v, uW} :=
  fun h => twistedCharacterSemidirectReduction h sigmaRegularCyclicGLComparison

end Langlands.BaseChange
