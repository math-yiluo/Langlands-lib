import Langlands.Representation.Archimedean.DiagonalEnvelopingProjection
import Langlands.Representation.Archimedean.LowerVermaCentral

/-! # Diagonal polynomials from individual matrix factors -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

open Langlands.Algebra Langlands.Algebra.UniversalEnveloping MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

section Factors

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (i : ι)

local notation "M" => Matrix (Fin (n i)) (Fin (n i)) ℂ
local notation "L" => GLProd ℂ n
local notation "U" => UniversalEnvelopingAlgebra ℂ (GLProd ℂ n)

/-- The additive Lie inclusion into one matrix place. -/
def matrixFactorLieInclusion : M →ₗ⁅ℂ⁆ L :=
  { LinearMap.single ℂ (fun j => Matrix (Fin (n j)) (Fin (n j)) ℂ) i with
    map_lie' := fun {x y} => by
      change (Pi.single i ⁅x, y⁆ : L) = ⁅(Pi.single i x : L), (Pi.single i y : L)⁆
      rw [Ring.lie_def, Ring.lie_def, ← Pi.single_mul, ← Pi.single_mul, Pi.single_sub] }

omit [Fintype ι] in
@[simp]
theorem matrixFactorLieInclusion_apply (x : M) : matrixFactorLieInclusion n i x = Pi.single i x := rfl

omit [Fintype ι] in
private theorem commute_enveloping_of_lie (x : L) (hx : ∀ y : M, ⁅x, matrixFactorLieInclusion n i y⁆ = 0)
    (a : UniversalEnvelopingAlgebra ℂ M) :
    Commute (UniversalEnvelopingAlgebra.ι ℂ x) (LieEnvelopingEquiv.map (matrixFactorLieInclusion n i) a) := by
  obtain ⟨N, hN⟩ := exists_mem_degreeFiltration ℂ M a
  replace hN := degreeFiltration_le_wordSpan ℂ M N hN
  induction hN using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, -, rfl⟩ := ha
    induction l with
    | nil => rw [word_nil, map_one]; exact Commute.one_right _
    | cons y l ih =>
      rw [word_cons, map_mul, LieEnvelopingEquiv.map_generator]
      apply Commute.mul_right _ ih
      have h := (UniversalEnvelopingAlgebra.ι ℂ).map_lie x (matrixFactorLieInclusion n i y)
      rw [hx, map_zero, Ring.lie_def] at h
      exact sub_eq_zero.mp h.symm
  | zero => rw [map_zero]; exact Commute.zero_right _
  | add x y _ _ hx hy => rw [map_add]; exact hx.add_right hy
  | smul c x _ hx =>
    rw [map_smul, Algebra.smul_def]
    exact (Algebra.commute_algebraMap_right _ _).mul_right hx

omit [Fintype ι] in
private theorem matrixFactor_map_mem_center (z : VermaGL.center (n i)) :
    LieEnvelopingEquiv.map (matrixFactorLieInclusion n i) z.val ∈ Subalgebra.center ℂ U := by
  let j := matrixFactorLieInclusion n i
  let J := LieEnvelopingEquiv.map j
  apply mem_center_of_commute
  intro x
  have hpart : Commute (UniversalEnvelopingAlgebra.ι ℂ (j (x i))) (J z.val) := by
    rw [← LieEnvelopingEquiv.map_generator]
    exact (show Commute (UniversalEnvelopingAlgebra.ι ℂ (x i)) z.val from
      Subalgebra.mem_center_iff.mp z.property _).map J
  have hrest : Commute (UniversalEnvelopingAlgebra.ι ℂ (x - j (x i))) (J z.val) := by
    apply commute_enveloping_of_lie n i
    intro y
    funext k
    change ((x - j (x i)) k * j y k) - (j y k * (x - j (x i)) k) = 0
    by_cases h : k = i
    · subst k
      simp [j, Pi.sub_apply]
    · simp [j, Pi.single_eq_of_ne h]
  have h := hpart.add_left hrest
  rw [← map_add, add_sub_cancel] at h
  exact h

/-- The centre of one matrix factor acts through the actual product centre. -/
def matrixFactorCenterInclusion : VermaGL.center (n i) →ₐ[ℂ] Subalgebra.center ℂ U :=
  ((LieEnvelopingEquiv.map (matrixFactorLieInclusion n i)).comp (Subalgebra.center ℂ _).val).codRestrict
    _ (matrixFactor_map_mem_center n i)

omit [Fintype ι] in
@[simp]
theorem matrixFactorCenterInclusion_val (z : VermaGL.center (n i)) :
    (matrixFactorCenterInclusion n i z).val = LieEnvelopingEquiv.map (matrixFactorLieInclusion n i) z.val := rfl

end Factors

section OneFactor

open VermaPBW

variable (r : ℕ)

/-- Evaluation of the one-factor matrix product. -/
def unitMatrixLieEquiv : GLProd ℂ (fun _ : Unit => r) ≃ₗ⁅ℂ⁆ Matrix (Fin r) (Fin r) ℂ where
  toFun x := x ()
  invFun x _ := x
  left_inv x := by funext j; cases j; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

local notation "S" => (fun _ : Unit => r)
local notation "E" => LieEnvelopingEquiv.enveloping (unitMatrixLieEquiv r)

@[simp]
private theorem unitMatrixLieEquiv_basis (p q : Fin r) :
    unitMatrixLieEquiv r (glBasis ℂ S ⟨(), p, q⟩) = unitE r (p, q) := by
  rw [glBasis_apply]
  change unit ℂ S () p q () = _
  rw [unit, Pi.single_eq_same]
  rfl

private theorem psi_envelopingMap_diagonal (μ : DiagonalCoordinate S → ℂ)
    (p : MvPolynomial (DiagonalCoordinate S) ℂ) :
    Psi r (vVal r (fun a => μ ⟨(), a⟩) 0) (E (diagonalPolynomialInclusion S p)) = eval μ p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one,
      map_smul, Psi_one, smul_eq_mul, mul_one, MvPolynomial.algebraMap_eq, eval_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p a hp =>
    obtain ⟨⟨⟩, a⟩ := a
    rw [map_mul, map_mul, diagonalPolynomialInclusion_X, LieEnvelopingEquiv.enveloping_generator,
      unitMatrixLieEquiv_basis]
    rw [Psi_mul_unitE_lo r _ _ (⟨(a, a), lt_irrefl _⟩ : LoIdx r)]
    rw [vVal_diag, hp, map_mul, eval_X, mul_comm]

private theorem psi_envelopingMap_eq_zero_of_pos (μ : DiagonalCoordinate S → ℂ)
    {x : UniversalEnvelopingAlgebra ℂ (GLProd ℂ S)}
    (hx : x ∈ positiveWeightRightIdeal (glBasis ℂ S) (deg S)) :
    Psi r (vVal r (fun a => μ ⟨(), a⟩) 0) (E x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, a, b⟩, hab, y, rfl⟩ := hx
    have h := (deg_pos_iff S ⟨(), a, b⟩).1 hab
    rw [map_mul, LieEnvelopingEquiv.enveloping_generator, unitMatrixLieEquiv_basis,
      Psi_unitE_up_mul r _ _ (⟨(a, b), h⟩ : UpIdx r)]
    simp [vVal, supCoeff, h]
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_zero]

/-- The singleton product gives the Library's lower Verma Harish-Chandra polynomial. -/
theorem diagonalCenterPolynomial_unit (z : VermaGL.center r) :
    diagonalCenterPolynomial S (LieEnvelopingEquiv.center (E).symm z) =
      rename (Sigma.mk ()) (VermaCentral.gamC r z) := by
  apply MvPolynomial.funext
  intro μ
  let w := LieEnvelopingEquiv.center (E).symm z
  have h := psi_envelopingMap_eq_zero_of_pos r μ (sub_diagonalCenterPolynomial_mem S w)
  rw [map_sub, map_sub, psi_envelopingMap_diagonal] at h
  have hw : E w.val = z.val := AlgEquiv.apply_symm_apply E z.val
  rw [hw, sub_eq_zero] at h
  rw [eval_rename, VermaCentral.gamC_apply, VermaCentral.eval_gam]
  exact h.symm

end OneFactor

/-- The diagonal polynomial of an included central element uses the variables of its own
matrix place. -/
theorem diagonalCenterPolynomial_factor {ι : Type u} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (i : ι) (z : VermaGL.center (n i)) :
    diagonalCenterPolynomial n (matrixFactorCenterInclusion n i z) =
      rename (Sigma.mk i) (VermaCentral.gamC (n i) z) := by
  let S := fun _ : Unit => n i
  let e := unitMatrixLieEquiv (n i)
  let E := LieEnvelopingEquiv.enveloping e
  let j := matrixFactorLieInclusion n i
  let J := j.comp e.toLieHom
  let f : DiagonalCoordinate S → DiagonalCoordinate n := fun a => ⟨i, a.2⟩
  let w : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ S)) :=
    LieEnvelopingEquiv.center E.symm z
  have hj : LieEnvelopingEquiv.map J = (LieEnvelopingEquiv.map j).comp E.toAlgHom := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change LieEnvelopingEquiv.map J (UniversalEnvelopingAlgebra.ι ℂ x) =
      LieEnvelopingEquiv.map j (E (UniversalEnvelopingAlgebra.ι ℂ x))
    rw [LieEnvelopingEquiv.map_generator, LieEnvelopingEquiv.enveloping_generator,
      LieEnvelopingEquiv.map_generator]
    rfl
  have hdiag (a : DiagonalCoordinate S) : J (glBasis ℂ S ⟨a.1, a.2, a.2⟩) =
      glBasis ℂ n ⟨(f a).1, (f a).2, (f a).2⟩ := by
    obtain ⟨⟨⟩, p⟩ := a
    change j (e (glBasis ℂ S ⟨(), p, p⟩)) = glBasis ℂ n ⟨i, p, p⟩
    rw [unitMatrixLieEquiv_basis, glBasis_apply]
    rfl
  have hpos (a : Coord S) (ha : 0 < deg S a) :
      ∃ b : Coord n, 0 < deg n b ∧ J (glBasis ℂ S a) = glBasis ℂ n b := by
    obtain ⟨⟨⟩, p, q⟩ := a
    refine ⟨⟨i, p, q⟩, ha, ?_⟩
    change j (e (glBasis ℂ S ⟨(), p, q⟩)) = glBasis ℂ n ⟨i, p, q⟩
    rw [unitMatrixLieEquiv_basis, glBasis_apply]
    rfl
  have hsub : (matrixFactorCenterInclusion n i z).val - LieEnvelopingEquiv.map J w.val = 0 := by
    rw [matrixFactorCenterInclusion_val, hj, AlgHom.comp_apply]
    change LieEnvelopingEquiv.map j z.val - LieEnvelopingEquiv.map j (E w.val) = 0
    rw [show E w.val = z.val from AlgEquiv.apply_symm_apply E z.val, sub_self]
  rw [diagonalCenterPolynomial_eq_rename_of_congruence J f hdiag hpos
    (matrixFactorCenterInclusion n i z) w (by rw [hsub]; exact (positiveWeightRightIdeal _ _).zero_mem)]
  rw [show diagonalCenterPolynomial S w = _ from diagonalCenterPolynomial_unit (n i) z]
  rw [rename_rename]
  rfl

end Langlands.Archimedean.Kostant
