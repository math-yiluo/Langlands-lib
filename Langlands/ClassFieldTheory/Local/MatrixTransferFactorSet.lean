import Langlands.Algebra.BrauerCorestriction.PiMatrixKronecker
import Langlands.Algebra.MatrixGaloisCocycle
import Langlands.Cohomology.Tate.CosetTransfer

noncomputable section

open Matrix Langlands.CentralSimple.SemilinearGaloisAction

namespace Langlands.BrauerCorestriction

universe u v

section Kronecker

variable (N : Type u) [Field N] (Q : Type v) [Fintype Q] [DecidableEq Q] (m : ℕ)

/-- The Kronecker product of an actual family of invertible matrices. -/
def kroneckerUnits : (Q → GL (Fin m) N) →* GL (Q → Fin m) N where
  toFun P :=
    { val := kroneckerMultilinear N Q m (fun q => (P q : Matrix (Fin m) (Fin m) N))
      inv := kroneckerMultilinear N Q m (fun q => ((P q)⁻¹ : GL (Fin m) N))
      val_inv := by
        rw [← kroneckerMultilinear_mul]
        have h : ((fun q => (P q : Matrix (Fin m) (Fin m) N)) *
            fun q => (((P q)⁻¹ : GL (Fin m) N) : Matrix (Fin m) (Fin m) N)) = 1 :=
          funext fun q => (P q).val_inv
        rw [h, kroneckerMultilinear_one]
      inv_val := by
        rw [← kroneckerMultilinear_mul]
        have h : ((fun q => (((P q)⁻¹ : GL (Fin m) N) : Matrix (Fin m) (Fin m) N)) *
            fun q => (P q : Matrix (Fin m) (Fin m) N)) = 1 :=
          funext fun q => (P q).inv_val
        rw [h, kroneckerMultilinear_one] }
  map_one' := Units.ext (kroneckerMultilinear_one N Q m)
  map_mul' P S := Units.ext (kroneckerMultilinear_mul N Q m _ _)

theorem kroneckerUnits_scalar (a : Q → Nˣ) :
    kroneckerUnits N Q m (fun q => GeneralLinearGroup.scalar (Fin m) (a q)) =
      GeneralLinearGroup.scalar (Q → Fin m) (∏ q, a q) := by
  apply Units.ext
  ext i j
  simp only [kroneckerUnits, MonoidHom.coe_mk, OneHom.coe_mk, kroneckerMultilinear_apply,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · rw [ite_eq_right hij]
    have h : ∃ q, i q ≠ j q := by
      by_contra! h
      exact hij (funext h)
    obtain ⟨q, hq⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (ite_eq_right hq)

end Kronecker

section Transfer

variable (K N : Type u) [Field K] [Field N] [Algebra K N]
  (H : Subgroup Gal(N/K)) [Fintype (Gal(N/K) ⧸ H)] [DecidableEq (Gal(N/K) ⧸ H)]
  (m : ℕ)

attribute [local instance] coefficientGLAction

local notation "G" => Gal(N/K)
local notation "Q" => G ⧸ H
local notation "h" => Langlands.Tate.schreierElement H
local notation "U" => kroneckerUnits N Q m

/-- The permutation unit that reindexes rows and columns by the left coset action. -/
def cosetPermutationUnit (g : G) : GL (Q → Fin m) N :=
  permUnit (indexPerm (MulAction.toPerm g)).symm

theorem cosetPermutationUnit_mul (g t : G) :
    cosetPermutationUnit K N H m (g * t) =
      cosetPermutationUnit K N H m g * cosetPermutationUnit K N H m t := by
  unfold cosetPermutationUnit
  rw [← permUnit_trans]
  congr 1
  apply Equiv.ext
  intro i
  funext q
  simp only [Equiv.trans_apply, indexPerm_symm_apply]
  change i ((g * t) • q) = i (g • (t • q))
  rw [mul_smul]

theorem cosetPermutationUnit_coefficients (g t : G) :
    g • cosetPermutationUnit K N H m t = cosetPermutationUnit K N H m t := by
  apply Units.ext
  exact permUnit_map g.toRingHom (indexPerm (MulAction.toPerm t)).symm

theorem cosetPermutationUnit_conj_kroneckerUnits (g : G) (P : Q → GL (Fin m) N) :
    cosetPermutationUnit K N H m g * U P * (cosetPermutationUnit K N H m g)⁻¹ =
      U (fun q => P (g⁻¹ • q)) := by
  apply Units.ext
  change ((cosetPermutationUnit K N H m g : GL (Q → Fin m) N) : Matrix _ _ N) *
    kroneckerMultilinear N Q m (fun q => (P q : Matrix _ _ N)) *
    (((cosetPermutationUnit K N H m g)⁻¹ : GL (Q → Fin m) N) : Matrix _ _ N) = _
  unfold cosetPermutationUnit
  rw [permUnit_conj, ← kroneckerMultilinear_reindex]
  rfl

theorem kroneckerUnits_coefficients (g : G) (P : Q → GL (Fin m) N) :
    g • U P = U (fun q => g • P q) := by
  apply Units.ext
  exact kroneckerMultilinear_map g.toRingHom _

omit [Fintype Q] [DecidableEq Q] in
theorem mul_cosetRepresentative (g : G) (q : Q) :
    g * (g⁻¹ • q).out = q.out * (h g q : G) := by
  change _ = q.out * (q.out⁻¹ * g * (g⁻¹ • q).out)
  group

omit [Fintype Q] [DecidableEq Q] in
theorem schreierElement_mul (g t : G) (q : Q) :
    h (g * t) q = h g q * h t (g⁻¹ • q) := by
  apply Subtype.ext
  change q.out⁻¹ * (g * t) * ((g * t)⁻¹ • q).out =
    (q.out⁻¹ * g * (g⁻¹ • q).out) * ((g⁻¹ • q).out⁻¹ * t * (t⁻¹ • (g⁻¹ • q)).out)
  rw [_root_.mul_inv_rev, mul_smul]
  group

/-- The Kronecker lift for the conjugate tensor, formed from the supplied subgroup lifts. -/
def tensorTransferMatrixLift (P : H → GL (Fin m) N) (g : G) : GL (Q → Fin m) N :=
  U (fun q => q.out • P (h g q)) * cosetPermutationUnit K N H m g

/-- The scalar defect of the tensor lift is the product of the conjugated Schreier factors. -/
theorem tensorTransferMatrixLift_mul (P : H → GL (Fin m) N) (c : H → H → Nˣ)
    (hP : ∀ s t, P s * ((s : G) • P t) = GeneralLinearGroup.scalar (Fin m) (c s t) * P (s * t))
    (g t : G) :
    tensorTransferMatrixLift K N H m P g * (g • tensorTransferMatrixLift K N H m P t) =
      GeneralLinearGroup.scalar (Q → Fin m) (∏ q : Q, q.out • c (h g q) (h t (g⁻¹ • q))) *
        tensorTransferMatrixLift K N H m P (g * t) := by
  let B (s : G) (q : Q) := q.out • P (h s q)
  let R := cosetPermutationUnit K N H m
  let a (q : Q) := q.out • c (h g q) (h t (g⁻¹ • q))
  have hB (q : Q) : B g q * (g • B t (g⁻¹ • q)) =
      GeneralLinearGroup.scalar (Fin m) (a q) * B (g * t) q := by
    dsimp only [B, a]
    rw [← mul_smul, mul_cosetRepresentative K N H, mul_smul, ← smul_mul', hP,
      smul_mul', coefficientGLAction_scalar, schreierElement_mul K N H]
  have hR : g • R t = R t := cosetPermutationUnit_coefficients K N H m g t
  have hperm : R g * R t = R (g * t) := (cosetPermutationUnit_mul K N H m g t).symm
  have hconj : R g * (g • U (B t)) * (R g)⁻¹ =
      U (fun q => g • B t (g⁻¹ • q)) := by
    rw [kroneckerUnits_coefficients, cosetPermutationUnit_conj_kroneckerUnits]
  change (U (B g) * R g) * (g • (U (B t) * R t)) =
    GeneralLinearGroup.scalar (Q → Fin m) (∏ q, a q) * (U (B (g * t)) * R (g * t))
  rw [smul_mul', hR]
  calc
    _ = U (B g) * (R g * (g • U (B t)) * (R g)⁻¹) * (R g * R t) := by group
    _ = U (fun q => B g q * (g • B t (g⁻¹ • q))) * R (g * t) := by
      rw [hconj, hperm, ← map_mul]
      rfl
    _ = _ := by
      simp only [hB]
      rw [show (fun q => GeneralLinearGroup.scalar (Fin m) (a q) * B (g * t) q) =
        (fun q => GeneralLinearGroup.scalar (Fin m) (a q)) * B (g * t) from rfl,
        map_mul, kroneckerUnits_scalar, mul_assoc]

end Transfer

end Langlands.BrauerCorestriction
