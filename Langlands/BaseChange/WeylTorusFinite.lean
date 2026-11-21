import Langlands.BaseChange.WeylIntegrationData
import Langlands.LinearAlgebra.MatrixSquarefreeCharpolyConjugacy

/-! # Finiteness of the rational Weyl group of `GL_n` -/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands
open Matrix _root_.Polynomial

universe u

variable {F : Type u} [Field F] {n : ℕ}

private theorem finite_commutingCharpolyFiber (A : Matrix (Fin n) (Fin n) F)
    (hA : A.charpoly.Separable) :
    Set.Finite {B : Matrix (Fin n) (Fin n) F | Commute B A ∧ B.charpoly = A.charpoly} := by
  classical
  let K := AlgebraicClosure F
  let ι := algebraMap F K
  let P := (A.map ι).charpoly
  have hP : P.Separable := by
    dsimp only [P]
    rw [Matrix.charpoly_map]
    exact hA.map
  let roots : Finset K := ⟨P.roots, nodup_roots hP⟩
  have hcard : roots.card = n := by
    change P.roots.card = n
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := (Finset.equivFinOfCardEq hcard).symm
  let d : Fin n → K := fun i => (e i).val
  have hd : Function.Injective d := Subtype.val_injective.comp e.injective
  have hdiag : (A.map ι).charpoly = (diagonal d).charpoly := by
    rw [charpoly_diagonal]
    calc
      P = (P.roots.map fun x => X - C x).prod :=
        (prod_multiset_X_sub_C_of_monic_of_roots_card_eq
          (Matrix.charpoly_monic _) IsAlgClosed.card_roots_eq_natDegree).symm
      _ = ∏ x ∈ roots, (X - C x) := rfl
      _ = ∏ i, (X - C (d i)) := by
        rw [← Finset.prod_coe_sort]
        exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  obtain ⟨g, hg⟩ := matrixConj_of_squarefree_charpoly_eq (A.map ι) (diagonal d)
    hP.squarefree hdiag
  let conjugate (B : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) K :=
    g.val * B.map ι * (g⁻¹).val
  have hinj : Function.Injective conjugate := by
    intro B D heq
    have heq' : B.map ι = D.map ι := by
      have h := congrArg (fun M => (g⁻¹).val * M * g.val) heq
      dsimp only [conjugate] at h
      simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using h
    ext i j
    exact ι.injective (congrArg (fun M => M i j) heq')
  let S := {B : Matrix (Fin n) (Fin n) F | Commute B A ∧ B.charpoly = A.charpoly}
  have hconj_diag (B : S) : conjugate B = diagonal (conjugate B).diag := by
    have hcomm : Commute (conjugate B) (diagonal d) := by
      rw [← hg]
      have hm := B.property.1.map (ι.mapMatrix (m := Fin n))
      change (B.val.map ι) * A.map ι = A.map ι * (B.val.map ι) at hm
      change (g.val * B.val.map ι * (g⁻¹).val) * (g.val * A.map ι * (g⁻¹).val) =
        (g.val * A.map ι * (g⁻¹).val) * (g.val * B.val.map ι * (g⁻¹).val)
      simpa only [mul_assoc, Units.inv_mul_cancel_left] using
        congrArg (fun M => g.val * M * (g⁻¹).val) hm
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · have hentry := congrArg (fun M => M i j) hcomm.eq
      rw [mul_diagonal, diagonal_mul, mul_comm (d i), ← sub_eq_zero, ← mul_sub] at hentry
      exact (mul_eq_zero.mp hentry).resolve_right (sub_ne_zero.mpr (hd.ne (Ne.symm hij))) |>.trans
        (diagonal_apply_ne _ hij).symm
  have hcharpoly (B : S) : (conjugate B).charpoly = P := by
    dsimp only [conjugate]
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, Matrix.charpoly_map,
      B.property.2, ← Matrix.charpoly_map]
  have hroot (B : S) (i : Fin n) : (conjugate B).diag i ∈ roots := by
    change (conjugate B).diag i ∈ P.roots
    apply (mem_roots (Matrix.charpoly_monic _).ne_zero).2
    change P.IsRoot ((conjugate B).diag i)
    rw [← hcharpoly B, congrArg Matrix.charpoly (hconj_diag B), Matrix.charpoly_diagonal,
      IsRoot, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  let toRoots (B : S) (i : Fin n) : roots := ⟨(conjugate B).diag i, hroot B i⟩
  have : Finite S := Finite.of_injective toRoots (by
    intro B D heq
    apply Subtype.ext
    apply hinj
    rw [hconj_diag B, hconj_diag D]
    congr 1
    funext i
    exact congrArg Subtype.val (congrFun heq i))
  exact Set.toFinite S

namespace WeylTorus

/-- The rational normalizer of a maximal torus modulo that torus is finite. -/
theorem finite_rationalWeylGroup (T : WeylTorus F n) : Finite T.RationalWeylGroup := by
  classical
  obtain ⟨γ, hγ, hT⟩ := T.property
  let N := Subgroup.normalizer (T.val : Set (GeneralLinear n F))
  let S := {B : Matrix (Fin n) (Fin n) F | Commute B γ.val ∧ B.charpoly = γ.val.charpoly}
  let : Finite S := (finite_commutingCharpolyFiber γ.val hγ).to_subtype
  have hγT : γ ∈ T.val := by
    rw [← hT, glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  let conjugate (x : N) : GeneralLinear n F := x.val * γ * x.val⁻¹
  have hmem (x : N) : conjugate x ∈ glCentralizer γ :=
    hT ▸ (Subgroup.mem_normalizer_iff.mp x.property γ).mp hγT
  let toFiber (q : T.RationalWeylGroup) : S := ⟨(conjugate q.out).val, by
    constructor
    · have h := hmem q.out
      rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at h
      exact (show Commute (conjugate q.out) γ from h).map (Units.coeHom _)
    · change (q.out.val.val * γ.val * (q.out.val⁻¹).val).charpoly = _
      rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]⟩
  refine Finite.of_injective toFiber ?_
  intro q r heq
  have hconj : conjugate q.out = conjugate r.out :=
    Units.ext (congrArg Subtype.val heq)
  have hcomm : q.out.val⁻¹ * r.out.val * γ = γ * (q.out.val⁻¹ * r.out.val) := by
    have h := congrArg (fun z => q.out.val⁻¹ * z * r.out.val) hconj.symm
    simpa [conjugate, mul_assoc] using h
  have hcoset : (q.out : T.RationalWeylGroup) = r.out := by
    apply QuotientGroup.eq.mpr
    change q.out.val⁻¹ * r.out.val ∈ T.val
    have hcentral : q.out.val⁻¹ * r.out.val ∈ glCentralizer γ := by
      rwa [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg (fun H : Subgroup (GeneralLinear n F) => q.out.val⁻¹ * r.out.val ∈ H) hT).mp
      hcentral
  simpa only [Quotient.out_eq'] using hcoset

/-- The denominator of the Weyl integration weight is a positive cardinal. -/
theorem natCard_rationalWeylGroup_pos (T : WeylTorus F n) :
    0 < Nat.card T.RationalWeylGroup := by
  let := finite_rationalWeylGroup T
  exact Nat.card_pos

end WeylTorus

end Langlands.BaseChange
