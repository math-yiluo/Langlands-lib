import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.OrbitalIntegral

/-! # Norms of regular matrices in their commutative centralizer algebra -/

noncomputable section

namespace Langlands.BaseChange

open Matrix _root_.Polynomial
open Langlands.JacquetLanglands

universe u v

section Evaluation

variable {R : Type v} [CommRing R] {n : ℕ}

/-- Evaluate the algebra adjoining a root of the characteristic polynomial at
the matrix itself. -/
def charpolyRootEvaluation (A : Matrix (Fin n) (Fin n) R) :
    AdjoinRoot A.charpoly →ₐ[R] Matrix (Fin n) (Fin n) R :=
  Ideal.Quotient.liftₐ _ (aeval A) fun _ h => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp h
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]

@[simp] theorem charpolyRootEvaluation_mk (A : Matrix (Fin n) (Fin n) R) (q : R[X]) :
    charpolyRootEvaluation A (AdjoinRoot.mk A.charpoly q) = aeval A q := rfl

@[simp] theorem charpolyRootEvaluation_root (A : Matrix (Fin n) (Fin n) R) :
    charpolyRootEvaluation A (AdjoinRoot.root A.charpoly) = A :=
  aeval_X A

theorem charpolyRootEvaluation_injective [Nontrivial R]
    (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (hv : IsUnit (cyclicBasisMatrix A v)) :
    Function.Injective (charpolyRootEvaluation A) := by
  let p := A.charpoly
  let pb := AdjoinRoot.powerBasis' A.charpoly_monic
  have hn : p.natDegree = n := by simp [p, Matrix.charpoly_natDegree_eq_dim]
  let b : Module.Basis (Fin n) R (AdjoinRoot p) := pb.basis.reindex (finCongr hn)
  have hb (j : Fin n) : b j = AdjoinRoot.root p ^ (j : ℕ) := by
    simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
    rfl
  apply (injective_iff_map_eq_zero (charpolyRootEvaluation A)).2
  intro x hx
  let c : Fin n → R := b.repr x
  have heval : charpolyRootEvaluation A x = ∑ j : Fin n, c j • A ^ (j : ℕ) := by
    rw [← b.sum_repr x, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, map_pow, charpolyRootEvaluation_root]
  have hsum : ∑ j : Fin n, c j • A ^ (j : ℕ) = 0 := heval.symm.trans hx
  let C := cyclicBasisMatrix A v
  have hz : C *ᵥ c = 0 := by
    calc
      C *ᵥ c = ∑ j : Fin n, c j • C.col j := by
        ext i
        simp only [mulVec_apply_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = (∑ j : Fin n, c j • A ^ (j : ℕ)) *ᵥ v := by
        simp only [sum_mulVec, smul_mulVec, C, cyclicBasisMatrix_col]
      _ = 0 := by rw [hsum, zero_mulVec]
  have hc : c = 0 := by
    let W := hv.unit
    have hW : (W : Matrix (Fin n) (Fin n) R) = C := hv.unit_spec
    have h := congrArg (fun z : Fin n → R => (↑W⁻¹ : Matrix (Fin n) (Fin n) R) *ᵥ z) hz
    rw [← hW, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec, mulVec_zero] at h
    exact h
  apply b.repr.injective
  ext j
  simp only [map_zero, Finsupp.zero_apply]
  exact congrFun hc j

private theorem charpolyRootEvaluation_unit [Nontrivial R]
    (A d : GeneralLinear n R) (v : Fin n → R) (hv : IsUnit (cyclicBasisMatrix A.val v))
    (h : Commute d A) :
    ∃ b : (AdjoinRoot A.val.charpoly)ˣ,
      Units.map (charpolyRootEvaluation A.val).toMonoidHom b = d := by
  let e := charpolyRootEvaluation A.val
  have hinj := charpolyRootEvaluation_injective A.val v hv
  have preimage (a : GeneralLinear n R) (ha : Commute a A) :
      ∃ u : AdjoinRoot A.val.charpoly, e u = a.val := by
    obtain ⟨c, hc⟩ := exists_sum_pow_of_commute hv (ha.map (Units.coeHom _))
    change a.val = ∑ j : Fin n, c j • A.val ^ (j : ℕ) at hc
    refine ⟨AdjoinRoot.mk _ (∑ j : Fin n, monomial (j : ℕ) (c j)), ?_⟩
    change charpolyRootEvaluation A.val _ = _
    rw [charpolyRootEvaluation_mk, hc, map_sum]
    simp only [aeval_monomial, Algebra.smul_def]
  obtain ⟨b, hb⟩ := preimage d h
  obtain ⟨b', hb'⟩ := preimage d⁻¹ h.inv_left
  have hbb' : b * b' = 1 := hinj (by rw [map_mul, map_one, hb, hb']; exact d.val_inv)
  have hb'b : b' * b = 1 := hinj (by rw [map_mul, map_one, hb, hb']; exact d.inv_val)
  exact ⟨⟨b, b', hbb', hb'b⟩, Units.ext hb⟩

end Evaluation

section Cyclic

variable {F : Type u} {E : Type v} [Field F] [CommRing E] [Algebra F E]
  {n l : ℕ} (σ : E ≃ₐ[F] E) (γ : GeneralLinear n F)

local notation "A" => Units.val (baseChange F E n γ)
local notation "p" => Matrix.charpoly A

private theorem baseChange_matrix_map_automorphism : (A).map σ.toRingHom = A := by
  ext i j
  exact σ.commutes (γ i j)

private theorem charpolyBaseChange_map_automorphism :
    (p).map σ.toRingHom = p := by
  rw [← Matrix.charpoly_map, baseChange_matrix_map_automorphism σ γ]

/-- The induced automorphism of the characteristic-polynomial algebra applies
the coefficient automorphism and fixes the distinguished root. -/
def centralizerAlgebraAut : AdjoinRoot p ≃ₐ[F] AdjoinRoot p :=
  AdjoinRoot.mapAlgEquiv σ p p
    (Associated.of_eq (charpolyBaseChange_map_automorphism σ γ))

private theorem charpolyRootEvaluation_automorphism (b : AdjoinRoot p) :
    charpolyRootEvaluation A (centralizerAlgebraAut σ γ b) =
      (charpolyRootEvaluation A b).map σ.toRingHom := by
  let e := charpolyRootEvaluation A
  have hr : e.toRingHom.comp (centralizerAlgebraAut σ γ).toRingHom =
      σ.toRingHom.mapMatrix.comp e.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro r
      change e (centralizerAlgebraAut σ γ (AdjoinRoot.of p r)) =
        (e (AdjoinRoot.of p r)).map σ.toRingHom
      have hOf : centralizerAlgebraAut σ γ (AdjoinRoot.of p r) = AdjoinRoot.of p (σ r) := by
        simp [centralizerAlgebraAut]
      rw [hOf, ← AdjoinRoot.algebraMap_eq, e.commutes, e.commutes, Matrix.algebraMap_eq_diagonal,
        Matrix.algebraMap_eq_diagonal, diagonal_map (map_zero σ.toRingHom)]
      rfl
    · change e (centralizerAlgebraAut σ γ (AdjoinRoot.root p)) = (e (AdjoinRoot.root p)).map σ.toRingHom
      simpa [centralizerAlgebraAut, e] using (baseChange_matrix_map_automorphism σ γ).symm
  exact DFunLike.congr_fun hr b

private theorem charpolyRootEvaluation_norm_product (b : (AdjoinRoot p)ˣ) (l : ℕ) :
    charpolyRootEvaluation A (((List.range l).map fun i => (centralizerAlgebraAut σ γ ^ i) b.val).prod) =
      (cyclicNorm σ l (Units.map (charpolyRootEvaluation A).toMonoidHom b)).val := by
  let e := charpolyRootEvaluation A
  let a := centralizerAlgebraAut σ γ
  have hcomm (i : ℕ) (c : AdjoinRoot p) : e ((a ^ i) c) = (e c).map (σ ^ i).toRingHom := by
    induction i generalizing c with
    | zero => simp only [pow_zero]; ext j k; rfl
    | succ i ih =>
      rw [pow_succ a, pow_succ σ, AlgEquiv.mul_apply, ih,
        show e (a c) = (e c).map σ.toRingHom from charpolyRootEvaluation_automorphism σ γ c]
      ext j k
      rfl
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, map_mul, ih, cyclicNorm_succ, Units.val_mul]
    exact congrArg (fun x => (cyclicNorm σ l (Units.map e.toMonoidHom b)).val * x) (hcomm l b.val)

theorem isNorm_iff_centralizerAlgebra_product (hσ : IsCyclicAlgebra σ l)
    (hγ : IsRegularSemisimple γ) :
    IsNorm σ l γ ↔ ∃ b : (AdjoinRoot p)ˣ,
      ((List.range l).map fun i => (centralizerAlgebraAut σ γ ^ i) b.val).prod = AdjoinRoot.root p := by
  let : Module.Finite F E := hσ.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1.symm ▸ hσ.pos)
  let f := algebraMap F E
  obtain ⟨v, hv⟩ := regularCyclicBasis F n γ.val hγ
  have hV : IsUnit (cyclicBasisMatrix A (f ∘ v)) := by
    change IsUnit (cyclicBasisMatrix (γ.val.map f) (f ∘ v))
    rw [← cyclicBasisMatrix_map]
    exact hv.map f.mapMatrix
  let e := charpolyRootEvaluation A
  have hinj := charpolyRootEvaluation_injective A (f ∘ v) hV
  constructor
  · rintro ⟨δ, x, hx⟩
    let d := x⁻¹ * δ * entrywiseAut σ n x
    have hn : cyclicNorm σ l d = baseChange F E n γ := by
      dsimp only [d]
      rw [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply, hx]
    have hcomm : Commute d (baseChange F E n γ) := by
      have h := entrywiseAut_cyclicNorm σ l d
      rw [hn, entrywiseAut_baseChange, hσ.pow_eq_one, entrywiseAut_one_apply] at h
      change d * baseChange F E n γ = baseChange F E n γ * d
      conv_lhs => rw [h]
      group
    obtain ⟨b, hb⟩ := charpolyRootEvaluation_unit (baseChange F E n γ) d (f ∘ v) hV hcomm
    refine ⟨b, hinj ?_⟩
    rw [charpolyRootEvaluation_norm_product, hb, hn, charpolyRootEvaluation_root]
  · rintro ⟨b, hb⟩
    let δ := Units.map e.toMonoidHom b
    refine ⟨δ, 1, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    apply Units.ext
    rw [← charpolyRootEvaluation_norm_product σ γ b, hb, charpolyRootEvaluation_root]

end Cyclic

/-- The norm condition at a regular base matrix is equivalent to a cyclic
product condition on the units of its scalar-extended characteristic algebra. -/
def RegularNormCentralizerAlgebraStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [CommRing E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ (γ : GeneralLinear n F), IsRegularSemisimple γ →
      let p := (baseChange F E n γ).val.charpoly
      IsNorm σ l γ ↔ ∃ b : (AdjoinRoot p)ˣ,
        ((List.range l).map fun i => (centralizerAlgebraAut σ γ ^ i) b.val).prod = AdjoinRoot.root p

theorem regularNormCentralizerAlgebra : RegularNormCentralizerAlgebraStatement.{u, v} := by
  intro F _ E _ _ σ l n hσ γ hγ
  exact isNorm_iff_centralizerAlgebra_product σ γ hσ hγ

end Langlands.BaseChange
