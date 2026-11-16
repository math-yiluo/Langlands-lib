import Langlands.Representation.Archimedean.ComplexOperatorSymbols
import Langlands.Representation.Archimedean.ComplexNoncompactFiltration

/-!
# The holomorphic operators of the noncompact picture, formally

Over the polynomial ring `Hol n` in the coordinates `v` of the lower unipotent group,
`nbH = 1 + lowMat v`, `conjH X = nbH X nbH⁻¹`, the vector field `fieldWH X` and the torus term
`lamH α X = Σ_k α_k (conjH X)_{kk}` evaluate to the functions `nbMat`, `conjMat`, `fieldW` of
`ComplexNoncompactPicture` / `ComplexNoncompactFiltration` (`eval_fieldWH`, `eval_conjH`).
Mapped into `Pol n`, they give the first-order operator `opDataH α X` whose symbol is
`tr(X Φ)` (`sym_opDataH`); for an elementary matrix `E_{kj}` it is `Φ_{jk}`
(`sym_opDataH_single`), so the symbols `symb` of `ComplexMomentSymbols` are symbols of
operators `opDataH α (symbMat i)` (`sym_opDataH_symbMat`).
-/

noncomputable section

open scoped Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.MomentSymbols

open MvPolynomial Langlands.Archimedean.NoncompactPicture

variable {n : ℕ}

/-- Polynomials in the coordinates `v`. -/
abbrev Hol (n : ℕ) := MvPolynomial (Lw n) ℂ

/-- The generic lower unipotent matrix over `Hol n`. -/
def nbH : Matrix (Fin n) (Fin n) (Hol n) := 1 + lowMatG X

/-- Its inverse (the adjugate, since the determinant is `1`). -/
def nbInvH : Matrix (Fin n) (Fin n) (Hol n) := (nbH (n := n)).adjugate

/-- `nb X nb⁻¹`. -/
def conjH (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (Hol n) :=
  nbH * X.map C * nbInvH

/-- The vector field of the noncompact formula. -/
def fieldWH (X : Matrix (Fin n) (Fin n) ℂ) (p : Lw n) : Hol n :=
  ((lowMatG (fun q => conjH X q.1.1 q.1.2) * nbH : Matrix (Fin n) (Fin n) (Hol n))) p.1.1 p.1.2

/-- The holomorphic torus term. -/
def lamH (α : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : Hol n := ∑ k, C (α k) * conjH X k k

theorem lowMatG_map {S T : Type*} [Zero S] [Zero T] (w : Lw n → S) (f : S → T) (hf : f 0 = 0) :
    (lowMatG w).map f = lowMatG (f ∘ w) := by
  ext a b
  simp only [Matrix.map_apply, lowMatG, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> simp [hf]

/-! ## Evaluation -/

theorem nbH_map_eval (v : Lw n → ℂ) : (nbH (n := n)).map (eval v) = nbMat v := by
  ext a b
  simp only [Matrix.map_apply, nbH, nbMat, lowMat, lowMatG, Matrix.add_apply, Matrix.of_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem nbInvH_map_eval (v : Lw n → ℂ) : (nbInvH (n := n)).map (eval v) = (nbMat v)⁻¹ := by
  rw [nbInvH, ← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply,
    nbH_map_eval, nbMat_inv]

theorem conjH_map_eval (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) :
    (conjH X).map (eval v) = conjMat X v := by
  rw [conjH, conjMat, Matrix.map_mul, Matrix.map_mul, nbH_map_eval, nbInvH_map_eval,
    Matrix.map_map]
  congr 2
  ext a b
  simp

theorem eval_conjH (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) (a b : Fin n) :
    eval v (conjH X a b) = conjMat X v a b := by
  rw [← conjH_map_eval X v]; rfl

theorem eval_fieldWH (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) (p : Lw n) :
    eval v (fieldWH X p) = fieldW X v p := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M p.1.1 p.1.2)
    (Matrix.map_mul (L := lowMatG fun q => conjH X q.1.1 q.1.2) (M := nbH) (f := eval v))
  simp only [Matrix.map_apply] at h
  rw [fieldWH, h, lowMatG_map _ _ (map_zero _), nbH_map_eval]
  have hl : lowMatG ((eval v) ∘ fun q : Lw n => conjH X q.1.1 q.1.2) =
      lowMat (lowCoords (conjMat X v)) := by
    ext a b
    simp only [lowMatG, lowMat, Matrix.of_apply, Function.comp_apply, lowCoords, eval_conjH]
  rw [hl]
  rfl

theorem eval_lamH (α : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) :
    eval v (lamH α X) = ∑ k, α k * conjMat X v k k := by
  simp [lamH, eval_conjH]

/-! ## In `Pol n` -/

/-- The inclusion of the polynomials in `v`. -/
abbrev ιP : Hol n →ₐ[ℂ] Pol n := rename vV

theorem nbH_map_ιP : (nbH (n := n)).map ιP = nbF := by
  ext a b
  simp only [Matrix.map_apply, nbH, nbF, lowMatG, Matrix.add_apply, Matrix.of_apply,
    Matrix.one_apply]
  split_ifs <;> simp [ιP, vV]

theorem nbInvH_map_ιP : (nbInvH (n := n)).map ιP = nbInvF := by
  rw [nbInvH, ← AlgHom.mapMatrix_apply, AlgHom.map_adjugate, AlgHom.mapMatrix_apply, nbH_map_ιP,
    nbInvF]

theorem conjH_map_ιP (X : Matrix (Fin n) (Fin n) ℂ) :
    (conjH X).map ιP = nbF * X.map C * nbInvF := by
  rw [conjH, Matrix.map_mul, Matrix.map_mul, nbH_map_ιP, nbInvH_map_ιP, Matrix.map_map]
  congr 2
  ext a b
  simp [ιP]

/-- The first-order operator of `X` on `Pol n`. -/
def opDataH (α : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : OpData n :=
  ⟨fun p => ιP (fieldWH X p), ιP (lamH α X)⟩

theorem sum_lw {M : Type*} [AddCommMonoid M] (f : Lw n → M) :
    ∑ p, f p = ∑ i : Fin n, ∑ j : Fin n, if h : j < i then f ⟨(i, j), h⟩ else 0 := by
  classical
  rw [← Fintype.sum_prod_type', ← Fintype.sum_subtype_add_sum_subtype (fun x : Fin n × Fin n =>
    x.2 < x.1)]
  rw [Finset.sum_eq_zero (fun (y : {x : Fin n × Fin n // ¬ x.2 < x.1}) _ => dite_eq_right y.2),
    add_zero]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [dite_eq_left p.2]

theorem trace_mul_lowMatG_transpose (M : Matrix (Fin n) (Fin n) (Pol n)) (w : Lw n → Pol n) :
    (M * (lowMatG w)ᵀ).trace = ∑ p, M p.1.1 p.1.2 * w p := by
  rw [sum_lw, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply, lowMatG, Matrix.of_apply]
  split_ifs <;> simp

theorem trace_lowMatG_mul (Y B : Matrix (Fin n) (Fin n) (Pol n)) :
    (lowMatG (fun q => Y q.1.1 q.1.2) * B).trace = (Y * upPart B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, lowMatG, upPart, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j < i
  · rw [dite_eq_left h, ite_eq_left h]
  · rw [dite_eq_right h, ite_eq_right h, zero_mul, mul_zero]

/-- **The symbol is `tr(X Φ)`.** -/
theorem sym_opDataH (α : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    sym (opDataH α X) = (X.map C * PhiF).trace := by
  have hW : ∀ p, ιP (fieldWH X p) =
      ((lowMatG (fun q => (nbF * X.map C * nbInvF : Matrix (Fin n) (Fin n) (Pol n)) q.1.1 q.1.2) *
        nbF : Matrix (Fin n) (Fin n) (Pol n))) p.1.1 p.1.2 := by
    intro p
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) (Pol n) => M p.1.1 p.1.2)
      (Matrix.map_mul (L := lowMatG fun q => conjH X q.1.1 q.1.2) (M := nbH)
        (f := (ιP : Hol n →ₐ[ℂ] Pol n)))
    simp only [Matrix.map_apply] at h
    rw [fieldWH, h, lowMatG_map _ _ (map_zero _), nbH_map_ιP]
    have hl : lowMatG ((ιP : Hol n →ₐ[ℂ] Pol n) ∘ fun q : Lw n => conjH X q.1.1 q.1.2) =
        lowMatG (fun q : Lw n =>
          (nbF * X.map C * nbInvF : Matrix (Fin n) (Fin n) (Pol n)) q.1.1 q.1.2) := by
      congr 1
      funext q
      simp only [Function.comp_apply, ← conjH_map_ιP]
      rfl
    rw [hl]
  simp only [sym, opDataH, hW]
  rw [← trace_mul_lowMatG_transpose, Matrix.mul_assoc, trace_lowMatG_mul, ← xiMat, ← UF,
    Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc UF nbF,
    Matrix.trace_mul_comm, PhiF]
  simp only [Matrix.mul_assoc]

theorem sym_opDataH_single (α : Fin n → ℂ) (k j : Fin n) :
    sym (opDataH α (Matrix.single k j 1)) = PhiF j k := by
  rw [sym_opDataH]
  have : (Matrix.single k j (1 : ℂ)).map C = Matrix.single k j (1 : Pol n) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [this, Matrix.trace_single_mul, one_smul]

/-- The elementary matrices giving the symbols `symb`. -/
def symbMat : Lw n ⊕ Lw n → Matrix (Fin n) (Fin n) ℂ
  | Sum.inr p => Matrix.single p.1.1 p.1.2 1
  | Sum.inl p => Matrix.single (succCol p) p.1.1 1

theorem sym_opDataH_symbMat (α : Fin n → ℂ) (i : Lw n ⊕ Lw n) :
    sym (opDataH α (symbMat i)) = symb i := by
  rcases i with p | p
  · exact sym_opDataH_single α _ _
  · exact sym_opDataH_single α _ _

end Langlands.Archimedean.MomentSymbols
