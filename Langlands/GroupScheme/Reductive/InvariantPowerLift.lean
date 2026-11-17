import Langlands.GroupScheme.Reductive.GeometricReductivityShift
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.HomogeneousQuotientInvariantSections

/-! # Finite coordinate power lifting from geometric reductivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Geometric reductivity separates a fixed functional by a normalized homogeneous
polynomial invariant under transpose substitution on every scheme test. -/
theorem exists_normalized_transpose_invariant
    (hH : IsGeometricallyReductive H) (ρ : MatrixRepresentation H n)
    (c : n → k) (hc : c ≠ 0) (hfix : ρ.dual.IsFixedVector c) :
    ∃ (d : ℕ) (F : MvPolynomial n k), 0 < d ∧ F.IsHomogeneous d ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
        (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ *ᵥ x) F =
          MvPolynomial.eval₂ (scalarMap T) x F) ∧
      MvPolynomial.eval c F = 1 := by
  obtain ⟨d, P, hd, hP, hinv, hPc⟩ := hH n ρ.dual c hc hfix
  refine ⟨d, MvPolynomial.C (MvPolynomial.eval c P)⁻¹ * P, hd, ?_, ?_, ?_⟩
  · simpa only [zero_add] using (MvPolynomial.isHomogeneous_C _ _).mul hP
  · intro T h x
    have hh := hinv T h⁻¹ x
    rw [dual_pointMatrix, GeneralLinear.matrixContragredient_coe, map_inv, inv_inv] at hh
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hh]
  · simp only [map_mul, MvPolynomial.eval_C, inv_mul_cancel₀ hPc]

end MatrixRepresentation

namespace InvariantPowerLift

variable {k : Type u} [Field k] {n : Type}

/-- A homogeneous polynomial normalized at `c` evaluates to the corresponding
power on every scalar multiple of `c`, over an arbitrary algebra. -/
theorem aeval_scaled_eq_pow {A : Type*} [CommRing A] [Algebra k A]
    {F : MvPolynomial n k} {d : ℕ} (hF : F.IsHomogeneous d)
    (c : n → k) (hc : MvPolynomial.eval c F = 1) (b : A) :
    MvPolynomial.aeval (fun j => algebraMap k A (c j) * b) F = b ^ d := by
  have he : MvPolynomial.aeval (fun j => algebraMap k A (c j)) F =
      algebraMap k A (MvPolynomial.eval c F) := by
    change MvPolynomial.eval₂ (algebraMap k A)
      ((algebraMap k A) ∘ c) F = _
    exact (by simpa only [RingHom.comp_id, MvPolynomial.eval₂_id] using
      (MvPolynomial.eval₂_comp_left (algebraMap k A) (RingHom.id k) c F).symm)
  have hx : (fun j => algebraMap k A (c j) * b) =
      b • (fun j => algebraMap k A (c j)) := by
    funext j
    exact mul_comm _ _
  rw [hx, HomogeneousShift.aeval_smul_of_isHomogeneous hF, he, hc, map_one, mul_one]

/-- Evaluating a normalized homogeneous separator in a finite lift family lifts
the power of its common image. -/
theorem map_aeval_eq_pow {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) (f : n → A)
    {F : MvPolynomial n k} {d : ℕ} (hF : F.IsHomogeneous d)
    (c : n → k) (hc : MvPolynomial.eval c F = 1) (b : B)
    (hf : ∀ j, φ (f j) = algebraMap k B (c j) * b) :
    φ (MvPolynomial.aeval f F) = b ^ d := by
  rw [MvPolynomial.comp_aeval_apply]
  simpa only [Function.comp_def, hf] using aeval_scaled_eq_pow hF c hc b

/-- A positive-degree homogeneous polynomial in elements of an ideal belongs
to that ideal, over an arbitrary algebra. -/
theorem aeval_mem_ideal {A : Type*} [CommRing A] [Algebra k A]
    (I : Ideal A) (f : n → A) (hf : ∀ j, f j ∈ I)
    {F : MvPolynomial n k} {d : ℕ} (hd : 0 < d) (hF : F.IsHomogeneous d) :
    MvPolynomial.aeval f F ∈ I := by
  have hzero : MvPolynomial.aeval (0 : n → A ⧸ I) F = 0 := by
    have hscale := HomogeneousShift.aeval_smul_of_isHomogeneous hF
      (0 : A ⧸ I) (0 : n → A ⧸ I)
    simpa only [zero_smul, zero_pow hd.ne', zero_mul] using hscale
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mkₐ k I) (MvPolynomial.aeval f F) = 0
  rw [MvPolynomial.comp_aeval_apply]
  have hx : (fun j => (Ideal.Quotient.mkₐ k I) (f j)) = 0 := by
    funext j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf j)
  exact hx ▸ hzero

variable {J H : GroupScheme (Spec (CommRingCat.of k))}
  (i : H ⟶ J) {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation H n) (f : n → Γ(J.X.left, ⊤))

/-- A finite family of ambient functions has the transpose transformation law
of a basis of a right regular subrepresentation, on every scheme test. -/
def IsRightCovariantFamily : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ J.X) (h : T ⟶ H.X),
    (fun j => (g * (h ≫ i.hom.hom)).left.appTop (f j)) =
      (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ *ᵥ
        (fun j => g.left.appTop (f j))

/-- A finite covariant family turns a transpose-invariant polynomial into an
actual right-invariant section on every relative test scheme. -/
theorem isRightInvariant_eval₂
    (hf : IsRightCovariantFamily i ρ f)
    (F : MvPolynomial n k)
    (hF : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (x : n → Γ(T.left, ⊤)),
      MvPolynomial.eval₂ (scalarMap T)
          ((ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))ᵀ *ᵥ x) F =
        MvPolynomial.eval₂ (scalarMap T) x F) :
    HomogeneousQuotientFromEmbedding.IsRightInvariant i
      (MvPolynomial.eval₂ (scalarMap J.X) f F) := by
  intro T g h
  have hn (a : T ⟶ J.X) :
      a.left.appTop (MvPolynomial.eval₂ (scalarMap J.X) f F) =
        MvPolynomial.eval₂ (scalarMap T) (fun j => a.left.appTop (f j)) F := by
    rw [MvPolynomial.eval₂_comp_left a.left.appTop.hom]
    have hc : a.left.appTop.hom.comp (scalarMap J.X) = scalarMap T := by
      ext t
      exact scalarMap_naturality a t
    rw [hc]
    rfl
  rw [hn, hn, hf T g h]
  exact hF T h _

end InvariantPowerLift

end Langlands.GroupScheme
