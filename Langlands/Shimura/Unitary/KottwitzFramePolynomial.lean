import Langlands.Shimura.Unitary.KottwitzPolynomial

/-!
# Kottwitz's polynomial in the ordinary Hecke convention

The inverse-opposite identification of the right frame group with the ordinary
similitude group negates the cocharacter. The dual of the pinned Kottwitz
representation has that extreme weight. Retaining the geometric Frobenius
normalization gives the polynomial for an ordinary spherical component.
-/

noncomputable section

open NumberField

namespace Langlands.Shimura.KottwitzDual

universe u v w uL uV uΩ

section Frobenius

variable {S : Type u} [Fintype S] {n : ℕ} {L : Type v} [Field L]

/-- The simultaneous representative of the long Weyl element is fixed by the
pinned action, including permutations that exchange the two CM embeddings. -/
theorem dualAction_signedAntidiagonal (G : CMPerm S) :
    dualAction S n L G (1, fun _ => signedAntidiagonalUnit n L) =
      (1, fun _ => signedAntidiagonalUnit n L) := by
  have hdet : Matrix.GeneralLinearGroup.det (signedAntidiagonalUnit n L) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_signedAntidiagonal L n
  have htwist : twist n L (signedAntidiagonalUnit n L) = signedAntidiagonalUnit n L := by
    rw [twist_apply, transposeInv_signedAntidiagonalUnit, mul_inv_cancel_right]
  rw [dualAction_apply]
  ext1
  · simp [dualEndo_fst, hdet]
  · funext τ
    obtain ⟨τ', rfl⟩ := (CMPerm.base G).surjective τ
    rw [dualEndo_snd_base]
    split_ifs <;> simp [htwist]

variable (h : S × Bool → ℕ) (hsum : ∀ τ, h (τ, true) + h (τ, false) = n)
  (G : CMPerm S) (f : ℕ)
  (hGf : ∀ x, h (((G ^ f : CMPerm S) : Equiv.Perm (S × Bool)) x) = h x)

/-- On the existing Kottwitz space, take the inverse of the normalized
Frobenius and multiply by `s^(2*f*d)`. Its transpose acts on the dual space
with the original weight normalization `s^(f*d)`. -/
def kottwitzFrameFrobenius (s : Lˣ) (x : DualGroup S n L) :
    KottwitzSpace S n L (hodgeDegrees h) ≃ₗ[L] KottwitzSpace S n L (hodgeDegrees h) :=
  (LinearEquiv.smulOfUnit ((s ^ (f * hodgeDim h)) ^ 2)).trans
    (kottwitzV h hsum G f hGf s x (Multiplicative.ofAdd 1)).symm

theorem kottwitzFrameFrobenius_eq (s : Lˣ) (x : DualGroup S n L) :
    (kottwitzFrameFrobenius h hsum G f hGf s x).toLinearMap =
      ((s : L) ^ (f * hodgeDim h)) •
        (kottwitzRep h hsum (G ^ f) hGf (frobeniusElement G f x)).symm.toLinearMap := by
  let e := kottwitzV h hsum G f hGf s x (Multiplicative.ofAdd 1)
  let R := kottwitzRep h hsum (G ^ f) hGf (frobeniusElement G f x)
  let a := s ^ (f * hodgeDim h)
  have he : e.toLinearMap = (a : L) • R.toLinearMap := by
    simpa only [e, R, a, kottwitzFrobenius, Units.val_pow_eq_pow_val] using
      kottwitzFrobenius_eq h hsum G f hGf s x
  refine LinearMap.ext fun y => e.injective ?_
  change e (e.symm ((a ^ 2) • y)) = e ((a : L) • R.symm y)
  rw [e.apply_symm_apply, map_smul]
  change (a ^ 2) • y = (a : L) • e.toLinearMap (R.symm y)
  rw [he, LinearMap.smul_apply, LinearEquiv.coe_coe, R.apply_symm_apply,
    Units.smul_def, Units.val_pow_eq_pow_val, smul_smul, pow_two]

open scoped Classical in
/-- The characteristic polynomial of the transported geometric Frobenius.
The matrix of the action on the dual is the transpose of the matrix used here. -/
def kottwitzFrameCharpoly (s : Lˣ) (x : DualGroup S n L) : Polynomial L :=
  (LinearMap.toMatrix (kottwitzBasis n L (hodgeDegrees h)) (kottwitzBasis n L (hodgeDegrees h))
    (kottwitzFrameFrobenius h hsum G f hGf s x).toLinearMap).charpoly

theorem kottwitzFrameCharpoly_monic (s : Lˣ) (x : DualGroup S n L) :
    (kottwitzFrameCharpoly h hsum G f hGf s x).Monic := by
  classical
  exact Matrix.charpoly_monic _

theorem kottwitzFrameCharpoly_natDegree (s : Lˣ) (x : DualGroup S n L) :
    (kottwitzFrameCharpoly h hsum G f hGf s x).natDegree = kottwitzDim n (hodgeDegrees h) := by
  classical
  rw [kottwitzFrameCharpoly, Matrix.charpoly_natDegree_eq_dim]
  exact card_kottwitzBasisIndex (hodgeDegrees h)

theorem kottwitzFrameCharpoly_eval_zero_ne_zero (s : Lˣ) (x : DualGroup S n L) :
    (kottwitzFrameCharpoly h hsum G f hGf s x).eval 0 ≠ 0 := by
  classical
  let B := kottwitzBasis n L (hodgeDegrees h)
  let e := kottwitzFrameFrobenius h hsum G f hGf s x
  have he : IsUnit (e.toLinearMap : Module.End L _) :=
    ⟨LinearEquiv.automorphismGroup.toLinearMapMonoidHom.toHomUnits e, rfl⟩
  have hM : IsUnit (LinearMap.toMatrix B B e.toLinearMap) := he.map (LinearMap.toMatrixAlgEquiv B)
  change (LinearMap.toMatrix B B e.toLinearMap).charpoly.eval 0 ≠ 0
  rw [Matrix.eval_charpoly, map_zero, zero_sub, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (hM.map Matrix.detMonoidHom).ne_zero

theorem kottwitzFrameCharpoly_neg (s : Lˣ) (x : DualGroup S n L) :
    kottwitzFrameCharpoly h hsum G f hGf (-s) (x * epsilonElement S n L) =
      kottwitzFrameCharpoly h hsum G f hGf s x := by
  unfold kottwitzFrameCharpoly kottwitzFrameFrobenius
  have hs : ((-s) ^ (f * hodgeDim h)) ^ 2 = (s ^ (f * hodgeDim h)) ^ 2 := by
    simp only [pow_two, ← mul_pow, neg_mul_neg]
  rw [kottwitzV_neg, hs]

end Frobenius

section Parameters

open KottwitzUnramified Langlands.Global.AdelicFunctoriality

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [Algebra.IsQuadraticExtension E K]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {σ : SecondKindInvolution E K A} {n : ℕ} {p : ℕ} [Fact p.Prime]
  (θ : ℂ →+* PadicAlgCl p) {Φ : (E →+* ℝ) → (K →+* ℂ)} (hΦ : IsCMSection E K Φ)
  (nfun : (K →+* ℂ) → ℕ) (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)

/-- The transported Frobenius polynomial of the normalized Satake lift `t`. -/
def kottwitzFramePolynomialOf {Ω : Type uΩ} [Field Ω]
    (s : Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)) : Polynomial Ω :=
  kottwitzFrameCharpoly (cmHodge hΦ nfun) (cmHodge_add hΦ nfun hconj) (frobeniusCMPerm hΦ θ)
    (localDegree p θ nfun) (cmHodge_frobenius_pow θ hΦ nfun) s (torusElement t)

variable [Module.Finite ℚ A] {L : Type uL} [Field L]
  (c : UnramifiedChart σ (rationalPrimePlace p) n)

/-- The right-frame Kottwitz polynomial expressed using the normalized Satake
parameter of the ordinary Hecke representation `π`. -/
def IsKottwitzFramePolynomialOver
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p)))
    (Ω : Type uΩ) [Field Ω] [Algebra L Ω] (s : SqrtPrime (rationalPrimePlace p) Ω)
    (P : Polynomial Ω) : Prop :=
  ∃ (ξ : c.torus →* Ωˣ) (t : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)),
    c.HasPrincipalSeriesParameter π ξ ∧ IsNormalizedLift c θ (Φ := Φ) s ξ t ∧
      P = kottwitzFramePolynomialOf θ hΦ nfun hconj s.1 t

/-- The transported polynomial has coefficients in `L` when its realization
over `AlgebraicClosure L` is the indicated image of `P`. -/
def IsKottwitzFramePolynomial
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p)))
    (s : SqrtPrime (rationalPrimePlace p) (AlgebraicClosure L)) (P : Polynomial L) : Prop :=
  IsKottwitzFramePolynomialOver θ hΦ nfun hconj c π (AlgebraicClosure L) s
    (P.map (algebraMap L (AlgebraicClosure L)))

variable {θ hΦ nfun hconj c}
  {π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p))}

/-- Transport preserves monicity and the degree of the Kottwitz polynomial. -/
theorem IsKottwitzFramePolynomial.monic_and_natDegree
    {s : SqrtPrime (rationalPrimePlace p) (AlgebraicClosure L)} {P : Polynomial L}
    (hP : IsKottwitzFramePolynomial θ hΦ nfun hconj c π s P) :
    P.Monic ∧ P.natDegree = kottwitzDim n (hodgeDegrees (cmHodge hΦ nfun)) := by
  obtain ⟨-, t, -, -, ht⟩ := hP
  constructor
  · apply (Polynomial.monic_map_iff (f := algebraMap L (AlgebraicClosure L))).mp
    rw [ht]
    exact kottwitzFrameCharpoly_monic _ _ _ _ _ _ _
  · rw [← Polynomial.natDegree_map (algebraMap L (AlgebraicClosure L)), ht]
    exact kottwitzFrameCharpoly_natDegree _ _ _ _ _ _ _

theorem IsKottwitzFramePolynomial.eval_zero_ne_zero
    {s : SqrtPrime (rationalPrimePlace p) (AlgebraicClosure L)} {P : Polynomial L}
    (hP : IsKottwitzFramePolynomial θ hΦ nfun hconj c π s P) : P.eval 0 ≠ 0 := by
  obtain ⟨-, t, -, -, ht⟩ := hP
  intro h
  apply kottwitzFrameCharpoly_eval_zero_ne_zero _ _ _ _ _ s.1 (torusElement t)
  change (kottwitzFramePolynomialOf θ hΦ nfun hconj s.1 t).eval 0 = 0
  rw [← ht, Polynomial.eval_zero_map, h, map_zero]

theorem IsKottwitzFramePolynomialOver.neg
    {Ω : Type uΩ} [Field Ω] [Algebra L Ω] {s : SqrtPrime (rationalPrimePlace p) Ω}
    {P : Polynomial Ω} (hP : IsKottwitzFramePolynomialOver θ hΦ nfun hconj c π Ω s P) :
    IsKottwitzFramePolynomialOver θ hΦ nfun hconj c π Ω s.neg P := by
  obtain ⟨ξ, t, hξ, ht, rfl⟩ := hP
  refine ⟨ξ, t * epsilonHat (E →+* ℝ) n Ω, hξ, ht.neg, ?_⟩
  unfold kottwitzFramePolynomialOf
  rw [torusElement_mul]
  exact (kottwitzFrameCharpoly_neg _ _ _ _ _ s.1 (torusElement t)).symm

end Parameters

end Langlands.Shimura.KottwitzDual
