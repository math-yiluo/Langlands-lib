import Langlands.Representation.Classification.BernsteinUnitaryStatement
import Langlands.Representation.Induction.CompactSesquilinear
import Langlands.Representation.Induction.CompactScalarProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Unitary.InvariantSesquilinearScalarProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Group.GL.CompactOpen

/-! # Unitarity of Hermitian factors of an irreducible unitary product -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped NNReal ComplexConjugate

namespace Langlands.Classification

universe uF uV

private theorem normalized_form_covariant
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hinv : ∀ g x y, b (ρ g x) (ρ g y) = b x y)
    (q : B.parabolic F.Carrier) (v w : V) :
    b (twist (T.parabolicHalfModulus B) (ρ.comp (B.leviProjection F.Carrier)) q v)
        (twist (T.parabolicHalfModulus B) (ρ.comp (B.leviProjection F.Carrier)) q w) =
      (((T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) * b v w := by
  change b
    ((((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ)) •
      ρ (B.leviProjection F.Carrier q) v)
    ((((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ)) •
      ρ (B.leviProjection F.Carrier q) w) = _
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply,
    smul_eq_mul, Complex.conj_ofReal, hinv]
  rw [← mul_assoc]
  congr 1
  norm_cast
  exact NNReal.mul_self_sqrt _

/-- The weak finite-family form of Tadic's Theorem 2.5(ii), with independent
field and coefficient-space universes. -/
theorem bernsteinUnitaryProductFactorUnitarity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    BernsteinUnitaryProductFactorUnitarity.{uF, uV} F T := by
  classical
  let := T.topology
  intro n B σ hσ hi hu
  by_cases hn : 0 < n
  swap
  · intro i
    have hlen := B.length_le
    have hilt := i.isLt
    omega
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.leviTopology B
  let ρ := B.blockTensor (fun i => (σ i).representation)
  let P := B.parabolic F.Carrier
  let τ := twist (T.parabolicHalfModulus B) (ρ.comp (B.leviProjection F.Carrier))
  let δ : P → ℝ≥0 := fun q => T.leviModulus B (B.leviProjection F.Carrier q)
  change Representation.IsIrreducible (Induction.smoothInduced P τ) at hi
  change IsUnitarizable (Induction.smoothInduced P τ) at hu
  have hτ : IsSmooth τ :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous
        (FiniteTensor.isSmooth_external _ (fun i => (σ i).property)))
  have hforms (i : Fin B.length) :
      ∃ H : σ i →ₗ⋆[ℂ] σ i →ₗ[ℂ] ℂ, H ≠ 0 ∧
        (∀ x y, H y x = conj (H x y)) ∧
        ∀ g x y, H ((σ i).representation g x) ((σ i).representation g y) = H x y := by
    obtain ⟨b, hb, hinv⟩ := (hσ i).2
    exact InvariantSesquilinear.exists_nonzero_hermitian (σ i).representation b hb hinv
  choose H hH0 hHherm hHinv using hforms
  let b := InvariantSesquilinear.tensor H
  have hb0 : b ≠ 0 := InvariantSesquilinear.tensor_ne_zero H hH0
  have hbherm (v w) : b w v = conj (b v w) :=
    InvariantSesquilinear.tensor_hermitian H hHherm v w
  have hbinv (g) (v w) : b (ρ g v) (ρ g w) = b v w :=
    InvariantSesquilinear.tensor_invariant _ H hHinv g v w
  have hbcov (q : P) (v w) : b (τ q v) (τ q w) = ((δ q : ℝ) : ℂ) * b v w :=
    normalized_form_covariant T B ρ b hbinv q v w
  obtain ⟨K, _hK, _hPK, hμ⟩ := glParabolicCompactScalarIntegral p F T n hn B
  let : MeasurableSpace K := borel K
  obtain ⟨μ, hHaar, _hprob, hscalar⟩ := hμ
  let := hHaar
  have hint (f h : Induction.SmoothFunctions P τ) :
      Integrable (fun k : K => b (Induction.eval P τ f k) (Induction.eval P τ h k)) μ := by
    simpa only [mul_one] using
      (hscalar (fun x => b (Induction.eval P τ f x) (Induction.eval P τ h x))
        (Induction.sesquilinearPairing_isLocallyConstant P τ b f h)
        (Induction.sesquilinearPairing_covariant P τ b δ hbcov f h) 1).1
  let Bint := Induction.integralSesquilinear P τ b K.toSubgroup μ hint
  have hB0 : Bint ≠ 0 :=
    Induction.integralSesquilinear_ne_zero P τ b hb0 hτ δ hbcov K.toSubgroup μ hint
  have hBherm (f h) : Bint h f = conj (Bint f h) :=
    Induction.integralSesquilinear_hermitian P τ b hbherm K.toSubgroup μ hint f h
  have hBinv (g) (f h) :
      Bint (Induction.smoothInduced P τ g f) (Induction.smoothInduced P τ g h) = Bint f h := by
    exact (hscalar (fun x => b (Induction.eval P τ f x) (Induction.eval P τ h x))
      (Induction.sesquilinearPairing_isLocallyConstant P τ b f h)
      (Induction.sesquilinearPairing_covariant P τ b δ hbcov f h) g).2
  obtain ⟨a⟩ := hu
  have ha : IsAdmissible (Induction.smoothInduced P τ) :=
    (CuspidalSupport.cuspidalEmbedding F T n
      (SmoothRep.of _ (Induction.smoothInduced_smooth P τ)) hi).1
  have hcof (U : OpenSubgroup (GeneralLinear n F.Carrier)) :
      ∃ L : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (L : Set (GeneralLinear n F.Carrier)) ∧ L ≤ U := by
    obtain ⟨L, hL, hLU⟩ := T.generalLinearCompactOpen n U U.mem_nhds_one
    exact ⟨L, hL, hLU⟩
  obtain ⟨c, hc, hcomp⟩ := invariantSesquilinearScalar
    (GeneralLinear n F.Carrier) hcof _ (Induction.smoothInduced P τ) ha hi a Bint hB0 hBinv
  obtain ⟨f, hf⟩ := InvariantSesquilinear.exists_diagonal_ne_zero Bint hB0
  have haf : a.inner f f ≠ 0 := by
    intro hzero
    exact hf (by rw [hcomp, hzero, mul_zero])
  have hcreal : conj c = c := by
    apply mul_right_cancel₀ haf
    calc
      conj c * a.inner f f = conj (c * a.inner f f) := by
        rw [map_mul, a.conj_inner_symm]
      _ = c * a.inner f f := by rw [← hcomp, ← hBherm]
  let b' := c⁻¹ • b
  have hb'herm (v w) : b' w v = conj (b' v w) := by
    change c⁻¹ * b w v = conj (c⁻¹ * b v w)
    rw [hbherm, map_mul, map_inv₀, hcreal]
  have hb'cov (q : P) (v w) :
      b' (τ q v) (τ q w) = ((δ q : ℝ) : ℂ) * b' v w := by
    change c⁻¹ * b (τ q v) (τ q w) = ((δ q : ℝ) : ℂ) * (c⁻¹ * b v w)
    rw [hbcov]
    ring
  have hint' (f h : Induction.SmoothFunctions P τ) :
      Integrable (fun k : K => b' (Induction.eval P τ f k) (Induction.eval P τ h k)) μ :=
    (hint f h).const_mul c⁻¹
  have heq (f h : Induction.SmoothFunctions P τ) :
      Induction.integralSesquilinear P τ b' K.toSubgroup μ hint' f h = a.inner f h := by
    change (∫ k : K, c⁻¹ * b (Induction.eval P τ f k) (Induction.eval P τ h k) ∂μ) = _
    rw [integral_const_mul]
    change c⁻¹ * Bint f h = _
    rw [hcomp, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hρu : IsUnitarizable ρ := by
    refine ⟨{
      toInnerProductCore := Induction.positiveCore_of_integral P τ b'
        hb'herm hτ δ hb'cov K.toSubgroup μ hint' a heq
      invariant := ?_ }⟩
    intro g v w
    change c⁻¹ * b (ρ g v) (ρ g w) = c⁻¹ * b v w
    rw [hbinv]
  exact InvariantSesquilinear.factors_unitarizable_of_external
    (fun i => (σ i).representation) H hH0 (fun i => (hσ i).1) hρu

end Langlands.Classification
