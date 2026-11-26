import Langlands.Shimura.Unitary.HermitianCoordinates
import Langlands.Shimura.Unitary.HermitianCongruence
import Langlands.Shimura.Unitary.RealSignatureNeighborhood
import Langlands.Global.RealCompletionWeakApproximation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Prescribing all real signatures by a symmetric unit -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra
open Langlands.Global (realCompletionVectorWeakApproximation)
open scoped TensorProduct Matrix.Norms.Operator

private theorem denseRange_realEmbeddingVectors (E : Type u) [Field E] [NumberField E]
    (d : ℕ) : DenseRange (fun x : Fin d → E => fun τ : E →+* ℝ => fun j => τ (x j)) := by
  let I := {p : InfinitePlace E // p.IsReal}
  let f : I → (E →+* ℝ) := fun p => InfinitePlace.embedding_of_isReal p.property
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => Subtype.ext (InfinitePlace.embedding_injective E ?_), fun τ => ?_⟩
    · apply RingHom.ext
      intro x
      have h := congrArg (fun τ : E →+* ℝ => (τ x : ℂ)) h
      simpa only [f, InfinitePlace.embedding_of_isReal_apply] using h
    · let c := Complex.ofRealHom.comp τ
      have hc : ComplexEmbedding.IsReal c := ComplexEmbedding.isReal_iff.mpr (by
        ext x
        simp [c, ComplexEmbedding.conjugate_coe_eq])
      let p : I := ⟨InfinitePlace.mk c, InfinitePlace.isReal_mk_iff.mpr hc⟩
      refine ⟨p, RingHom.ext fun x => Complex.ofReal_injective ?_⟩
      change ((InfinitePlace.embedding_of_isReal p.property) x : ℂ) = (τ x : ℂ)
      rw [InfinitePlace.embedding_of_isReal_apply]
      exact congrArg (fun g : E →+* ℂ => g x) (InfinitePlace.embedding_mk_eq_of_isReal hc)
  let i := Equiv.ofBijective f hf
  let g (x : ∀ p : I, Fin d → p.val.Completion) (τ : E →+* ℝ) (j : Fin d) :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (i.symm τ).property (x (i.symm τ) j)
  have hg : Function.Surjective g := by
    intro y
    choose a ha using fun p : I => fun j : Fin d =>
      InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal p.property (y (i p) j)
    refine ⟨a, funext fun τ => funext fun j => ?_⟩
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal (i.symm τ).property
      (a (i.symm τ) j) = y τ j
    rw [ha, i.apply_symm_apply]
  have hcont : Continuous g := continuous_pi fun τ => continuous_pi fun j =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (i.symm τ).property).continuous.comp
      ((continuous_apply j).comp (continuous_apply (i.symm τ)))
  have h := hg.denseRange.comp (realCompletionVectorWeakApproximation E d) hcont
  convert h using 1
  funext x τ j
  let p := i.symm τ
  change τ (x j) = InfinitePlace.Completion.extensionEmbeddingOfIsReal p.property
    (algebraMap E p.val.Completion (x j))
  change τ (x j) = InfinitePlace.Completion.extensionEmbeddingOfIsReal p.property
    ((WithAbs.equiv p.val.val).symm (x j) : p.val.Completion)
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply]
  exact congrArg (fun t : E →+* ℝ => t (x j)) (i.apply_symm_apply τ).symm

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]

private def symmetricPart (σ : AlgebraInvolution E A) : A →ₗ[E] A :=
  (1 / 2 : E) • (LinearMap.id + σ.linear)

omit [NumberField E] [IsTotallyReal E] in
private theorem symmetricPart_fixed (σ : AlgebraInvolution E A) (a : A) :
    σ (symmetricPart σ a) = symmetricPart σ a := by
  change σ ((1 / 2 : E) • (a + σ a)) = (1 / 2 : E) • (a + σ a)
  rw [σ.apply_smul, σ.apply_add, σ.apply_apply, add_comm]

omit [NumberField E] [IsTotallyReal E] in
private theorem symmetricPart_baseChange_apply (σ : AlgebraInvolution E A) (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    ∀ x : ℝ ⊗[E] A, (symmetricPart σ).baseChange ℝ x =
      (1 / 2 : ℝ) • (x + σ.baseChange ℝ x) := by
  let : Algebra E ℝ := τ.toAlgebra
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]
    abel
  | tmul s a =>
    simp only [LinearMap.baseChange_tmul, AlgebraInvolution.baseChange_tmul, symmetricPart,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
    rw [← TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul]
    change (τ (1 / 2) * s) ⊗ₜ[E] (a + σ a) = ((1 / 2 : ℝ) * s) ⊗ₜ[E] (a + σ a)
    have ht : τ (2 : E) = 2 := map_ofNat τ 2
    simp [ht]

omit [NumberField E] [IsTotallyReal E] in
private theorem isUnit_of_realBaseChange [FiniteDimensional E A] (τ : E →+* ℝ) (a : A) :
    letI : Algebra E ℝ := τ.toAlgebra
    IsUnit ((1 : ℝ) ⊗ₜ[E] a) → IsUnit a := by
  let : Algebra E ℝ := τ.toAlgebra
  intro ha
  let i : A →ₐ[E] ℝ ⊗[E] A := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (algebraMap E ℝ).injective
  have hmul : Function.Injective (LinearMap.mulLeft E a) := by
    intro x y hxy
    change a * x = a * y at hxy
    apply hi
    apply ha.mul_right_injective
    change i a * i x = i a * i y
    rw [← map_mul, ← map_mul, hxy]
  exact IsUnit.isUnit_iff_mulLeft_bijective.mpr
    ⟨hmul, (LinearMap.injective_iff_surjective).mp hmul⟩

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "θ" => matrixTranspose (AlgebraInvolution.ofStar (R := ℝ) (A := ℂ)) n

private def realTwistGram (D : CentralSimpleUnitaryData E K A n) (τ : E →+* ℝ) (a : A) : M :=
  let : Algebra E ℝ := τ.toAlgebra
  let G := realHermitianChart D (by have := D.rank_gt_one; omega) τ
  (G.gram : M) * G.equiv (1 ⊗ₜ[E] a)

private theorem realTwistGram_hermitian (D : CentralSimpleUnitaryData E K A n)
    (τ : E →+* ℝ) (a : A) (ha : D.involution a = a) :
    star (realTwistGram D τ a) = realTwistGram D τ a := by
  let : Algebra E ℝ := τ.toAlgebra
  let G := realHermitianChart D (by have := D.rank_gt_one; omega) τ
  let Y := G.equiv (1 ⊗ₜ[E] a)
  have h : (θ).adjoint G.gram G.hermitian Y = Y := by
    rw [← G.adjoint_eq, AlgebraInvolution.baseChange_tmul, ha]
  have he := congrArg (fun Z : M => (G.gram : M) * Z) h
  change θ ((G.gram : M) * Y) = (G.gram : M) * Y
  rw [(θ).apply_mul, G.hermitian]
  simpa only [AlgebraInvolution.adjoint_apply, ← mul_assoc, Units.mul_inv, one_mul] using he

private theorem hasSignature_twist_of_gram_congruence (D : CentralSimpleUnitaryData E K A n)
    (τ : E →+* ℝ) (r : ℕ) (hr : r ≤ n) (t : Aˣ) (ht : D.involution (t : A) = t)
    (P : Mˣ) (hP : star (P : M) * signatureMatrix n r * (P : M) = realTwistGram D τ t) :
    HasSignature (D.toSecondKindInvolution.twist t ht) τ n r := by
  let : Algebra E ℝ := τ.toAlgebra
  let G := realHermitianChart D (by have := D.rank_gt_one; omega) τ
  let j : A →ₐ[E] ℝ ⊗[E] A := Algebra.TensorProduct.includeRight
  let u := Units.map (G.equiv.toMonoidHom.comp j.toMonoidHom) t
  have hu : (θ).adjoint G.gram G.hermitian (u : M) = u := by
    change (θ).adjoint G.gram G.hermitian (G.equiv (1 ⊗ₜ[E] (t : A))) =
      G.equiv (1 ⊗ₜ[E] (t : A))
    rw [← G.adjoint_eq, AlgebraInvolution.baseChange_tmul, ht]
  let H := G.gram * u
  have hH := (θ).adjoint_gram_mul G.gram u G.hermitian hu
  have hChart (x : ℝ ⊗[E] A) :
      G.equiv ((D.toSecondKindInvolution.twist t ht).involution.baseChange ℝ x) =
        (θ).adjoint H hH (G.equiv x) := by
    change G.equiv ((D.involution.adjoint t ht).baseChange ℝ x) = _
    rw [AlgebraInvolution.baseChange_adjoint_apply, map_mul, map_mul, G.adjoint_eq]
    exact (θ).adjoint_adjoint_apply G.gram u G.hermitian hu hH (G.equiv x)
  let J := signatureUnit n r
  have hU : (θ).units P * J * P = H := Units.ext hP
  have hCongr : θ (↑P⁻¹ : M) * (H : M) * (↑P⁻¹ : M) = J := by
    change (↑((θ).units P⁻¹ * H * P⁻¹) : M) = J
    apply congrArg Units.val
    rw [(θ).units_inv, ← hU]
    group
  let f := matrixBasisChange (R := ℝ) P⁻¹
  refine ⟨hr, G.equiv.trans f, fun x => ?_⟩
  change f (G.equiv ((D.toSecondKindInvolution.twist t ht).involution.baseChange ℝ x)) =
    signatureAdjoint n r (f (G.equiv x))
  rw [hChart]
  exact matrixBasisChange_adjoint θ H J P⁻¹ hH (signatureMatrix_star n r) hCongr (G.equiv x)

set_option maxHeartbeats 800000 in
/-- One symmetric global unit prescribes the signatures of the twisted
involution at all real embeddings. -/
theorem exists_realSignature_twist (D : CentralSimpleUnitaryData E K A n)
    (r : (E →+* ℝ) → ℕ) (hr : ∀ τ, r τ ≤ n) :
    ∃ t : Aˣ, ∃ ht : D.involution (t : A) = t,
      ∀ τ, HasSignature (D.toSecondKindInvolution.twist t ht) τ n (r τ) := by
  let : FiniteDimensional K A := D.finite
  let : FiniteDimensional E A := Module.Finite.trans K A
  let nA := Module.finrank E A
  let B := Module.finBasis E A
  let G (τ : E →+* ℝ) := realHermitianChart D (by have := D.rank_gt_one; omega) τ
  let m (τ : E →+* ℝ) : (Fin nA → ℝ) →ₗ[ℝ] M :=
    let : Algebra E ℝ := τ.toAlgebra
    (G τ).equiv.toLinearMap.comp (((symmetricPart D.involution).baseChange ℝ).comp
      (B.baseChange ℝ).equivFun.symm.toLinearMap)
  let form (τ : E →+* ℝ) (x : Fin nA → ℝ) : M := ((G τ).gram : M) * m τ x
  let U (τ : E →+* ℝ) := signatureCongruenceNeighborhood n (r τ)
  let V (τ : E →+* ℝ) := form τ ⁻¹' (U τ).val
  have hV (τ : E →+* ℝ) : IsOpen (V τ) :=
    (U τ).property.1.preimage (continuous_const.mul (m τ).continuous_of_finiteDimensional)
  have hVnonempty (τ : E →+* ℝ) : (V τ).Nonempty := by
    let : Algebra E ℝ := τ.toAlgebra
    let J := signatureUnit n (r τ)
    let g := G τ
    let a := g.equiv.symm ((↑g.gram⁻¹ : M) * (J : M))
    have hJ : (θ).units J = J := Units.ext (signatureMatrix_star n (r τ))
    have hG : (θ).units g.gram = g.gram := Units.ext g.hermitian
    have ha : D.involution.baseChange ℝ a = a := by
      apply g.equiv.injective
      rw [g.adjoint_eq]
      change (θ).adjoint g.gram g.hermitian
        (g.equiv (g.equiv.symm ((↑g.gram⁻¹ : M) * (J : M)))) = _
      rw [g.equiv.apply_symm_apply]
      change (↑(g.gram⁻¹ * (θ).units (g.gram⁻¹ * J) * g.gram) : M) = ↑(g.gram⁻¹ * J)
      apply congrArg Units.val
      rw [(θ).units_mul, (θ).units_inv, hJ, hG]
      group
    have hproj : (symmetricPart D.involution).baseChange ℝ a = a := by
      rw [symmetricPart_baseChange_apply D.involution τ, ha, ← two_smul ℝ, smul_smul,
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
    refine ⟨(B.baseChange ℝ).equivFun a, ?_⟩
    change ((g.gram : M) *
      g.equiv ((symmetricPart D.involution).baseChange ℝ
        ((B.baseChange ℝ).equivFun.symm ((B.baseChange ℝ).equivFun a)))) ∈ (U τ).val
    rw [LinearEquiv.symm_apply_apply, hproj]
    change (g.gram : M) * g.equiv (g.equiv.symm ((↑g.gram⁻¹ : M) * (J : M))) ∈ (U τ).val
    rw [g.equiv.apply_symm_apply, Units.mul_inv_cancel_left]
    exact (U τ).property.2.1
  obtain ⟨x, hx⟩ := (denseRange_realEmbeddingVectors E nA).exists_mem_open
    (isOpen_set_pi Set.finite_univ (fun τ _ => hV τ)) (Set.univ_pi_nonempty_iff.mpr hVnonempty)
  let a := B.equivFun.symm x
  let t := symmetricPart D.involution a
  have ht : D.involution t = t := symmetricPart_fixed D.involution a
  have hmem (τ : E →+* ℝ) : realTwistGram D τ t ∈ (U τ).val := by
    let : Algebra E ℝ := τ.toAlgebra
    have hτ := hx τ (Set.mem_univ _)
    have hb : (B.baseChange ℝ).equivFun ((1 : ℝ) ⊗ₜ[E] a) = fun j => τ (x j) := by
      funext j
      change (B.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[E] a) j = τ (x j)
      rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      change τ (B.equivFun a j) = τ (x j)
      rw [LinearEquiv.apply_symm_apply]
    change ((G τ).gram : M) * (G τ).equiv
      ((symmetricPart D.involution).baseChange ℝ ((B.baseChange ℝ).equivFun.symm
        (fun j => τ (x j)))) ∈ (U τ).val at hτ
    rw [← hb, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul] at hτ
    exact hτ
  have hcongr (τ : E →+* ℝ) :
      ∃ P : Mˣ, star (P : M) * signatureMatrix n (r τ) * (P : M) = realTwistGram D τ t :=
    (U τ).property.2.2 _ (hmem τ) (realTwistGram_hermitian D τ t ht)
  let τ₀ : E →+* ℝ :=
    (IsTotallyReal.complexEmbedding_isReal (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom).embedding
  have hunit : IsUnit t := by
    let : Algebra E ℝ := τ₀.toAlgebra
    obtain ⟨P, hP⟩ := hcongr τ₀
    let g := G τ₀
    have h := ((θ).units P * signatureUnit n (r τ₀) * P).isUnit
    change IsUnit (star (P : M) * signatureMatrix n (r τ₀) * (P : M)) at h
    rw [hP] at h
    change IsUnit ((g.gram : M) * g.equiv (1 ⊗ₜ[E] t)) at h
    have hu := (g.gram⁻¹).isUnit.mul h
    rw [Units.inv_mul_cancel_left] at hu
    have h' := hu.map g.equiv.symm.toMonoidHom
    change IsUnit (g.equiv.symm (g.equiv ((1 : ℝ) ⊗ₜ[E] t))) at h'
    rw [g.equiv.symm_apply_apply] at h'
    apply isUnit_of_realBaseChange τ₀ t
    exact h'
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [hunit.unit_spec, ht]
  · intro τ
    obtain ⟨P, hP⟩ := hcongr τ
    exact hasSignature_twist_of_gram_congruence D τ (r τ) (hr τ) hunit.unit _ P
      (by rwa [hunit.unit_spec])

/-- The twisted second-kind involution on the original algebra, with its
prescribed signatures at all real embeddings. -/
def realSignatureTwist (D : CentralSimpleUnitaryData E K A n)
    (r : (E →+* ℝ) → ℕ) (hr : ∀ τ, r τ ≤ n) :
    {σ : SecondKindInvolution E K A // ∀ τ, HasSignature σ τ n (r τ)} :=
  let h := exists_realSignature_twist D r hr
  ⟨D.toSecondKindInvolution.twist h.choose h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Langlands.Shimura.FiniteUnitary
