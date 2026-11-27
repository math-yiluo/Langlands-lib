import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisStabilizer
import Langlands.GroupScheme.Quaternionic.QuaternionicProperWittSplit
import Langlands.GroupScheme.Quaternionic.QuaternionicSkewQuadraticComparison
import Langlands.GroupScheme.Quaternionic.QuaternionCoefficientDichotomy
import Langlands.GroupScheme.Quaternionic.BinaryQuaternionAction
import Langlands.GroupScheme.SymplecticInnerForm.SymplecticInvolutionAntihermitian
import Langlands.GroupScheme.CentralSimpleNormOneTransport
import Langlands.Algebra.ReducedNormScalarExtension

/-! # Proper Witt transitivity over every field extension

For a central quaternion division algebra `D` over a field `F` of characteristic zero and a
field `K ⊇ F`, the algebra `K ⊗ D` is either split or a division algebra. In the split case
proper Witt transitivity for antihermitian Gram matrices is the split-chart theorem; in the
division case it is the theorem for quaternion division algebras applied to `K ⊗ D`, with the
extended orthogonal involution, after identifying its quaternion conjugation and its matrix
reduced norm with the extended ones.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

open FiniteAlgebraUnits.MatrixPoints Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

section NormComparison

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D]

/-- The matrix comparison `K ⊗ M_N(D) ≃ M_N(K ⊗ D)` as an isomorphism of `K`-algebras. -/
def coefficientAlgEquiv (K : Type u) [Field K] [Algebra F K] (N : ℕ) :
    K ⊗[F] Matrix (Fin N) (Fin N) D ≃ₐ[K] Matrix (Fin N) (Fin N) (K ⊗[F] D) :=
  AlgEquiv.ofRingEquiv (f := (coefficientEquiv (m := Fin N) F D K).toRingEquiv) (fun r => by
    ext i j
    change coefficientEquiv F D K (r ⊗ₜ[F] (1 : Matrix (Fin N) (Fin N) D)) i j = _
    rw [coefficientEquiv_tmul, Matrix.algebraMap_matrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      rfl
    · simp only [hij, ↓reduceIte, TensorProduct.tmul_zero])

theorem reducedNorm_matrix_baseChange (K : Type u) [Field K] [Algebra F K] (N : ℕ) [NeZero N]
    (p : Matrix (Fin N) (Fin N) (K ⊗[F] D)) :
    letI : IsSimpleRing (K ⊗[F] D) := isSimpleRing_baseChange F D K
    letI : Algebra.IsCentral K (K ⊗[F] D) := isCentral_baseChange F D K
    reducedNorm K (Matrix (Fin N) (Fin N) (K ⊗[F] D)) K ((1 : K) ⊗ₜ[K] p) =
      matrixReducedNorm K p := by
  let : IsSimpleRing (K ⊗[F] D) := isSimpleRing_baseChange F D K
  let : Algebra.IsCentral K (K ⊗[F] D) := isCentral_baseChange F D K
  let : IsSimpleRing (K ⊗[F] Matrix (Fin N) (Fin N) D) :=
    isSimpleRing_baseChange F (Matrix (Fin N) (Fin N) D) K
  let : Algebra.IsCentral K (K ⊗[F] Matrix (Fin N) (Fin N) D) :=
    isCentral_baseChange F (Matrix (Fin N) (Fin N) D) K
  let φ := coefficientAlgEquiv (F := F) (D := D) K N
  let A0 : CSA.{u, u} F := { toAlgCat := AlgCat.of F (Matrix (Fin N) (Fin N) D) }
  have h1 : (1 : K) ⊗ₜ[K] p =
      Algebra.TensorProduct.map (AlgHom.id K K) φ.toAlgHom ((1 : K) ⊗ₜ[K] φ.symm p) := by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    congr 1
    exact (φ.apply_symm_apply p).symm
  rw [h1, reducedNorm_algEquiv φ K]
  have h2 := reducedNorm_baseChange A0 K (φ.symm p)
  exact h2

end NormComparison

section Witt

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

/-- Proper Witt transitivity over a field splitting `D`. -/
theorem properWittAt_of_split (K : Type u) [Field K] [Algebra F K]
    (e : K ⊗[F] D ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ProperWittAt (σ.quaternionConjugation hdim hsym) K N := by
  intro G hG hu x y hx hxy
  exact quaternionicProperWittSplit F D K σ hdim hsym e (Fin N) (by simpa using hN) G hG hu x y
    hx hxy

omit [CharZero F] in
/-- Proper Witt transitivity over a field over which `D` stays a division algebra. -/
theorem properWittAt_of_isDomain (K : Type u) [Field K] [Algebra F K] [CharZero K]
    (hdom : IsDomain (K ⊗[F] D)) (N : ℕ) [NeZero N] :
    ProperWittAt (σ.quaternionConjugation hdim hsym) K N := by
  intro G hG hu x y hx hxy
  let : IsDomain (K ⊗[F] D) := hdom
  let : DivisionRing (K ⊗[F] D) := divisionRingOfFiniteDimensional K (K ⊗[F] D)
  let : Algebra.IsCentral K (K ⊗[F] D) := isCentral_baseChange F D K
  have hdimK : Module.finrank K (K ⊗[F] D) = 4 := Module.finrank_baseChange.trans hdim
  have hsymK : Module.finrank K (σ.baseChange K).symmetricSubspace = 3 :=
    (σ.finrank_symmetricSubspace_baseChange K).trans hsym
  have hτ : ∀ a, (σ.baseChange K).quaternionConjugation hdimK hsymK a =
      (σ.quaternionConjugation hdim hsym).baseChange K a := by
    intro a
    set lK := BinaryAction.tensorAlternatingUnit σ hdim hsym K
    have hlK : (lK : K ⊗[F] D) ∈ (σ.baseChange K).alternatingSubspace :=
      BinaryAction.tensorAlternatingUnit_mem σ hdim hsym K
    set l' := (σ.baseChange K).quaternionAlternatingUnit hdimK hsymK
    have hl' := (σ.baseChange K).quaternionAlternatingUnit_mem hdimK hsymK
    have hline := (σ.baseChange K).finrank_alternatingSubspace_of_dimensions hdimK hsymK
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨lK, hlK⟩ : (σ.baseChange K).alternatingSubspace)
      (fun h => lK.ne_zero (congrArg Subtype.val h))).mp hline ⟨l', hl'⟩
    have hc' : (l' : K ⊗[F] D) = algebraMap K (K ⊗[F] D) c * lK := by
      rw [← Algebra.smul_def]
      exact (congrArg Subtype.val hc).symm
    have hc0 : algebraMap K (K ⊗[F] D) c ≠ 0 := by
      intro h
      rw [h, zero_mul] at hc'
      exact l'.ne_zero hc'
    rw [BinaryAction.quaternionConjugation_baseChange]
    change (l' : K ⊗[F] D) * (σ.baseChange K) a * (l' : K ⊗[F] D)⁻¹ = _
    rw [hc', mul_inv_rev, Units.val_inv_eq_inv_val]
    calc algebraMap K (K ⊗[F] D) c * lK * (σ.baseChange K) a *
          ((lK : K ⊗[F] D)⁻¹ * (algebraMap K (K ⊗[F] D) c)⁻¹)
        = algebraMap K (K ⊗[F] D) c * (lK * (σ.baseChange K) a * (lK : K ⊗[F] D)⁻¹) *
            (algebraMap K (K ⊗[F] D) c)⁻¹ := by
          simp only [mul_assoc]
      _ = lK * (σ.baseChange K) a * (lK : K ⊗[F] D)⁻¹ *
            (algebraMap K (K ⊗[F] D) c * (algebraMap K (K ⊗[F] D) c)⁻¹) := by
          rw [Algebra.commutes, mul_assoc]
      _ = lK * (σ.baseChange K) a * (lK : K ⊗[F] D)⁻¹ := by
          rw [mul_inv_cancel₀ hc0, mul_one]
  have hmat : ∀ M : Matrix (Fin N) (Fin N) (K ⊗[F] D),
      ((σ.baseChange K).quaternionConjugation hdimK hsymK).matrix (Fin N) M =
        ((σ.quaternionConjugation hdim hsym).baseChange K).matrix (Fin N) M := by
    intro M
    ext i j
    simp only [FirstKindInvolution.matrix_apply, hτ]
  have hses : ∀ (M : Matrix (Fin N) (Fin N) (K ⊗[F] D)) (v w : Fin N → K ⊗[F] D),
      ((σ.baseChange K).quaternionConjugation hdimK hsymK).sesqForm M v w =
        ((σ.quaternionConjugation hdim hsym).baseChange K).matrixSesqBilin M v w := by
    intro M v w
    simp only [FirstKindInvolution.sesqForm, hτ]
    rfl
  obtain ⟨p, hp, hn, hpx⟩ := (σ.baseChange K).exists_properIsometry_skewGram_division hdimK hsymK
    (I := Fin N) (H := G) (by rw [hmat]; exact hG) (x := x) (y := y)
    (by rw [hses]; exact hx.ne_zero) (by rw [hses, hses]; exact hxy)
  refine ⟨p, ?_, ?_, hpx⟩
  · rw [← hmat]
    exact hp
  · rw [← reducedNorm_matrix_baseChange]
    exact hn

/-- Proper Witt transitivity in rank at least two over every field extension of
characteristic zero. -/
theorem properWittAt (K : Type u) [Field K] [Algebra F K] [CharZero K] (N : ℕ) [NeZero N]
    (hN : 2 ≤ N) : ProperWittAt (σ.quaternionConjugation hdim hsym) K N := by
  rcases quaternionCoefficientDichotomy F D K hdim with hdom | he
  · exact properWittAt_of_isDomain σ hdim hsym K hdom N
  · obtain ⟨e⟩ := he
    exact properWittAt_of_split σ hdim hsym K e N hN

end Witt

end Langlands.GroupScheme.Quaternionic.SkewUnitary
