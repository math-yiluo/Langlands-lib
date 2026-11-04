import Langlands.Representation.Exponents.NormalizedJacquetCompressionSpectrumStatement
import Langlands.Representation.Exponents.CentralEigenvalueDetectionProof

/-! # Spectral bound for the actual normalized Jacquet compression -/

noncomputable section

namespace Langlands

universe uG uV

open Jacquet

/-- Nonzero compression eigenvectors survive in the actual quotient. -/
theorem jacquet_mk_ne_zero_of_compression_eigenvector
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (g : G)
    (h : IsIwahoriContraction K N M Nbar g)
    {μ : ℂ} (hμ : μ ≠ 0) (x : fixedVectors ρ K.toSubgroup)
    (hx : x ≠ 0) (heigen : compressedAction ρ hρ K hK g x = μ • x) :
    Jacquet.mk ρ N (x : V) ≠ 0 := by
  have hpow : ∀ r : ℕ, (compressedAction ρ hρ K hK g ^ r) x = μ ^ r • x := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, Module.End.mul_apply, heigen, map_smul, ih, smul_smul,
        pow_succ, mul_comm]
  intro hzero
  have hker : x ∈ LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) := by
    rw [LinearMap.mem_ker]
    exact Subtype.ext hzero
  rw [← powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN] at hker
  have hmono : Monotone
      (fun r : ℕ => LinearMap.ker (compressedAction ρ hρ K hK g ^ r)) := by
    intro r s hrs y hy
    rw [LinearMap.mem_ker] at hy ⊢
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
    rw [add_comm, pow_add, Module.End.mul_apply, hy, map_zero]
  obtain ⟨r, hr⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hker
  rw [LinearMap.mem_ker, hpow r] at hr
  exact hx ((smul_eq_zero.mp hr).resolve_left (pow_ne_zero r hμ))

/-- Strict full-center exponents of the actual normalized Jacquet module
bound every eigenvalue of compact compression by a contracting central point. -/
theorem norm_normalized_compression_eigenvalue_lt_one
    {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
    [NonarchimedeanGroup G] (N M Nbar : Subgroup G)
    (hN : IsClosed (N : Set G)) (hMN : M ≤ Subgroup.normalizer N)
    (hbasis : HasIwahoriContractionBasis N M Nbar)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (z : Subgroup.center M)
    (h : IsIwahoriContraction K N M Nbar ((z : M) : G))
    (hstrict : ∀ χ : Subgroup.center M →* ℂˣ,
      IsCentralExponent
        ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A).representation χ →
      ‖(χ z : ℂ)‖ < 1)
    (μ : ℂ) (x : fixedVectors A.representation K.toSubgroup)
    (hx : x ≠ 0)
    (heigen : compressedAction A.representation hA.1 K hK ((z : M) : G) x = μ • x) :
    ‖(HaarModulus.closedInverseHalfCharacter N hN M hMN (z : M) : ℂ) * μ‖ < 1 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  let Q := (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A
  have hQ : Q.IsAdmissible :=
    Aubert.General.isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction
      N M Nbar hN hMN hbasis A hA
  let σ : Representation ℂ M (Jacquet.Localization.Coinvariants A.representation N 1) :=
    Langlands.twist (HaarModulus.closedInverseHalfCharacter N hN M hMN)
      (Jacquet.Localization.action A.representation N 1 M hMN
        (Jacquet.Localization.isInvariant_one N M hMN))
  have hσ : IsAdmissible σ := hQ
  let y := Jacquet.Localization.mk A.representation N 1 (x : A)
  have hy : y ≠ 0 := by
    intro hy
    have hm := jacquet_mk_ne_zero_of_compression_eigenvector A.representation hA.1
      K hK N M Nbar hMN ((z : M) : G) h hμ x hx heigen
    apply hm
    have ht := congrArg (Jacquet.Localization.trivialEquiv A.representation N M hMN) hy
    simpa only [y, map_zero, Jacquet.Localization.trivialEquiv_mk] using ht
  have hmk : Jacquet.mk A.representation N (A.representation ((z : M) : G) (x : A)) =
      μ • Jacquet.mk A.representation N (x : A) := by
    rw [← Jacquet.action_mk A.representation N M hMN (z : M)]
    rw [← mk_compressedAction_of_iwahoriContraction A.representation hA.1 hK h hMN x]
    simp only [heigen, SetLike.val_smul, map_smul]
  have hloc :
      Jacquet.Localization.mk A.representation N 1
          (A.representation ((z : M) : G) (x : A)) = μ • y := by
    apply (Jacquet.Localization.trivialEquiv A.representation N M hMN).injective
    rw [map_smul]
    change Jacquet.mk A.representation N
        (A.representation ((z : M) : G) (x : A)) =
      μ • Jacquet.mk A.representation N (x : A)
    exact hmk
  have hyeigen : σ (z : M) y =
      ((HaarModulus.closedInverseHalfCharacter N hN M hMN (z : M) : ℂ) * μ) • y := by
    change (HaarModulus.closedInverseHalfCharacter N hN M hMN (z : M) : ℂ) •
      Jacquet.Localization.mk A.representation N 1
        (A.representation ((z : M) : G) (x : A)) = _
    rw [hloc, smul_smul]
  obtain ⟨χ, hχ, hχz⟩ := exists_centralExponent_of_generalized_eigenvector σ hσ
    z ((HaarModulus.closedInverseHalfCharacter N hN M hMN (z : M) : ℂ) * μ) 1
    hy (by
      rw [pow_one]
      change σ (z : M) y -
        ((HaarModulus.closedInverseHalfCharacter N hN M hMN (z : M) : ℂ) * μ) • y = 0
      exact sub_eq_zero.mpr hyeigen)
  simpa only [hχz] using hstrict χ hχ

/-- The complete general normalized Jacquet compression spectrum proposition. -/
theorem normalizedJacquetCompressionSpectrum :
    NormalizedJacquetCompressionSpectrumStatement.{uG, uV} := by
  intro G _ _ _ _ N M Nbar hN hMN hbasis A hA K hK z h hstrict μ x hx heigen
  exact norm_normalized_compression_eigenvalue_lt_one N M Nbar hN hMN hbasis
    A hA K hK z h hstrict μ x hx heigen

end Langlands
