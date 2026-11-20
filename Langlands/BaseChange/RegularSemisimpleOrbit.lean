import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof
import Langlands.LinearAlgebra.MatrixAEvalConjugacyProof
import Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Closed regular semisimple conjugacy orbits and compact support -/

noncomputable section

namespace Langlands.BaseChange

open Function _root_.Polynomial
open HarmonicAnalysis.Distribution (charpolyCoeffs charpoly_eq_of_coeff_eq
  charpolyCoeffs_conj continuous_charpolyCoeffs conjAct_orbit_eq)
open JacquetLanglands (IsRegularSemisimple)
open QuotientIntegration TraceFormula _root_.Topology

universe u

section Algebra

variable {K : Type u} [Field K] {n : ℕ}

/-- An annihilating polynomial contains all the simple roots of a separable characteristic
polynomial. -/
private theorem charpoly_dvd_of_separable (A : Matrix (Fin n) (Fin n) K) {q : K[X]}
    (hsep : A.charpoly.Separable) (hq : q ≠ 0) (hA : aeval A q = 0) : A.charpoly ∣ q := by
  let Ω := AlgebraicClosure K
  let φ : K →+* Ω := algebraMap K Ω
  let B := A.map φ
  have hB : aeval B (q.map φ) = 0 := by
    rw [show aeval B (q.map φ) = (aeval A q).map φ by
      rw [Polynomial.aeval_map_algebraMap]
      exact Polynomial.aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId K Ω)) A q,
      hA, Matrix.map_zero _ (map_zero φ)]
  have hq' : q.map φ ≠ 0 := Polynomial.map_ne_zero hq
  have hroots : ∀ x ∈ (A.charpoly.map φ).roots, x ∈ (q.map φ).roots := by
    intro x hx
    have hxroot : B.charpoly.IsRoot x := by
      rw [Matrix.charpoly_map]
      exact (mem_roots (A.charpoly_monic.map φ).ne_zero).mp hx
    by_cases hn : Nonempty (Fin n)
    · have hspec := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hxroot
      have hmem := spectrum.subset_polynomial_aeval B (q.map φ) ⟨x, hspec, rfl⟩
      rw [hB, spectrum.zero_eq] at hmem
      exact (mem_roots hq').mpr hmem
    · have : IsEmpty (Fin n) := not_nonempty_iff.mp hn
      simp [Matrix.charpoly_isEmpty] at hxroot
  have hle : (A.charpoly.map φ).roots ≤ (q.map φ).roots :=
    (Multiset.le_iff_subset (nodup_roots hsep.map)).mpr hroots
  apply (Polynomial.map_dvd_map' φ).mp
  rw [(IsAlgClosed.splits (A.charpoly.map φ)).eq_prod_roots_of_monic (A.charpoly_monic.map φ)]
  exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hq' _).mpr hle

/-- The polynomial module attached to a matrix with separable characteristic polynomial is
isomorphic to the quotient by that polynomial. -/
private theorem nonempty_aevalEquiv_quotient (A : Matrix (Fin n) (Fin n) K)
    (hsep : A.charpoly.Separable) :
    Nonempty (Module.AEval' A.mulVecLin ≃ₗ[K[X]] K[X] ⧸ Ideal.span {A.charpoly}) := by
  classical
  let p := A.charpoly
  have hp : p.Monic := A.charpoly_monic
  have hann : aeval A.mulVecLin p = 0 := by
    rw [show p = A.mulVecLin.charpoly from (Matrix.charpoly_mulVecLin A).symm]
    exact LinearMap.aeval_self_charpoly _
  obtain ⟨m, q, _, hq, ⟨e⟩⟩ :=
    polynomialModuleBoundedCyclicDecomposition K (Fin n → K) A.mulVecLin p hp.ne_zero hann
  let Q := ∏ i, q i
  have hQ : Q.Monic := monic_prod_of_monic _ _ fun i _ => (hq i).1
  have hAnnQ : aeval A Q = 0 := by
    let L := Matrix.toLinAlgEquiv' (n := Fin n) (R := K)
    apply L.injective
    rw [map_zero, ← Polynomial.aeval_algHom_apply L A Q]
    change aeval A.mulVecLin Q = 0
    apply LinearMap.ext
    intro v
    apply (Module.AEval'.of A.mulVecLin).injective
    rw [LinearMap.zero_apply, map_zero]
    change (Module.AEval'.of A.mulVecLin) (aeval A.mulVecLin Q • v) = 0
    rw [Module.AEval.of_aeval_smul]
    apply e.injective
    rw [map_smul, map_zero]
    funext i
    have hmem : Q ∈ Ideal.span ({q i} : Set K[X]) :=
      Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    change (Ideal.Quotient.mk (Ideal.span {q i}) Q) * (e ((Module.AEval'.of A.mulVecLin) v)) i = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul]
  have (i : Fin m) : Module.Finite K (K[X] ⧸ Ideal.span {q i}) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis (hq i).1.ne_zero).basis
  have hdim : Q.natDegree = p.natDegree := by
    calc
      Q.natDegree = ∑ i, (q i).natDegree := natDegree_prod_of_monic _ _ fun i _ => (hq i).1
      _ = Module.finrank K ((i : Fin m) → K[X] ⧸ Ideal.span {q i}) := by
        rw [Module.finrank_pi_fintype]
        simp only [finrank_quotient_span_eq_natDegree]
      _ = Module.finrank K (Fin n → K) :=
        ((Module.AEval'.of A.mulVecLin).trans (e.restrictScalars K)).finrank_eq.symm
      _ = p.natDegree := by
        rw [Module.finrank_fin_fun, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hQp : Q = p := eq_of_monic_of_dvd_of_natDegree_le hp hQ
    (charpoly_dvd_of_separable A hsep hQ.ne_zero hAnnQ) hdim.le
  let I (i : Fin m) : Ideal K[X] := Ideal.span {q i}
  have hcoprime : Pairwise (IsCoprime on I) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    apply IsRelPrime.isCoprime
    apply IsRelPrime.of_squarefree_mul
    apply hsep.squarefree.squarefree_of_dvd
    rw [← show Q = A.charpoly from hQp]
    change q i * q j ∣ ∏ k, q k
    rw [← Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)]
    exact mul_dvd_mul_left _
      (Finset.dvd_prod_of_mem q (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩))
  have hI : (⨅ i, I i) = Ideal.span {p} := by
    calc
      (⨅ i, I i) = ⨅ i ∈ (Finset.univ : Finset (Fin m)), I i := by simp
      _ = ∏ i, I i := (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := Finset.univ) (fun _ _ _ _ hij => hcoprime hij)).symm
      _ = Ideal.span {Q} := Ideal.prod_span_singleton _ _
      _ = Ideal.span {p} := by rw [hQp]
  let crt := Ideal.quotientInfRingEquivPiQuotient I hcoprime
  let crtAlg : (K[X] ⧸ (⨅ i, I i)) ≃ₐ[K[X]] ((i : Fin m) → K[X] ⧸ I i) :=
    { crt with
      commutes' := fun _ => rfl }
  exact ⟨e.trans (crtAlg.toLinearEquiv.symm.trans (Submodule.quotEquivOfEq _ _ hI))⟩

/-- A matrix with separable characteristic polynomial is determined up to conjugacy by
that polynomial. -/
theorem exists_matrix_conj_of_charpoly_eq_of_separable (A B : Matrix (Fin n) (Fin n) K)
    (hsep : A.charpoly.Separable) (hchar : B.charpoly = A.charpoly) :
    ∃ g : GeneralLinear n K,
      (g : Matrix (Fin n) (Fin n) K) * A * ((g⁻¹ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K) = B := by
  obtain ⟨eA⟩ := nonempty_aevalEquiv_quotient A hsep
  obtain ⟨eB⟩ : Nonempty (Module.AEval' B.mulVecLin ≃ₗ[K[X]] K[X] ⧸ Ideal.span {A.charpoly}) := by
    rw [← hchar]
    exact nonempty_aevalEquiv_quotient B (hchar.symm ▸ hsep)
  exact matrixAEvalConjugacy K n A B (eA.trans eB.symm)

end Algebra

section Orbit

variable {K : Type u} [Field K] {n : ℕ}

local notation "G" => GeneralLinear n K

/-- The conjugacy orbit of a regular semisimple element is a characteristic-polynomial fiber. -/
theorem regularSemisimpleOrbit_eq_fiber (γ : G) (hγ : IsRegularSemisimple γ) :
    MulAction.orbit (ConjAct G) γ = charpolyCoeffs n ⁻¹' {charpolyCoeffs n γ} := by
  rw [conjAct_orbit_eq]
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact charpolyCoeffs_conj a γ
  · intro hg
    obtain ⟨a, ha⟩ := exists_matrix_conj_of_charpoly_eq_of_separable
      (γ : Matrix (Fin n) (Fin n) K) (g : Matrix (Fin n) (Fin n) K)
      hγ (charpoly_eq_of_coeff_eq _ _ (congrFun hg))
    exact ⟨a, Units.ext ha⟩

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- The conjugacy orbit of a regular semisimple element is closed. -/
theorem isClosed_regularSemisimpleOrbit (γ : G) (hγ : IsRegularSemisimple γ) :
    IsClosed (MulAction.orbit (ConjAct G) γ) := by
  rw [regularSemisimpleOrbit_eq_fiber γ hγ]
  exact isClosed_singleton.preimage (continuous_charpolyCoeffs n)

variable [LocallyCompactSpace (GeneralLinear n K)] [SigmaCompactSpace (GeneralLinear n K)]

/-- The map `[x] ↦ x⁻¹ * γ * x` from left centralizer cosets to the closed conjugacy orbit
is a homeomorphism. -/
def regularSemisimpleOrbitHomeomorph (γ : G) (hγ : IsRegularSemisimple γ) :
    LeftQuotient (glCentralizer γ) ≃ₜ MulAction.orbit (ConjAct G) γ := by
  let O := MulAction.orbit (ConjAct G) γ
  let f₀ : LeftQuotient (glCentralizer γ) → G :=
    twistedOrbitFunction (MonoidHom.id G) γ id
  have hq := leftQuotient_isOpenQuotientMap (glCentralizer γ)
  have hf₀ (x : G) : f₀ (leftQuotientMap (glCentralizer γ) x) = x⁻¹ * γ * x := rfl
  have hf₀O (q : LeftQuotient (glCentralizer γ)) : f₀ q ∈ O := by
    obtain ⟨x, rfl⟩ := hq.surjective q
    exact MulAction.mem_orbit_iff.mpr ⟨ConjAct.toConjAct x⁻¹, by
      rw [ConjAct.toConjAct_smul, inv_inv, hf₀]⟩
  let f : LeftQuotient (glCentralizer γ) → O := fun q => ⟨f₀ q, hf₀O q⟩
  have hinj : Injective f := by
    intro q r hqr
    obtain ⟨x, rfl⟩ := hq.surjective q
    obtain ⟨y, rfl⟩ := hq.surjective r
    have h : x⁻¹ * γ * x = y⁻¹ * γ * y := congrArg Subtype.val hqr
    apply Quotient.sound
    change QuotientGroup.rightRel (glCentralizer γ) x y
    rw [QuotientGroup.rightRel_apply, mem_twistedCentralizer, MonoidHom.id_apply]
    calc
      (y * x⁻¹)⁻¹ * γ * (y * x⁻¹) = x * (y⁻¹ * γ * y) * x⁻¹ := by group
      _ = γ := by rw [← h]; group
  have hsurj : Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hg
    refine ⟨leftQuotientMap _ (ConjAct.ofConjAct a)⁻¹, Subtype.ext ?_⟩
    change f₀ (leftQuotientMap _ (ConjAct.ofConjAct a)⁻¹) = g
    rw [hf₀, inv_inv, ← ConjAct.smul_def]
    exact ha
  let : TopologicalSpace (ConjAct G) := inferInstanceAs (TopologicalSpace G)
  let : IsTopologicalGroup (ConjAct G) := inferInstanceAs (IsTopologicalGroup G)
  let : SigmaCompactSpace (ConjAct G) := inferInstanceAs (SigmaCompactSpace G)
  have : ContinuousSMul (ConjAct G) G := by
    refine ⟨?_⟩
    have hof : Continuous (fun q : ConjAct G × G => (ConjAct.ofConjAct q.1 : G)) :=
      continuous_fst
    simp only [ConjAct.smul_def]
    exact (hof.mul continuous_snd).mul hof.inv
  let : ContinuousSMul (ConjAct G) O :=
    IsInducing.subtypeVal.continuousSMul continuous_id rfl
  let : LocallyCompactSpace O := (isClosed_regularSemisimpleOrbit γ hγ).locallyCompactSpace
  let γ' : O := ⟨γ, MulAction.mem_orbit_self γ⟩
  have heq : f ∘ leftQuotientMap _ = fun x : G => ConjAct.toConjAct x⁻¹ • γ' := by
    funext x
    apply Subtype.ext
    change f₀ (leftQuotientMap _ x) = ConjAct.toConjAct x⁻¹ • γ
    rw [hf₀, ConjAct.toConjAct_smul, inv_inv]
  refine (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen ?_ ?_
  · apply hq.isQuotientMap.continuous_iff.mpr
    exact ((continuous_id.inv.mul continuous_const).mul continuous_id).subtype_mk _
  · apply hq.isOpenMap_iff.mpr
    change IsOpenMap (f ∘ leftQuotientMap (glCentralizer γ))
    rw [heq]
    have hinv : IsOpenMap (fun x : G => ConjAct.toConjAct x⁻¹) := isOpenMap_inv G
    exact (isOpenMap_smul_of_sigmaCompact γ').comp hinv

@[simp] theorem regularSemisimpleOrbitHomeomorph_mk (γ : G) (hγ : IsRegularSemisimple γ)
    (x : G) :
    (regularSemisimpleOrbitHomeomorph γ hγ (leftQuotientMap (glCentralizer γ) x) : G) =
    x⁻¹ * γ * x := rfl

/-- The ordinary orbital integrand is the original function pulled back from the closed orbit. -/
theorem regularSemisimpleOrbitFunction_eq_comp (γ : G) (hγ : IsRegularSemisimple γ)
    {A : Type*} (f : G → A) :
    twistedOrbitFunction (MonoidHom.id G) γ f =
      f ∘ Subtype.val ∘ regularSemisimpleOrbitHomeomorph γ hγ := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- Compact support on the group gives compact support of the ordinary orbital integrand
at a regular semisimple element. -/
theorem hasCompactSupport_regularSemisimpleOrbitFunction (γ : G)
    (hγ : IsRegularSemisimple γ) {A : Type*} [Zero A] {f : G → A} (hf : HasCompactSupport f) :
    HasCompactSupport (twistedOrbitFunction (MonoidHom.id G) γ f) := by
  rw [regularSemisimpleOrbitFunction_eq_comp γ hγ f]
  have hclosed := (isClosed_regularSemisimpleOrbit γ hγ).isClosedEmbedding_subtypeVal
  exact hf.comp_isClosedEmbedding (hclosed.comp
    (regularSemisimpleOrbitHomeomorph γ hγ).isClosedEmbedding)

end Orbit

end Langlands.BaseChange
