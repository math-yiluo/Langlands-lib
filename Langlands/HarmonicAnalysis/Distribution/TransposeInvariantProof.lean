import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement
import Langlands.HarmonicAnalysis.Distribution.LocalizationStatement
import Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement
import Langlands.LinearAlgebra.MatrixTransposeConjugateStatement
import Langlands.LinearAlgebra.MatrixCharpolyConjugacyStatement
import Langlands.HarmonicAnalysis.Distribution.LocalizationProof
import Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof
import Langlands.LinearAlgebra.MatrixTransposeConjugateProof
import Langlands.LinearAlgebra.MatrixCharpolyConjugacyProof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Transpose invariance of conjugation-invariant distributions on p-adic GL

Bernstein–Zelevinsky (1976), §7.3: for a conjugation-invariant distribution
`D` on `GL_{n+1}(F)`, the difference `D - τ_* D` is conjugation invariant and
anti-invariant under transposition `τ`. Localizing along the characteristic
polynomial reduces its vanishing to single fibres, each of which is a closed
finite union of conjugacy classes preserved by transposition.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

universe uG uK uF

open ConjAct

section Conjugation

variable {G : Type uG} [Group G]

/-- Orbits of the conjugation action are conjugacy classes. -/
theorem conjAct_orbit_eq (x : G) :
    MulAction.orbit (ConjAct G) x = {g | ∃ a : G, a * x * a⁻¹ = g} := by
  ext g
  simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨ofConjAct c, (ConjAct.smul_def c x).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨toConjAct a, ConjAct.toConjAct_smul a x⟩

variable [TopologicalSpace G] [NonarchimedeanGroup G] [LocallyCompactSpace G]
  [SigmaCompactSpace G] [T2Space G]

/-- The finite-orbit vanishing statement for the conjugation action of a group
on itself: a conjugation-invariant distribution supported in a closed finite
union of conjugacy classes and anti-invariant under a homeomorphism preserving
each of these classes vanishes. -/
theorem conjugationInvariant_finiteOrbit_vanishing
    (h3 : FiniteOrbitAntiInvariantVanishingStatement.{uG, uG})
    (σ : G ≃ₜ G) (Z : Set G) (s : Finset G) (hZ : IsClosed Z)
    (hZs : Z = ⋃ x ∈ s, {g | ∃ a : G, a * x * a⁻¹ = g})
    (hσ : ∀ z ∈ Z, (∃ a : G, a * z * a⁻¹ = σ z) ∧ ∃ a : G, a * z * a⁻¹ = σ.symm z)
    (D : Distribution G)
    (hsupp : ∀ f : SchwartzBruhat G, (∀ z ∈ Z, f z = 0) → D f = 0)
    (hD : IsConjugationInvariant D) (hσD : pushforward σ D = -D) : D = 0 := by
  let : TopologicalSpace (ConjAct G) := inferInstanceAs (TopologicalSpace G)
  have : NonarchimedeanGroup (ConjAct G) := inferInstanceAs (NonarchimedeanGroup G)
  have : LocallyCompactSpace (ConjAct G) := inferInstanceAs (LocallyCompactSpace G)
  have : SigmaCompactSpace (ConjAct G) := inferInstanceAs (SigmaCompactSpace G)
  have : ContinuousSMul (ConjAct G) G := by
    refine ⟨?_⟩
    have hof : Continuous fun q : ConjAct G × G => (ofConjAct q.1 : G) := continuous_fst
    simp only [ConjAct.smul_def]
    exact (hof.mul continuous_snd).mul hof.inv
  refine h3 (ConjAct G) G σ Z s hZ ?_ ?_ D hsupp ?_ hσD
  · simpa only [conjAct_orbit_eq] using hZs
  · intro z hz
    simp only [conjAct_orbit_eq, Set.mem_ofPred_eq]
    exact hσ z hz
  · intro c
    have he : (Homeomorph.smul c : G ≃ₜ G) = conjugationHomeomorph (ofConjAct c) := by
      ext x
      simp only [Homeomorph.smul_apply, ConjAct.smul_def, conjugationHomeomorph_apply]
    rw [he]
    exact hD (ofConjAct c)

end Conjugation

section CharacteristicPolynomial

variable {K : Type uK} [Field K]

/-- A characteristic polynomial is determined by its coefficients below the
dimension, since it is monic of degree the dimension. -/
theorem charpoly_eq_of_coeff_eq {m : ℕ} (x y : Matrix (Fin m) (Fin m) K)
    (h : ∀ i : Fin m, x.charpoly.coeff i = y.charpoly.coeff i) :
    x.charpoly = y.charpoly := by
  rw [x.charpoly_monic.as_sum, y.charpoly_monic.as_sum, Matrix.charpoly_natDegree_eq_dim,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  exact congrArg (fun c => Polynomial.C c * Polynomial.X ^ i) (h ⟨i, Finset.mem_range.mp hi⟩)

/-- The coefficients of the characteristic polynomial below the top degree. -/
def charpolyCoeffs (m : ℕ) (g : Matrix.GeneralLinearGroup (Fin m) K) : Fin m → K :=
  fun i => (g : Matrix (Fin m) (Fin m) K).charpoly.coeff i

theorem charpolyCoeffs_conj {m : ℕ} (a g : Matrix.GeneralLinearGroup (Fin m) K) :
    charpolyCoeffs m (a * g * a⁻¹) = charpolyCoeffs m g := by
  funext i
  simp only [charpolyCoeffs, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem charpolyCoeffs_transpose {m : ℕ} (g : Matrix.GeneralLinearGroup (Fin m) K) :
    charpolyCoeffs m (transposeHomeomorph m K g) = charpolyCoeffs m g := by
  funext i
  simp only [charpolyCoeffs, transposeHomeomorph_coe, Matrix.charpoly_transpose]

/-- The characteristic-polynomial coefficients are polynomial in the entries,
hence continuous. -/
theorem continuous_charpolyCoeffs (m : ℕ) :
    Continuous (charpolyCoeffs (K := K) m) := by
  refine continuous_pi fun i => ?_
  have h : (fun g : Matrix.GeneralLinearGroup (Fin m) K => charpolyCoeffs m g i) =
      fun g : Matrix.GeneralLinearGroup (Fin m) K => MvPolynomial.eval
        (fun ij : Fin m × Fin m => (g : Matrix (Fin m) (Fin m) K) ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom K) ((Matrix.charpoly.univ ℤ (Fin m)).coeff i)) := by
    funext g
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom,
      Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => Units.continuous_val.matrix_elem ij.1 ij.2)

end CharacteristicPolynomial

/-- Transpose invariance from the five focused prerequisites: localization
along the characteristic polynomial, finite-orbit vanishing, conjugacy of a
matrix to its transpose and finiteness of conjugacy classes in each fibre. -/
theorem generalLinearConjugationDistributionTranspose_of_prerequisites
    (h1 : EquivariantLocalizationStatement.{uF, uF, uF})
    (h3 : FiniteOrbitAntiInvariantVanishingStatement.{uF, uF})
    (h4 : MatrixTransposeConjugateStatement.{uF})
    (h5 : MatrixCharpolyFiniteConjugacyStatement.{uF}) :
    GeneralLinearConjugationDistributionTransposeStatement.{uF} := by
  intro p hp F
  let := F.canonicalNormedField
  intro n D hD
  classical
  let : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
  have : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier
  have : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  have : NonarchimedeanGroup (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearNonarchimedean (n + 1)
  have : LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  have : SigmaCompactSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
  have : T2Space (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearT2Space (n + 1)
  set τ := transposeHomeomorph (n + 1) F.Carrier with hτ
  set q := charpolyCoeffs (K := F.Carrier) (n + 1) with hq
  have hqconj : ∀ a g, q (a * g * a⁻¹) = q g := charpolyCoeffs_conj
  have hqτ : ∀ g, q (τ g) = q g := charpolyCoeffs_transpose
  -- Transposition preserves every conjugacy class.
  have hτconj : ∀ z : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier,
      ∃ a, a * z * a⁻¹ = τ z := by
    intro z
    obtain ⟨a, ha⟩ := h4 F.Carrier (n + 1) z
    exact ⟨a, Units.ext (by simpa only [Units.val_mul, hτ, transposeHomeomorph_coe] using ha)⟩
  have hτsymm : ∀ z, τ.symm z = τ z := fun z =>
    τ.symm_apply_eq.mpr (transposeHomeomorph_involutive (n + 1) F.Carrier z).symm
  -- The difference is conjugation invariant and transpose anti-invariant.
  let D' := D - pushforward τ D
  have hDτ : IsConjugationInvariant (pushforward τ D) :=
    IsConjugationInvariant.pushforward_transpose (n + 1) F.Carrier hD
  have hD'conj : IsConjugationInvariant D' := fun a => by
    simp only [D', map_sub, hD a, hDτ a]
  have hD'τ : pushforward τ D' = -D' := by
    simp only [D', map_sub, hτ, pushforward_transpose_involutive, neg_sub]
  -- Localization along the characteristic polynomial.
  let ι := Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier ⊕ Unit
  let h : ι → Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier ≃ₜ
      Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier :=
    Sum.elim conjugationHomeomorph fun _ => τ
  let χ : ι → ℂ := Sum.elim (fun _ => 1) fun _ => -1
  have hfib : ∀ i x, q (h i x) = q x := by
    rintro (a | u) x
    · exact hqconj a x
    · exact hqτ x
  have hloc : ∀ (y : Fin (n + 1) → F.Carrier)
      (T : Distribution (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier)),
      (∀ f : SchwartzBruhat (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier),
        (∀ x, q x = y → f x = 0) → T f = 0) →
      (∀ i, pushforward (h i) T = χ i • T) → T = 0 := by
    intro y T hT hTi
    have hTconj : IsConjugationInvariant T := fun a => by
      simpa [h, χ] using hTi (Sum.inl a)
    have hTτ : pushforward τ T = -T := by
      simpa [h, χ] using hTi (Sum.inr ())
    -- The fibre is a closed finite union of conjugacy classes.
    obtain ⟨s, hs⟩ : ∃ s : Finset (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier),
        q ⁻¹' {y} = ⋃ x ∈ s, {g | ∃ a, a * x * a⁻¹ = g} := by
      by_cases hne : ∃ g₀, q g₀ = y
      · obtain ⟨g₀, hg₀⟩ := hne
        obtain ⟨s₀, hs₀⟩ := h5 F.Carrier (n + 1)
          (g₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier).charpoly
        refine ⟨(s₀.preimage (fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier =>
          (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) Units.val_injective.injOn).filter
            (fun g => q g = y), ?_⟩
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
          Finset.mem_filter, exists_prop]
        constructor
        · intro hg
          have hc : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier).charpoly =
              (g₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier).charpoly :=
            charpoly_eq_of_coeff_eq _ _ fun i => by
              have := congrFun (hg.trans hg₀.symm) i
              simpa only [hq, charpolyCoeffs] using this
          obtain ⟨y', hy's, k, hk⟩ := hs₀ _ hc
          refine ⟨k * g * k⁻¹, ⟨?_, ?_⟩, k⁻¹, ?_⟩
          · rw [Finset.mem_preimage, Units.val_mul, Units.val_mul, hk]
            exact hy's
          · rw [hqconj, hg]
          · group
        · rintro ⟨x, ⟨-, hx⟩, a, rfl⟩
          rw [hqconj, hx]
      · refine ⟨∅, ?_⟩
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.notMem_empty,
          Set.iUnion_of_empty, Set.iUnion_empty, Set.mem_empty_iff_false, iff_false]
        exact fun hg => hne ⟨g, hg⟩
    refine conjugationInvariant_finiteOrbit_vanishing h3 τ (q ⁻¹' {y}) s
      ((isClosed_singleton).preimage (continuous_charpolyCoeffs (n + 1))) hs
      (fun z _ => ⟨hτconj z, by rw [hτsymm]; exact hτconj z⟩) T
      (fun f hf => hT f fun x hx => hf x hx) hTconj hTτ
  have hD'i : ∀ i, pushforward (h i) D' = χ i • D' := by
    rintro (a | u)
    · simpa [h, χ] using hD'conj a
    · simpa [h, χ] using hD'τ
  have hD'0 : D' = 0 :=
    h1 (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) (Fin (n + 1) → F.Carrier) q
      (continuous_charpolyCoeffs (n + 1)) ι h χ hfib hloc D' hD'i
  have : D - pushforward τ D = 0 := hD'0
  exact (sub_eq_zero.mp this).symm

end Langlands.HarmonicAnalysis.Distribution

namespace Langlands

universe uF

/-- Bernstein–Zelevinsky (1976), §7.3: a conjugation-invariant distribution on
`GL_n(F)` is invariant under transposition. -/
theorem generalLinearConjugationDistributionTranspose :
    GeneralLinearConjugationDistributionTransposeStatement.{uF} :=
  HarmonicAnalysis.Distribution.generalLinearConjugationDistributionTranspose_of_prerequisites
    HarmonicAnalysis.Distribution.equivariantLocalization
    HarmonicAnalysis.Distribution.finiteOrbitAntiInvariantVanishing
    matrixTransposeConjugate matrixCharpolyFiniteConjugacy

end Langlands
