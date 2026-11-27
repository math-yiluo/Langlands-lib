import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.BaseChange.TwistedLocalDescent.Classification
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.TwistedCharacter.Saturation
import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Windows around the Levi representatives

Small open windows `Ω' j ∋ d j` in `M(E)` on which the characteristic polynomials of the norms
of the blocks stay coprime across different blocks and separate different Levi classes. See the
paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear Langlands.JacquetLanglands Langlands.HarmonicAnalysis.Distribution
open _root_.Polynomial Set

universe u v

section Coefficients

variable {E : Type v} [Field E]

theorem charpoly_coeff_eq_zero_of_lt {r t : ℕ} (g : GeneralLinear r E) (ht : r < t) :
    g.val.charpoly.coeff t = 0 := by
  have hd : g.val.charpoly.natDegree < t := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact ht
  exact coeff_eq_zero_of_natDegree_lt hd

theorem charpoly_coeff_dim {r : ℕ} (g : GeneralLinear r E) : g.val.charpoly.coeff r = 1 := by
  have := (Matrix.charpoly_monic g.val).coeff_natDegree
  rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this

end Coefficients

section Continuity

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type v} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [Algebra F E]
  [IsModuleTopology F E] (σ : E ≃ₐ[F] E)

/-- Coefficients of characteristic polynomials depend continuously on the element. -/
theorem continuous_charpoly_coeff (r t : ℕ) :
    Continuous (fun g : GeneralLinear r E => g.val.charpoly.coeff t) := by
  rcases lt_trichotomy t r with h | rfl | h
  · exact (continuous_apply (⟨t, h⟩ : Fin r)).comp (continuous_charpolyCoeffs (K := E) r)
  · exact (continuous_const : Continuous fun _ : GeneralLinear t E => (1 : E)).congr
      fun g => (charpoly_coeff_dim g).symm
  · exact (continuous_const : Continuous fun _ : GeneralLinear r E => (0 : E)).congr
      fun g => (charpoly_coeff_eq_zero_of_lt g h).symm

/-- The Sylvester matrix of two continuously varying polynomials varies continuously. -/
theorem continuous_resultant {X : Type*} [TopologicalSpace X] (f g : X → E[X]) (m k : ℕ)
    (hf : ∀ t, Continuous fun x => (f x).coeff t) (hg : ∀ t, Continuous fun x => (g x).coeff t) :
    Continuous (fun x => resultant (f x) (g x) m k) := by
  unfold resultant
  apply Continuous.matrix_det
  refine continuous_pi fun a => continuous_pi fun b => ?_
  refine Fin.addCases (fun b₁ => ?_) (fun b₁ => ?_) b
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · exact continuous_const
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · exact continuous_const

end Continuity

section Windows

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) (l : ℕ)
  {n : ℕ} (B : BlockShape n)

/-- The characteristic polynomial of the norm of the `i`-th block. -/
def normCharpoly (x : B.Levi E) (i : Fin B.length) : E[X] :=
  (cyclicNorm σ l (x i)).val.charpoly

theorem normCharpoly_twistedConj (hσ : σ ^ l = 1) (y x : B.Levi E) (i : Fin B.length) :
    normCharpoly σ l B (y * x * (leviAut σ B y)⁻¹) i = normCharpoly σ l B x i := by
  unfold normCharpoly
  have h : (y * x * (leviAut σ B y)⁻¹) i =
      (y i)⁻¹⁻¹ * x i * entrywiseAut σ (B.size i) (y i)⁻¹ := by
    simp only [Pi.mul_apply, Pi.inv_apply, leviAut_apply, inv_inv, map_inv]
  rw [h, cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, charpoly_conj]

/-- The coefficient vector of the norm characteristic polynomials. -/
def normCoeffs (x : B.Levi E) : ∀ i : Fin B.length, Fin (B.size i) → E :=
  fun i => charpolyCoeffs (B.size i) (cyclicNorm σ l (x i))

theorem normCharpoly_eq_of_normCoeffs_eq {x x' : B.Levi E} (h : normCoeffs σ l B x =
    normCoeffs σ l B x') (i : Fin B.length) : normCharpoly σ l B x i = normCharpoly σ l B x' i := by
  have hi := congrFun h i
  unfold normCharpoly
  apply Polynomial.ext
  intro t
  rcases lt_trichotomy t (B.size i) with ht | rfl | ht
  · exact congrFun hi ⟨t, ht⟩
  · rw [charpoly_coeff_dim, charpoly_coeff_dim]
  · rw [charpoly_coeff_eq_zero_of_lt _ ht, charpoly_coeff_eq_zero_of_lt _ ht]

theorem normCoeffs_twistedConj (hσ : σ ^ l = 1) (y x : B.Levi E) :
    normCoeffs σ l B (y * x * (leviAut σ B y)⁻¹) = normCoeffs σ l B x := by
  funext i t
  have h := normCharpoly_twistedConj σ l B hσ y x i
  exact congrArg (fun p => p.coeff t) h

/-- Coprimality of characteristic polynomials of the norms of two blocks, through the
resultant. -/
theorem isCoprime_normCharpoly_iff (x x' : B.Levi E) (i k : Fin B.length) :
    IsCoprime (normCharpoly σ l B x' k) (normCharpoly σ l B x i) ↔
      resultant (normCharpoly σ l B x' k) (normCharpoly σ l B x i) (B.size k) (B.size i) ≠ 0 := by
  have hk : (normCharpoly σ l B x' k).natDegree = B.size k := by
    rw [normCharpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hi : (normCharpoly σ l B x i).natDegree = B.size i := by
    rw [normCharpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [← hk, ← hi, Ne, resultant_eq_zero_iff]
  have hne : normCharpoly σ l B x' k ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  simp [hne]

variable [TopologicalSpace F] [IsTopologicalRing F] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] [T2Space E]

theorem continuous_normCoeffs : Continuous (normCoeffs σ l B) :=
  continuous_pi fun i => (continuous_charpolyCoeffs (B.size i)).comp
    ((SigmaLiftCharacterIdentity.continuous_cyclicNorm (n := B.size i) σ l).comp (continuous_apply i))

theorem continuous_normCharpoly_coeff (i : Fin B.length) (t : ℕ) :
    Continuous (fun x : B.Levi E => (normCharpoly σ l B x i).coeff t) :=
  (continuous_charpoly_coeff (B.size i) t).comp
    ((SigmaLiftCharacterIdentity.continuous_cyclicNorm (n := B.size i) σ l).comp (continuous_apply i))

theorem isOpen_coprime (i k : Fin B.length) :
    IsOpen {xx : B.Levi E × B.Levi E |
      IsCoprime (normCharpoly σ l B xx.2 k) (normCharpoly σ l B xx.1 i)} := by
  simp_rw [isCoprime_normCharpoly_iff]
  exact isOpen_ne_fun (continuous_resultant _ _ _ _
    (fun t => (continuous_normCharpoly_coeff σ l B k t).comp continuous_snd)
    (fun t => (continuous_normCharpoly_coeff σ l B i t).comp continuous_fst)) continuous_const

end Windows

section Existence

theorem isCoprime_charpoly_of_regular {K : Type u} [Field K] {n : ℕ} (B : BlockShape n)
    {m : B.Levi K} (hm : IsRegularSemisimple (B.leviEmbedding K m)) {i k : Fin B.length}
    (hik : i ≠ k) : IsCoprime (m i).val.charpoly (m k).val.charpoly := by
  classical
  apply Polynomial.Separable.isCoprime
  apply Polynomial.Separable.of_dvd hm
  rw [charpoly_leviEmbedding, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_dvd_mul_left _ (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hik.symm,
    Finset.mem_univ k⟩))

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) {l : ℕ}
  {n : ℕ} (B : BlockShape n)
  [TopologicalSpace F] [IsTopologicalRing F] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] [T2Space E]

/-- **Windows.** Around the Levi representatives `d j` there are open windows inside given
windows `Ω j` such that the characteristic polynomials of the norms of different blocks, at any
two points of the same window, are coprime, and which have different norm characteristic
polynomials for different `j`. -/
theorem exists_windows {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) {k : ℕ}
    {m : Fin k → B.Levi F} (hm : IsLeviClassSystem B γ m) {d : Fin k → B.Levi E}
    (hd : ∀ j i, cyclicNorm σ l (d j i) = baseChange F E (B.size i) (m j i))
    (Ω : Fin k → Set (B.Levi E)) (hΩ : ∀ j, IsOpen (Ω j)) (hdΩ : ∀ j, d j ∈ Ω j) :
    ∃ Ω' : Fin k → Set (B.Levi E), (∀ j, IsOpen (Ω' j)) ∧ (∀ j, d j ∈ Ω' j) ∧
      (∀ j, Ω' j ⊆ Ω j) ∧
      (∀ j, ∀ x ∈ Ω' j, ∀ x' ∈ Ω' j, ∀ i i', i ≠ i' →
        IsCoprime (normCharpoly σ l B x' i') (normCharpoly σ l B x i)) ∧
      (∀ j j', j ≠ j' → ∀ x ∈ Ω' j, ∀ x' ∈ Ω' j', normCoeffs σ l B x ≠ normCoeffs σ l B x') := by
  classical
  -- Regularity of the Levi representatives.
  have hreg : ∀ j, IsRegularSemisimple (B.leviEmbedding F (m j)) := fun j => by
    obtain ⟨x, hx⟩ := hm.1 j
    rw [← hx]
    exact isRegularSemisimple_conj hγ x
  have hnc : ∀ j i, normCharpoly σ l B (d j) i = ((m j i).val.charpoly).map (algebraMap F E) :=
    fun j i => by rw [normCharpoly, hd, charpoly_baseChange]
  -- Coprimality on a product neighbourhood.
  let C : Set (B.Levi E × B.Levi E) := ⋂ i : Fin B.length, ⋂ i' : Fin B.length,
    {xx | i ≠ i' → IsCoprime (normCharpoly σ l B xx.2 i') (normCharpoly σ l B xx.1 i)}
  have hC : IsOpen C := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun i' => ?_
    by_cases h : i = i'
    · simp [h]
    · simpa [h] using isOpen_coprime σ l B i i'
  have hdC : ∀ j, (d j, d j) ∈ C := by
    intro j
    simp only [C, Set.mem_iInter, Set.mem_ofPred_eq]
    intro i i' hii'
    rw [hnc, hnc]
    have h := (isCoprime_charpoly_of_regular B (hreg j) hii'.symm).map
      (Polynomial.mapRingHom (algebraMap F E))
    exact h
  choose U V hU hV hdU hdV hUV using fun j => isOpen_prod_iff.mp hC (d j) (d j) (hdC j)
  -- Separation of the norm coefficients.
  have hsep : ∀ j j', j ≠ j' → normCoeffs σ l B (d j) ≠ normCoeffs σ l B (d j') := by
    intro j j' hjj' heq
    apply hjj'
    apply hm.2.1 j j'
    have hblock : ∀ i, ∃ y : GeneralLinear (B.size i) F, y⁻¹ * m j i * y = m j' i := by
      intro i
      have hcp : (m j' i).val.charpoly = (m j i).val.charpoly := by
        have h := normCharpoly_eq_of_normCoeffs_eq σ l B heq i
        rw [hnc, hnc] at h
        exact (Polynomial.map_injective _ (algebraMap F E).injective h).symm
      obtain ⟨z, hz⟩ := exists_matrix_conj_of_charpoly_eq_of_separable (m j i).val (m j' i).val
        (isRegularSemisimple_block B (hreg j) i) hcp
      refine ⟨z⁻¹, Units.ext ?_⟩
      rw [inv_inv]
      exact hz
    choose y hy using hblock
    exact ⟨y, funext hy⟩
  have hsep' : ∀ j j' (h : j ≠ j'), ∃ A A' : Set (∀ i : Fin B.length, Fin (B.size i) → E),
      IsOpen A ∧ IsOpen A' ∧ normCoeffs σ l B (d j) ∈ A ∧ normCoeffs σ l B (d j') ∈ A' ∧
        Disjoint A A' := fun j j' h => t2_separation (hsep j j' h)
  choose A A' hA hA' hdA hdA' hAA' using hsep'
  let Wj : Fin k → Set (∀ i : Fin B.length, Fin (B.size i) → E) := fun j =>
    ⋂ j' : Fin k, ⋂ (h : j ≠ j'), A j j' h ∩ A' j' j h.symm
  have hW : ∀ j, IsOpen (Wj j) := fun j =>
    isOpen_iInter_of_finite fun j' => isOpen_iInter_of_finite fun h => (hA j j' h).inter
      (hA' j' j h.symm)
  have hdW : ∀ j, normCoeffs σ l B (d j) ∈ Wj j := by
    intro j
    simp only [Wj, Set.mem_iInter, Set.mem_inter_iff]
    exact fun j' h => ⟨hdA j j' h, hdA' j' j h.symm⟩
  refine ⟨fun j => Ω j ∩ (U j ∩ V j) ∩ normCoeffs σ l B ⁻¹' Wj j, fun j => ?_, fun j => ?_,
    fun j => ?_, ?_, ?_⟩
  · exact ((hΩ j).inter ((hU j).inter (hV j))).inter
      ((hW j).preimage (continuous_normCoeffs σ l B))
  · exact ⟨⟨hdΩ j, hdU j, hdV j⟩, hdW j⟩
  · exact fun x hx => hx.1.1
  · intro j x hx x' hx' i i' hii'
    have hmem : (x, x') ∈ C := hUV j ⟨hx.1.2.1, hx'.1.2.2⟩
    simp only [C, Set.mem_iInter, Set.mem_ofPred_eq] at hmem
    exact hmem i i' hii'
  · intro j j' hjj' x hx x' hx' heq
    have h1 : normCoeffs σ l B x ∈ A j j' hjj' := by
      have := hx.2
      simp only [Wj, Set.mem_preimage, Set.mem_iInter, Set.mem_inter_iff] at this
      exact (this j' hjj').1
    have h2 : normCoeffs σ l B x' ∈ A' j j' hjj' := by
      have := hx'.2
      simp only [Wj, Set.mem_preimage, Set.mem_iInter, Set.mem_inter_iff] at this
      exact (this j hjj'.symm).2
    rw [heq] at h1
    exact Set.disjoint_left.mp (hAA' j j' hjj') h1 h2

end Existence

end Langlands.BaseChange.TwistedLocalDescent
