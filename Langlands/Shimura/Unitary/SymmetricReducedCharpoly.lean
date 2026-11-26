import Langlands.Shimura.Unitary.HermitianCoordinates
import Langlands.Algebra.ReducedCharpoly
import Mathlib.Algebra.Polynomial.Lifts

/-! # The reduced characteristic polynomial of a symmetric element -/

noncomputable section

universe u v w x y

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra _root_.Polynomial Langlands.CentralSimple
open scoped TensorProduct

section Chart

variable {E : Type u} {S : Type x} {K : Type v} {L : Type y} {A : Type w}
  [CommRing E] [CommRing S] [Field K] [Field L] [Ring A]
  [Algebra E S] [Algebra E A] [Algebra S L] [Algebra K L] [Algebra K A]
  {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- A surjective matrix chart over an extended base that acts on the original
center through the specified map to `L` identifies the `L`-extension of the algebra. -/
def matrixChartOfCenterCompatible [FiniteDimensional K A]
    (hdim : Module.finrank K A = n ^ 2)
    (e : S ⊗[E] A →ₐ[S] Matrix (Fin n) (Fin n) L) (hsurj : Function.Surjective e)
    (hcenter : ∀ k : K, e (1 ⊗ₜ[E] algebraMap K A k) =
      algebraMap L (Matrix (Fin n) (Fin n) L) (algebraMap K L k)) :
    {f : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L //
      ∀ a : A, f (1 ⊗ₜ[K] a) = e (1 ⊗ₜ[E] a)} := by
  let M := Matrix (Fin n) (Fin n) L
  let g : A →ₐ[K] M :=
    { toRingHom := e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := E) (A := S)).toRingHom
      commutes' := hcenter }
  let f : L ⊗[K] A →ₐ[L] M :=
    Algebra.TensorProduct.lift (Algebra.ofId L M) g (fun z a => Algebra.commutes z (g a))
  have hf (z : L) (a : A) : f (z ⊗ₜ[K] a) = algebraMap L M z * e (1 ⊗ₜ[E] a) := rfl
  have hsurj' : Function.Surjective f := by
    intro Y
    obtain ⟨t, rfl⟩ := hsurj Y
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' =>
      obtain ⟨z, hz⟩ := ht
      obtain ⟨z', hz'⟩ := ht'
      exact ⟨z + z', by rw [map_add, hz, hz', map_add]⟩
    | tmul s a =>
      refine ⟨(algebraMap S L s) ⊗ₜ[K] a, ?_⟩
      rw [hf, show s ⊗ₜ[E] a = algebraMap S (S ⊗[E] A) s * (1 ⊗ₜ[E] a) by
        change s ⊗ₜ[E] a = (s ⊗ₜ[E] (1 : A)) * (1 ⊗ₜ[E] a)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, e.commutes]
      rfl
  have hdim' : Module.finrank L (L ⊗[K] A) = Module.finrank L M := by
    rw [Module.finrank_baseChange, hdim, Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one, pow_two]
  let f' := AlgEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim').mpr hsurj', hsurj'⟩
  refine ⟨f', fun a => ?_⟩
  change f (1 ⊗ₜ[K] a) = _
  rw [hf, map_one, one_mul]

end Chart

variable {E : Type u} {K A : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] {n : ℕ}

/-- The characteristic polynomial in the actual real matrix chart is the
coefficient extension of the reduced characteristic polynomial. -/
theorem reducedCharpoly_map_realHermitianChart
    (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n) (τ : E →+* ℝ) (a : A) :
    letI : Algebra E ℝ := τ.toAlgebra
    (reducedCharpoly K A a).map (embeddingOverReal τ) =
      ((realHermitianChart D hn τ).equiv (1 ⊗ₜ[E] a)).charpoly := by
  let : Algebra E ℝ := τ.toAlgebra
  let : Algebra K ℂ := (embeddingOverReal τ : K →+* ℂ).toAlgebra
  let G := realHermitianChart D hn τ
  let C := realCenterEquiv (K := K) τ
  have hcenter (k : K) : G.equiv (1 ⊗ₜ[E] algebraMap K A k) =
      algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (algebraMap K ℂ k) := by
    let z : ℝ ⊗[E] K := 1 ⊗ₜ[E] k
    have h := G.center_eq (C z)
    change G.equiv (realCenterInclusion τ (C.symm (C z))) = Matrix.scalar (Fin n) (C z) at h
    rw [C.symm_apply_apply] at h
    simp only [z, realCenterInclusion_tmul, C, realCenterEquiv_tmul, Complex.ofReal_one, one_mul] at h
    exact h
  let f := matrixChartOfCenterCompatible D.dimension G.equiv.toAlgHom G.equiv.surjective hcenter
  have hdim : reducedDegree K A = n := by
    change Nat.sqrt (Module.finrank K A) = n
    rw [D.dimension, pow_two, Nat.sqrt_eq]
  let e := f.val.trans (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hdim.symm))
  change (reducedCharpoly K A a).map (algebraMap K ℂ) = (G.equiv (1 ⊗ₜ[E] a)).charpoly
  rw [reducedCharpoly_map_chart K A e]
  simp only [e, AlgEquiv.trans_apply, Matrix.coe_reindexAlgEquiv, Matrix.charpoly_reindex]
  exact congrArg Matrix.charpoly (f.property a)

private theorem reducedCharpoly_map_cmConjugation_of_symmetric
    (D : CentralSimpleUnitaryData E K A n) {a : A} (ha : D.involution a = a) :
    (reducedCharpoly K A a).map (cmConjugation E K).toRingHom = reducedCharpoly K A a := by
  let τ : E →+* ℝ :=
    (IsTotallyReal.complexEmbedding_isReal (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom).embedding
  let : Algebra E ℝ := τ.toAlgebra
  let φ : K →+* ℂ := embeddingOverReal τ
  let M := Matrix (Fin n) (Fin n) ℂ
  have hn : 0 < n := by have := D.rank_gt_one; omega
  let G := realHermitianChart D hn τ
  let X : M := G.equiv (1 ⊗ₜ[E] a)
  have h := G.adjoint_eq (1 ⊗ₜ[E] a)
  change G.equiv ((1 : ℝ) ⊗ₜ[E] D.involution a) = _ at h
  rw [ha] at h
  change X = (↑G.gram⁻¹ : M) *
    matrixTranspose (AlgebraInvolution.ofStar (R := ℝ) (A := ℂ)) n X * G.gram at h
  have hθ : matrixTranspose (AlgebraInvolution.ofStar (R := ℝ) (A := ℂ)) n X =
      (X.map (starRingEnd ℂ)).transpose := rfl
  have hchar := congrArg Matrix.charpoly h
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.charpoly_units_conj', hθ,
    Matrix.charpoly_transpose, Matrix.charpoly_map] at hchar
  have hφ : φ.comp (cmConjugation E K).toRingHom = (starRingEnd ℂ).comp φ := by
    ext k
    exact embedding_cmConjugation E K φ k
  apply Polynomial.map_injective φ φ.injective
  rw [Polynomial.map_map, hφ, ← Polynomial.map_map, reducedCharpoly_map_realHermitianChart D hn τ]
  exact hchar.symm

private theorem exists_algebraMap_of_cmConjugation_fixed {k : K} (h : cmConjugation E K k = k) :
    ∃ e : E, algebraMap E K e = k := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed k).mpr
  have hcard : Nat.card (K ≃ₐ[E] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, IsQuadraticExtension.finrank_eq_two]
  obtain ⟨g, -, hg⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[E] K)).mp hcard
  intro σ
  by_cases hσ : σ = 1
  · rw [hσ]
    rfl
  · rw [(hg σ hσ).trans (hg _ (cmConjugation_ne_one E K)).symm]
    exact h

private theorem exists_reducedCharpoly_descent (D : CentralSimpleUnitaryData E K A n)
    {a : A} (ha : D.involution a = a) :
    ∃ f : E[X], f.map (algebraMap E K) = reducedCharpoly K A a := by
  let p := reducedCharpoly K A a
  have hp := reducedCharpoly_map_cmConjugation_of_symmetric D ha
  apply (Polynomial.mem_lifts p).mp
  apply (Polynomial.lifts_iff_coeff_lifts p).mpr
  intro i
  apply exists_algebraMap_of_cmConjugation_fixed
  have h := congrArg (fun q : K[X] => q.coeff i) hp
  rw [Polynomial.coeff_map] at h
  exact h

/-- The reduced characteristic polynomial of a symmetric element has a
unique coefficient descent to the specified real number field. -/
def symmetricReducedCharpoly (D : CentralSimpleUnitaryData E K A n) {a : A}
    (ha : D.involution a = a) :
    {f : E[X] // f.map (algebraMap E K) = reducedCharpoly K A a} :=
  ⟨(exists_reducedCharpoly_descent D ha).choose, (exists_reducedCharpoly_descent D ha).choose_spec⟩

theorem symmetricReducedCharpoly_unique (D : CentralSimpleUnitaryData E K A n) {a : A}
    (ha : D.involution a = a) (f : E[X])
    (hf : f.map (algebraMap E K) = reducedCharpoly K A a) :
    f = (symmetricReducedCharpoly D ha).val :=
  Polynomial.map_injective (algebraMap E K) (algebraMap E K).injective
    (hf.trans (symmetricReducedCharpoly D ha).property.symm)

theorem symmetricReducedCharpoly_monic (D : CentralSimpleUnitaryData E K A n) {a : A}
    (ha : D.involution a = a) : (symmetricReducedCharpoly D ha).val.Monic := by
  apply Polynomial.monic_of_injective (algebraMap E K).injective
  rw [(symmetricReducedCharpoly D ha).property]
  exact reducedCharpoly_monic K A a

theorem symmetricReducedCharpoly_natDegree (D : CentralSimpleUnitaryData E K A n) {a : A}
    (ha : D.involution a = a) : (symmetricReducedCharpoly D ha).val.natDegree = n := by
  rw [← (symmetricReducedCharpoly_monic D ha).natDegree_map (algebraMap E K),
    (symmetricReducedCharpoly D ha).property, reducedCharpoly_natDegree]
  change Nat.sqrt (Module.finrank K A) = n
  rw [D.dimension, pow_two, Nat.sqrt_eq]

end Langlands.Shimura.FiniteUnitary
