import Langlands.Geometry.Building.AffineSimpleDerivativeBase
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Logic.Equiv.Option

/-! # Cartan extensions from deleted simple-gradient bases -/

noncomputable section

universe uV uA uI

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

/-- The integer pairing on full derivative roots agrees with the chamber
Cartan entry when the derivatives come from simple affine roots. -/
theorem rationalDerivativePairing_pairingIn_simple {C : Set A}
    (ψ η : simpleAffineRoots Ψ C) :
    hΨ.rationalDerivativePairing.pairingIn ℤ
      ⟨(ψ : A →ᵃ[ℝ] ℝ).linear, linear_mem_derivativeRoots ψ.2.1.1⟩
      ⟨(η : A →ᵃ[ℝ] ℝ).linear, linear_mem_derivativeRoots η.2.1.1⟩ =
      chamberCartanMatrix Ψ C ψ η := by
  let a : derivativeRoots Ψ :=
    ⟨(ψ : A →ᵃ[ℝ] ℝ).linear, linear_mem_derivativeRoots ψ.2.1.1⟩
  let b : derivativeRoots Ψ :=
    ⟨(η : A →ᵃ[ℝ] ℝ).linear, linear_mem_derivativeRoots η.2.1.1⟩
  have hcor : hΨ.derivativeCoroot b = corootVector Ψ (η : A →ᵃ[ℝ] ℝ) :=
    hΨ.coroot_eq_of_linear_eq (hΨ.isCoroot_derivativeCoroot b)
      (hΨ.isCoroot_corootVector_of_mem η.2.1.1)
      (hΨ.linear_derivativeRootLift b).symm
  have hq : algebraMap ℚ ℝ
      (algebraMap ℤ ℚ (hΨ.rationalDerivativePairing.pairingIn ℤ a b)) =
        (chamberCartanMatrix Ψ C ψ η : ℝ) := by
    rw [RootPairing.algebraMap_pairingIn,
      hΨ.rationalDerivativePairing_pairing, hcor, hΨ.cast_chamberCartanMatrix]
  change (((hΨ.rationalDerivativePairing.pairingIn ℤ a b : ℤ) : ℚ) : ℝ) =
    (chamberCartanMatrix Ψ C ψ η : ℝ) at hq
  exact_mod_cast hq

/-- A deleted independent simple-gradient family is equivalent to the support
of a full derivative base with that exact support image. -/
def deletedSimpleRootDerivativeEquiv (C : Set A)
    (δ : simpleAffineRoots Ψ C)
    (hdel : IsIntegralSimpleDerivativeDeletion Ψ C δ)
    (B : hΨ.rationalDerivativePairing.Base)
    (hB : (B.support : Set (derivativeRoots Ψ)) =
      Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
        (⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
          linear_mem_derivativeRoots η.val.2.1.1⟩ : derivativeRoots Ψ))) :
    {η : simpleAffineRoots Ψ C // η ≠ δ} ≃ B.support := by
  classical
  let f : {η : simpleAffineRoots Ψ C // η ≠ δ} → B.support :=
    fun η => ⟨⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
      linear_mem_derivativeRoots η.val.2.1.1⟩, by
        change _ ∈ (B.support : Set (derivativeRoots Ψ))
        rw [hB]
        exact ⟨η, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro η ψ h
    apply hdel.1.injective
    exact congrArg (fun x : B.support => x.val.val) h
  · intro a
    have ha : a.val ∈ Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
        (⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
          linear_mem_derivativeRoots η.val.2.1.1⟩ : derivativeRoots Ψ)) := by
      rw [← hB]
      exact a.property
    obtain ⟨η, hη⟩ := ha
    exact ⟨η, Subtype.ext hη⟩

@[simp] theorem deletedSimpleRootDerivativeEquiv_val (C : Set A)
    (δ : simpleAffineRoots Ψ C)
    (hdel : IsIntegralSimpleDerivativeDeletion Ψ C δ)
    (B : hΨ.rationalDerivativePairing.Base)
    (hB : (B.support : Set (derivativeRoots Ψ)) =
      Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
        (⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
          linear_mem_derivativeRoots η.val.2.1.1⟩ : derivativeRoots Ψ)))
    (η : {η : simpleAffineRoots Ψ C // η ≠ δ}) :
    (hΨ.deletedSimpleRootDerivativeEquiv C δ hdel B hB η).val =
      ⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
        linear_mem_derivativeRoots η.val.2.1.1⟩ := rfl

/-- The base Cartan matrix is the undeleted principal submatrix of the
affine chamber matrix, through the actual gradient equivalence. -/
theorem cartanMatrix_deletedSimpleRootDerivativeEquiv (C : Set A)
    (δ : simpleAffineRoots Ψ C)
    (hdel : IsIntegralSimpleDerivativeDeletion Ψ C δ)
    (B : hΨ.rationalDerivativePairing.Base)
    (hB : (B.support : Set (derivativeRoots Ψ)) =
      Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
        (⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
          linear_mem_derivativeRoots η.val.2.1.1⟩ : derivativeRoots Ψ)))
    (η ψ : {η : simpleAffineRoots Ψ C // η ≠ δ}) :
    B.cartanMatrix (hΨ.deletedSimpleRootDerivativeEquiv C δ hdel B hB η)
      (hΨ.deletedSimpleRootDerivativeEquiv C δ hdel B hB ψ) =
      chamberCartanMatrix Ψ C η.val ψ.val := by
  exact hΨ.rationalDerivativePairing_pairingIn_simple η.val ψ.val

/-- A Cartan identification with a deleted full derivative base transports
the actual chamber matrix to a vertex-transitive affine extension. -/
theorem exists_transitive_cartanExtension_of_simpleDerivativeBase
    {c : A} (hc : IsRegular Ψ c)
    (δ : simpleAffineRoots Ψ (facet Ψ c))
    (hdel : IsIntegralSimpleDerivativeDeletion Ψ (facet Ψ c) δ)
    (B : hΨ.rationalDerivativePairing.Base)
    (hB : (B.support : Set (derivativeRoots Ψ)) =
      Set.range (fun η : {η : simpleAffineRoots Ψ (facet Ψ c) // η ≠ δ} =>
        (⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
          linear_mem_derivativeRoots η.val.2.1.1⟩ : derivativeRoots Ψ)))
    (htrans : Langlands.GroupScheme.AffineCartan.IsVertexTransitive
      (chamberCartanMatrix Ψ (facet Ψ c)))
    {I : Type uI} [Fintype I] (M : Matrix I I ℤ)
    (e : I ≃ B.support)
    (he : ∀ i j, B.cartanMatrix (e i) (e j) = M i j) :
    ∃ N : Matrix (Option I) (Option I) ℤ,
      (∀ i j, N (some i) (some j) = M i j) ∧
      (∀ i, N i i = 2) ∧
      (∀ i j, i ≠ j → N i j ≤ 0) ∧
      (∀ i j, N i j = 0 ↔ N j i = 0) ∧
      (∃ m : Option I → ℤ, (∀ i, 0 < m i) ∧ Matrix.vecMul m N = 0) ∧
      Langlands.GroupScheme.AffineCartan.IsVertexTransitive N := by
  classical
  let := (finite_simpleAffineRoots hΨ hc).fintype
  let d := hΨ.deletedSimpleRootDerivativeEquiv (facet Ψ c) δ hdel B hB
  let f : Option I ≃ simpleAffineRoots Ψ (facet Ψ c) :=
    (e.trans d.symm).optionCongr.trans (Equiv.optionSubtypeNe δ)
  let Q := chamberCartanMatrix Ψ (facet Ψ c)
  refine ⟨Q.submatrix f f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change Q (d.symm (e i)).val (d.symm (e j)).val = M i j
    have h := hΨ.cartanMatrix_deletedSimpleRootDerivativeEquiv
      (facet Ψ c) δ hdel B hB (d.symm (e i)) (d.symm (e j))
    change B.cartanMatrix (d (d.symm (e i))) (d (d.symm (e j))) = _ at h
    rw [d.apply_symm_apply, d.apply_symm_apply] at h
    exact h.symm.trans (he i j)
  · intro i
    exact hΨ.chamberCartanMatrix_self (f i)
  · intro i j hij
    exact hΨ.chamberCartanMatrix_nonpos hc (fun h => hij (f.injective h))
  · intro i j
    exact hΨ.chamberCartanMatrix_eq_zero_iff (f i) (f j)
  · obtain ⟨m, hm, hker⟩ := hΨ.exists_pos_vecMul_chamberCartanMatrix_eq_zero hc
    refine ⟨m ∘ f, fun i => hm (f i), ?_⟩
    rw [Matrix.submatrix_vecMul_equiv]
    simp only [Function.comp_assoc, f.self_comp_symm, Function.comp_id]
    funext i
    exact congrFun hker (f i)
  · intro i j
    obtain ⟨σ, hσ, hσij⟩ := htrans (f i) (f j)
    refine ⟨f.trans (σ.trans f.symm), ?_, ?_⟩
    · intro k l
      change Q (f (f.symm (σ (f k)))) (f (f.symm (σ (f l)))) = Q (f k) (f l)
      simpa only [f.apply_symm_apply] using hσ (f k) (f l)
    · change f.symm (σ (f i)) = j
      rw [hσij, f.symm_apply_apply]

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
