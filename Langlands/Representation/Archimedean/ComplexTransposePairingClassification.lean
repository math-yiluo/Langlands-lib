import Langlands.Representation.Archimedean.ComplexTransposeStandardDuality

/-! # A matched-head criterion for the complex transpose pairing -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uV

open scoped TensorProduct Matrix

namespace Langlands.Archimedean.ComplexTransposePairingClassification

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean KFiniteDual ComplexTransposeStandardDuality

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ds : List ComplexCharacterData}

/-- Transposing an embedding into the opposite-order standard module along the actual
inverse-transpose standard duality. -/
def standardAdjointOfEmbedding (hn : ds.length = n) (J : V →ₗ[ℂ] Standard n ds.reverse) :
    Standard n ds →ₗ[ℂ] Module.Dual ℂ V :=
  (((kDual (complexStandardRep n ds)).subtype.comp
      (transposeDualEquiv n ds hn).toLinearMap).comp J).flip

@[simp]
lemma standardAdjointOfEmbedding_apply (hn : ds.length = n)
    (J : V →ₗ[ℂ] Standard n ds.reverse) (f : Standard n ds) (v : V) :
    standardAdjointOfEmbedding hn J f v =
      (transposeDualEquiv n ds hn (J v) : Module.Dual ℂ (Standard n ds)) f := rfl

section Embedding

variable (hn : ds.length = n) (J : V →ₗ[ℂ] Standard n ds.reverse)
  (hJK : ∀ k v, J (ρ k v) = complexStandardRep n ds.reverse k (J v))
  (hJL : ∀ X v, J (π X v) = complexStandardLie n ds.reverse X (J v))

include hJK in
lemma standardAdjoint_rep (k : Matrix.unitaryGroup (Fin n) ℂ) (f : Standard n ds) :
    standardAdjointOfEmbedding hn J (complexStandardRep n ds k f) =
      ρ.dual (compactIota ℂ n k) (standardAdjointOfEmbedding hn J f) := by
  ext v
  rw [dual_apply_apply, ← (compactIota ℂ n).map_inv k]
  simp only [standardAdjointOfEmbedding_apply, hJK]
  have h := congrArg (fun w : kDual (complexStandardRep n ds) =>
      (w : Module.Dual ℂ (Standard n ds)) f)
    (transposeDualEquiv_rep ds hn (compactIota ℂ n k⁻¹) (J v))
  simp only [compactIota_involutive, coe_kDualRep_apply, dual_apply_apply, inv_inv] at h
  exact h.symm

include hJL in
lemma standardAdjoint_lie (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (f : Standard n ds) (v : V) :
    standardAdjointOfEmbedding hn J (complexStandardLie n ds X f) v =
      -standardAdjointOfEmbedding hn J f (π (complexifiedMatrixLieIota ℂ n X) v) := by
  simp only [standardAdjointOfEmbedding_apply, hJL]
  have h := congrArg (fun w : kDual (complexStandardRep n ds) =>
      (w : Module.Dual ℂ (Standard n ds)) f)
    (transposeDualEquiv_lie ds hn (complexifiedMatrixLieIota ℂ n X) (J v))
  simp only [complexifiedMatrixLieIota_involutive,
    ComplexContragredient.dualLie_apply_apply] at h
  linear_combination h

include hJK in
lemma standardAdjoint_finite (f : Standard n ds) :
    FiniteVectors.IsFiniteVector ρ.dual (standardAdjointOfEmbedding hn J f) := by
  let σ := (complexStandardRep n ds).comp (compactIota ℂ n).toMonoidHom
  have hfin : FiniteVectors.IsFiniteVector σ f := by
    have : FiniteDimensional ℂ (FiniteVectors.orbitSpan (complexStandardRep n ds) f) :=
      (isComplexGKModule_complexStandardModule n ds).1 f
    apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan
      (complexStandardRep n ds) f)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨compactIota ℂ n k, rfl⟩
  apply ComplexStandardHomTransposeProof.isFiniteVector_dual_of_equivariant
    (σ := σ) (standardAdjointOfEmbedding hn J) ?_ hfin
  intro k g
  simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    compactIota_involutive] using standardAdjoint_rep hn J hJK
    (compactIota ℂ n k) g

end Embedding

/-- A quotient of a standard module which also embeds into the reversed standard module
has a transpose pairing if that standard module has a unique simple head. -/
theorem hasNonzeroTransposeGKPairing_of_matched_standard
    (hn : ds.length = n) (hgk : IsComplexGKModule n ρ π)
    (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ)
    (A : Standard n ds →ₗ[ℂ] V) (hA0 : A ≠ 0)
    (hA : IsComplexStandardIntertwining n ρ π ds A)
    (J : V →ₗ[ℂ] Standard n ds.reverse) (hJ0 : J ≠ 0)
    (hJK : ∀ k v, J (ρ k v) = complexStandardRep n ds.reverse k (J v))
    (hJL : ∀ X v, J (π X v) = complexStandardLie n ds.reverse X (J v))
    (R : Submodule ℂ (Standard n ds))
    (hR : IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) R)
    (hRtop : R ≠ ⊤)
    (hRmax : ∀ W : Submodule ℂ (Standard n ds),
      IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W → W ≠ ⊤ → W ≤ R) :
    HasNonzeroTransposeGKPairing ℂ n ρ π := by
  let q : Standard n ds →ₗ[ℂ] kDual ρ :=
    (standardAdjointOfEmbedding hn J).codRestrict (kDual ρ)
      (standardAdjoint_finite hn J hJK)
  have hq (f : Standard n ds) (v : V) : (q f : Module.Dual ℂ V) v =
      (transposeDualEquiv n ds hn (J v) : Module.Dual ℂ (Standard n ds)) f := rfl
  let ρD := (kDualRep ρ).comp (compactIota ℂ n).toMonoidHom
  let πD := (ComplexContragredient.dualLie hgk).comp
    (complexifiedMatrixLieIota ℂ n).toLieHom
  have hqK : ∀ k f, q (complexStandardRep n ds k f) = ρD k (q f) := by
    intro k f
    apply Subtype.ext
    exact standardAdjoint_rep hn J hJK k f
  have hqL : ∀ X f, q (complexStandardLie n ds X f) = πD X (q f) := by
    intro X f
    apply Subtype.ext
    ext v
    exact standardAdjoint_lie hn J hJL X f v
  have hq0 : q ≠ 0 := by
    intro h0
    apply hJ0
    ext v : 1
    apply (transposeDualEquiv n ds hn).injective
    rw [LinearMap.zero_apply, map_zero]
    apply Subtype.ext
    ext f
    have h := congrArg (fun w : kDual ρ => (w : Module.Dual ℂ V) v)
      (LinearMap.congr_fun h0 f)
    exact h
  have hDIrr : IsIrreducibleGKModule ρD πD := by
    have h := ComplexContragredient.isIrreducible_kDual hgk hirr hadm
    refine ⟨h.1, fun W hK hL => h.2 W ?_ ?_⟩
    · intro k w hw
      have h' := hK (compactIota ℂ n k) w hw
      change kDualRep ρ (compactIota ℂ n (compactIota ℂ n k)) w ∈ W at h'
      simpa only [compactIota_involutive] using h' 
    · intro X w hw
      have h' := hL (complexifiedMatrixLieIota ℂ n X) w hw
      change ComplexContragredient.dualLie hgk
        (complexifiedMatrixLieIota ℂ n (complexifiedMatrixLieIota ℂ n X)) w ∈ W at h'
      simpa only [complexifiedMatrixLieIota_involutive] using h' 
  have hkerA := eq_ker_of_largest_proper hA.map_rep hA.map_lie hirr hA0 hR hRtop hRmax
  have hkerq := eq_ker_of_largest_proper hqK hqL hDIrr hq0 hR hRtop hRmax
  have hker : LinearMap.ker A ≤ LinearMap.ker q := by rw [← hkerA, ← hkerq]
  have hsurj := surjective_of_isComplexStandardIntertwining n hirr hA hA0
  let D : V →ₗ[ℂ] kDual ρ :=
    ((LinearMap.ker A).liftQ q hker).comp
      (A.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hD (f : Standard n ds) : D (A f) = q f := by
    dsimp only [D, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  let B : V →ₗ[ℂ] Module.Dual ℂ V := (kDual ρ).subtype.comp D
  have hB (f : Standard n ds) (v : V) : B (A f) v = (q f : Module.Dual ℂ V) v := by
    change (D (A f) : Module.Dual ℂ V) v = _
    rw [hD]
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · intro k y x
    obtain ⟨f, rfl⟩ := hsurj y
    rw [← hA.map_rep, hB, hB, hqK]
    change (ρ.dual (compactIota ℂ n k) (q f)) (ρ (compactIota ℂ n k) x) =
      (q f : Module.Dual ℂ V) x
    rw [dual_apply_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  · intro X y x
    obtain ⟨f, rfl⟩ := hsurj y
    rw [← hA.map_lie, hB, hB, hqL]
    change -(q f : Module.Dual ℂ V) (π (complexifiedMatrixLieIota ℂ n X) x) +
      (q f : Module.Dual ℂ V) (π (complexifiedMatrixLieIota ℂ n X) x) = 0
    exact neg_add_cancel _
  · intro h0
    apply hq0
    ext f : 1
    apply Subtype.ext
    ext v
    rw [← hB, h0, LinearMap.zero_apply, LinearMap.zero_apply]
    rfl

end Langlands.Archimedean.ComplexTransposePairingClassification
