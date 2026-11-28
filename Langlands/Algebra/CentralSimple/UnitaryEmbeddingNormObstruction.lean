import Langlands.Algebra.CentralSimple.UnitaryReducedNormInvolution
import Langlands.Algebra.CentralSimple.UnitaryReducedNormRestriction
import Langlands.ClassFieldTheory.Global.QuadraticTensorUnitConjugation

/-! # The determinant norm condition from a unitary twist equation -/

noncomputable section

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open Langlands.ClassFieldTheory.Global.TensorUnitShapiro

universe u

variable {F E B : Type u} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

section Restriction

variable {K P : Type u} [Field K] [Algebra F K] [FiniteDimensional F K]
  [Field P] [Algebra F P] [Algebra E P] [IsScalarTower F E P] [FiniteDimensional E P]
  [Infinite E]

/-- The relative reduced norm of a base-changed subfield element can be computed
by taking its determinant norm before adjoining the quadratic coefficient field. -/
theorem relativeReducedNorm_tensor_inclusion (ε : P →ₐ[E] B)
    (hdim : Module.finrank E P = reducedDegree E B)
    (e : E ⊗[F] K ≃ₐ[E] P) (ι : K →ₐ[F] P)
    (hι : ∀ k : K, e ((1 : E) ⊗ₜ[F] k) = ι k)
    (R : Type u) [CommRing R] [Algebra F R] (a : R ⊗[F] K) :
    reducedNorm E B (E ⊗[F] R) (UnitaryPoints.tensorEquiv F E B R
      (Algebra.TensorProduct.map (AlgHom.id R R) ((ε.restrictScalars F).comp ι) a)) =
      (1 : E) ⊗ₜ[F] Algebra.norm R a := by
  let S := E ⊗[F] R
  let j : R →ₐ[F] S := Algebra.TensorProduct.includeRight
  let e₁ := (Algebra.TensorProduct.cancelBaseChange F E S S K).symm
  let e₂ : S ⊗[E] (E ⊗[F] K) ≃ₐ[S] S ⊗[E] P := Algebra.TensorProduct.congr AlgEquiv.refl e
  let f : R ⊗[F] K →ₐ[F] S ⊗[F] K := Algebra.TensorProduct.map j (AlgHom.id F K)
  let t : S ⊗[E] P →ₐ[S] S ⊗[E] B := Algebra.TensorProduct.map (AlgHom.id S S) ε
  have he (x : R ⊗[F] K) :
      UnitaryPoints.tensorEquiv F E B R
        (Algebra.TensorProduct.map (AlgHom.id R R) ((ε.restrictScalars F).comp ι) x) =
      t (e₂ (e₁ (f x))) := by
    induction x using TensorProduct.inductionOn with
    | tmul r k =>
      change ((1 : E) ⊗ₜ[F] r) ⊗ₜ[E] ε (ι k) =
        ((1 : E) ⊗ₜ[F] r) ⊗ₜ[E] ε (e ((1 : E) ⊗ₜ[F] k))
      rw [hι]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [he]
  change reducedNorm E B S (Algebra.TensorProduct.map (AlgHom.id E S) ε (e₂ (e₁ (f a)))) = _
  rw [reducedNorm_eq_field_norm_tensor E B ε hdim, Algebra.norm_eq_of_algEquiv e₂,
    Algebra.norm_eq_of_algEquiv e₁]
  exact norm_baseChange_naturality (Module.finBasis F K) j a

end Restriction

section Symmetry

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (τ : FirstKindInvolution F B)
  (hτ : ∀ a : E, τ (algebraMap E B a) = algebraMap E B (conjugation F E a))
include hτ

/-- The reduced norm of a symmetric global unit is a unit in the fixed field of
conjugation on the center. -/
theorem exists_scalar_reducedNorm_of_symmetric (g : Bˣ) (hg : τ (g : B) = g) :
    ∃ d : Fˣ, algebraMap F E (d : F) = reducedNorm E B E ((1 : E) ⊗ₜ[E] (g : B)) := by
  let n := reducedNorm E B E ((1 : E) ⊗ₜ[E] (g : B))
  have hred := relativeReducedNorm_involution τ hτ F ((1 : F) ⊗ₜ[F] (g : B))
  rw [FirstKindInvolution.baseChange_tmul, hg, UnitaryPoints.tensorEquiv_tmul] at hred
  have he := reducedNorm_naturality E B
    (Algebra.TensorProduct.includeLeft : E →ₐ[E] E ⊗[F] F) ((1 : E) ⊗ₜ[E] (g : B))
  change reducedNorm E B (E ⊗[F] F) (((1 : E) ⊗ₜ[F] (1 : F)) ⊗ₜ[E] (g : B)) =
    n ⊗ₜ[F] (1 : F) at he
  rw [he] at hred
  have hconj : n = conjugation F E n := by
    have hr := congrArg (Algebra.TensorProduct.rid F E E) hred
    simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.rid_tmul, one_smul] using hr
  let c := Algebra.trace F E n / 2
  have hc : algebraMap F E c = n := by
    have : CharZero E := Algebra.charZero_of_charZero F E
    rw [map_div₀, algebraMap_trace, ← hconj, map_ofNat]
    ring
  have hn : IsUnit n := IsUnit.map (reducedNorm E B E)
    (g.isUnit.map (Algebra.TensorProduct.includeRight : B →ₐ[E] E ⊗[E] B))
  have hne : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact hn.ne_zero hc.symm
  exact ⟨Units.mk0 c hne, hc⟩

omit [CharZero F] in
/-- The relative norm of `h τ(h)` is the scalar image of the determinant norm
of the relative reduced norm of `h`. -/
theorem relativeReducedNorm_mul_involution
    (R : Type u) [CommRing R] [Algebra F R] (h : R ⊗[F] B) :
    reducedNorm E B (E ⊗[F] R) (UnitaryPoints.tensorEquiv F E B R (h * τ.baseChange R h)) =
      (1 : E) ⊗ₜ[F] Langlands.Algebra.tensorNorm F E R
        (reducedNorm E B (E ⊗[F] R) (UnitaryPoints.tensorEquiv F E B R h)) := by
  let z := reducedNorm E B (E ⊗[F] R) (UnitaryPoints.tensorEquiv F E B R h)
  rw [map_mul, map_mul, relativeReducedNorm_involution τ hτ]
  rw [show (1 : E) ⊗ₜ[F] Langlands.Algebra.tensorNorm F E R z =
    z * quadraticTensorConjugation z from includeRight_tensorNorm_quadratic z]
  congr 1
  change Algebra.TensorProduct.map (conjugation F E).toAlgHom (AlgHom.id F R) z =
    quadraticTensorConjugation z
  induction z using TensorProduct.inductionOn with
  | tmul a r => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

end Symmetry

/-- A unitary twist equation makes the determinant norm of its fixed-field parameter,
multiplied by the reduced norm of the symmetric twist, a quadratic norm. -/
def UnitaryEmbeddingNormObstructionStatement : Prop :=
  ∀ (F E B K P : Type u) [Field F] [CharZero F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    [Field K] [Algebra F K] [FiniteDimensional F K]
    [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P] [FiniteDimensional E P]
    (τ : FirstKindInvolution F B),
    (∀ a : E, τ (algebraMap E B a) = algebraMap E B (conjugation F E a)) →
    Module.finrank E B = Module.finrank E P ^ 2 →
    ∀ (ε : P →ₐ[E] B) (e : E ⊗[F] K ≃ₐ[E] P) (ι : K →ₐ[F] P),
    (∀ x : K, e ((1 : E) ⊗ₜ[F] x) = ι x) →
    ∀ (g : Bˣ), τ (g : B) = g →
    ∃ d : Fˣ,
      algebraMap F E (d : F) = reducedNorm E B E ((1 : E) ⊗ₜ[E] (g : B)) ∧
      ∀ (R : Type u) [CommRing R] [Algebra F R] (a : (R ⊗[F] K)ˣ) (h : (R ⊗[F] B)ˣ),
        ((1 : R) ⊗ₜ[F] (g : B)) *
            Algebra.TensorProduct.map (AlgHom.id R R) ((ε.restrictScalars F).comp ι) a =
          (h : R ⊗[F] B) * τ.baseChange R h →
        ∃ z : (E ⊗[F] R)ˣ, Langlands.Algebra.tensorNorm F E R z =
          algebraMap F R (d : F) * Algebra.norm R (a : R ⊗[F] K)

theorem unitaryEmbeddingNormObstruction : UnitaryEmbeddingNormObstructionStatement.{u} := by
  intro F E B K P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ hτ hdim ε e ι hι g hg
  have : CharZero E := Algebra.charZero_of_charZero F E
  have hdeg : Module.finrank E P = reducedDegree E B := by
    apply Nat.pow_left_injective (n := 2) (by decide)
    change Module.finrank E P ^ 2 = reducedDegree E B ^ 2
    rw [pow_two (reducedDegree E B), ← (reducedNorm_degree_spec E B).2, hdim]
  obtain ⟨d, hd⟩ := exists_scalar_reducedNorm_of_symmetric τ hτ g hg
  refine ⟨d, hd, ?_⟩
  intro R _ _ a h heq
  let C := UnitaryPoints.tensorEquiv F E B R
  let v := reducedNorm E B (E ⊗[F] R)
  have hg' : v (C ((1 : R) ⊗ₜ[F] (g : B))) =
      (1 : E) ⊗ₜ[F] algebraMap F R (d : F) := by
    have hnat := reducedNorm_naturality E B
      (Algebra.TensorProduct.includeLeft : E →ₐ[E] E ⊗[F] R) ((1 : E) ⊗ₜ[E] (g : B))
    change v (C ((1 : R) ⊗ₜ[F] (g : B))) =
      reducedNorm E B E ((1 : E) ⊗ₜ[E] (g : B)) ⊗ₜ[F] (1 : R) at hnat
    rw [hnat, ← hd, Algebra.algebraMap_eq_smul_one (R := F) (A := E),
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have he := congrArg (fun y : R ⊗[F] B => v (C y)) heq
  change v (C (_ * _)) = v (C (_ * _)) at he
  rw [map_mul C, map_mul v, hg', relativeReducedNorm_tensor_inclusion ε hdeg e ι hι,
    relativeReducedNorm_mul_involution τ hτ] at he
  refine ⟨UnitaryPoints.relativeNorm F E B R h, ?_⟩
  apply Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective F E)
  change (1 : E) ⊗ₜ[F] Langlands.Algebra.tensorNorm F E R (v (C (h : R ⊗[F] B))) =
    (1 : E) ⊗ₜ[F] (algebraMap F R (d : F) * Algebra.norm R (a : R ⊗[F] K))
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using he.symm

end Langlands.CentralSimple
