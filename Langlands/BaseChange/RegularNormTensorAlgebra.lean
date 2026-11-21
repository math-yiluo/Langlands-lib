import Langlands.BaseChange.RegularNormCentralizerAlgebra
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The scalar extension of the characteristic algebra -/

noncomputable section

namespace Langlands.BaseChange

open Matrix _root_.Polynomial
open Langlands.JacquetLanglands
open scoped TensorProduct

universe u v

section AdjoinRoot

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]
  (p : F[X])

local notation "q" => p.map (algebraMap F E)
local notation "T" => E ⊗[F] AdjoinRoot p

private def adjoinRootCoefficientMap : AdjoinRoot p →ₐ[F] AdjoinRoot q :=
  AdjoinRoot.mapAlgHom (Algebra.ofId F E) p q (dvd_refl q)

private def adjoinRootTensorMap : T →ₐ[E] AdjoinRoot q :=
  (adjoinRootCoefficientMap p).liftEquiv F E (AdjoinRoot p) (AdjoinRoot q)

private theorem adjoinRootTensorMap_one_tmul_root :
    adjoinRootTensorMap (E := E) p (1 ⊗ₜ AdjoinRoot.root p) = AdjoinRoot.root q := by
  rw [adjoinRootTensorMap, AlgHom.liftEquiv_tmul, one_smul]
  exact AdjoinRoot.map_root (algebraMap F E) p q (dvd_refl q)

private def adjoinRootTensorInv : AdjoinRoot q →ₐ[E] T :=
  AdjoinRoot.liftAlgHom q (Algebra.ofId E T) (1 ⊗ₜ AdjoinRoot.root p) (by
    change (q).eval₂ (algebraMap E T) _ = _
    rw [eval₂_map, ← IsScalarTower.algebraMap_eq F E T, ← aeval_def]
    let m : AdjoinRoot p →ₐ[F] T := Algebra.TensorProduct.includeRight
    change aeval (m (AdjoinRoot.root p)) p = 0
    rw [aeval_algHom_apply m, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero])

@[simp] private theorem adjoinRootTensorInv_root :
    adjoinRootTensorInv (E := E) p (AdjoinRoot.root q) = 1 ⊗ₜ AdjoinRoot.root p :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem adjoinRootTensorMap_comp_inv :
    (adjoinRootTensorMap (E := E) p).comp (adjoinRootTensorInv p) = AlgHom.id E (AdjoinRoot q) := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, AlgHom.id_apply, adjoinRootTensorInv_root,
    adjoinRootTensorMap_one_tmul_root]

private theorem adjoinRootTensorInv_comp_map :
    (adjoinRootTensorInv (E := E) p).comp (adjoinRootTensorMap p) = AlgHom.id E T := by
  apply Algebra.TensorProduct.ext_ring
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.restrictScalars_apply, AlgHom.id_apply, adjoinRootTensorMap_one_tmul_root,
    adjoinRootTensorInv_root]

/-- Extension of scalars commutes with adjoining a root. -/
def adjoinRootTensorEquiv : T ≃ₐ[E] AdjoinRoot q :=
  AlgEquiv.ofAlgHom (adjoinRootTensorMap p) (adjoinRootTensorInv p)
    (adjoinRootTensorMap_comp_inv p) (adjoinRootTensorInv_comp_map p)

@[simp] theorem adjoinRootTensorEquiv_one_tmul_root :
    adjoinRootTensorEquiv (E := E) p (1 ⊗ₜ AdjoinRoot.root p) = AdjoinRoot.root q :=
  adjoinRootTensorMap_one_tmul_root p

variable (σ : E ≃ₐ[F] E)

private theorem mappedPolynomial_fixed : (q).map σ.toRingHom = q := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext σ.commutes

private theorem adjoinRootTensorEquiv_intertwine (x : T) :
    adjoinRootTensorEquiv p (Algebra.TensorProduct.congr σ (AlgEquiv.refl : AdjoinRoot p ≃ₐ[F] _) x) =
      AdjoinRoot.mapAlgEquiv σ q q (Associated.of_eq (mappedPolynomial_fixed p σ))
        (adjoinRootTensorEquiv p x) := by
  let e := (adjoinRootTensorEquiv (E := E) p).toRingHom
  let t := Algebra.TensorProduct.congr σ (AlgEquiv.refl : AdjoinRoot p ≃ₐ[F] _)
  let s := AdjoinRoot.mapAlgEquiv σ q q (Associated.of_eq (mappedPolynomial_fixed p σ))
  have hh : e.comp t.toRingHom = s.toRingHom.comp e := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro z
      change adjoinRootTensorEquiv p (t (z ⊗ₜ 1)) = s (adjoinRootTensorEquiv p (z ⊗ₜ 1))
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      change adjoinRootTensorEquiv p (algebraMap E T (σ z)) =
        s (adjoinRootTensorEquiv p (algebraMap E T z))
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
      simp [s, AdjoinRoot.algebraMap_eq]
    · apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro z
        have ht : (1 : E) ⊗ₜ[F] AdjoinRoot.of p z = algebraMap F T z := by
          rw [Algebra.TensorProduct.algebraMap_apply', AdjoinRoot.algebraMap_eq]
        change adjoinRootTensorEquiv p (t (1 ⊗ₜ AdjoinRoot.of p z)) =
          s (adjoinRootTensorEquiv p (1 ⊗ₜ AdjoinRoot.of p z))
        rw [ht, t.commutes, IsScalarTower.algebraMap_apply F E T, AlgEquiv.commutes,
          ← IsScalarTower.algebraMap_apply F E (AdjoinRoot q), s.commutes]
      · change adjoinRootTensorEquiv p (t (1 ⊗ₜ AdjoinRoot.root p)) =
          s (adjoinRootTensorEquiv p (1 ⊗ₜ AdjoinRoot.root p))
        rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
        simp [s]
  exact DFunLike.congr_fun hh x

end AdjoinRoot

/-- Extend an automorphism of the right tensor factor by the identity on the left factor. -/
def tensorFactorAut {F : Type u} [CommRing F] (B : Type*) [CommRing B] [Algebra F B]
    {E : Type v} [CommRing E] [Algebra F E] (σ : E ≃ₐ[F] E) : B ⊗[F] E ≃ₐ[B] B ⊗[F] E :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) σ

@[simp] theorem tensorFactorAut_tmul {F : Type u} [CommRing F] (B : Type*) [CommRing B]
    [Algebra F B] {E : Type v} [CommRing E] [Algebra F E] (σ : E ≃ₐ[F] E) (b : B) (x : E) :
    tensorFactorAut B σ (b ⊗ₜ x) = b ⊗ₜ σ x := rfl

section Matrix

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {n l : ℕ} (σ : E ≃ₐ[F] E) (γ : GeneralLinear n F)

local notation "p₀" => Matrix.charpoly γ.val
local notation "P" => Matrix.charpoly (Units.val (baseChange F E n γ))

/-- Identify the upper characteristic algebra with the tensor product of the
base characteristic algebra and the upper coefficient algebra. -/
def charpolyTensorEquiv : (AdjoinRoot p₀ ⊗[F] E) ≃ₐ[F] AdjoinRoot P :=
  (Algebra.TensorProduct.comm F _ _).trans <|
    ((adjoinRootTensorEquiv (E := E) p₀).restrictScalars F).trans <|
      AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : E ≃ₐ[F] E) _ _
        (Associated.of_eq (by
          change ((p₀).map (algebraMap F E)).map (RingHom.id E) = (γ.val.map (algebraMap F E)).charpoly
          rw [Polynomial.map_id, Matrix.charpoly_map]))

@[simp] theorem charpolyTensorEquiv_root_tmul_one :
    charpolyTensorEquiv (E := E) γ (AdjoinRoot.root p₀ ⊗ₜ 1) = AdjoinRoot.root P := by
  simp [charpolyTensorEquiv]

private theorem charpolyTensorEquiv_intertwine (x : AdjoinRoot p₀ ⊗[F] E) :
    charpolyTensorEquiv γ (tensorFactorAut (AdjoinRoot p₀) σ x) =
      centralizerAlgebraAut σ γ (charpolyTensorEquiv γ x) := by
  let c := Algebra.TensorProduct.comm F (AdjoinRoot p₀) E
  let r := (tensorFactorAut (AdjoinRoot p₀) σ).restrictScalars F
  let t := Algebra.TensorProduct.congr σ (AlgEquiv.refl : AdjoinRoot p₀ ≃ₐ[F] _)
  have hc : c.toAlgHom.comp r.toAlgHom = t.toAlgHom.comp c.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a z
    simp [c, r, t]
  have h := AlgHom.congr_fun hc x
  change c (tensorFactorAut (AdjoinRoot p₀) σ x) = t (c x) at h
  simp only [charpolyTensorEquiv, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  rw [show (Algebra.TensorProduct.comm F (AdjoinRoot p₀) E) (tensorFactorAut (AdjoinRoot p₀) σ x) =
      t ((Algebra.TensorProduct.comm F (AdjoinRoot p₀) E) x) from h]
  rw [adjoinRootTensorEquiv_intertwine p₀ σ]
  let f := AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : E ≃ₐ[F] E)
    ((p₀).map (algebraMap F E)) P (Associated.of_eq (by
      change ((p₀).map (algebraMap F E)).map (RingHom.id E) = (γ.val.map (algebraMap F E)).charpoly
      rw [Polynomial.map_id, Matrix.charpoly_map]))
  let s := AdjoinRoot.mapAlgEquiv σ ((p₀).map (algebraMap F E)) ((p₀).map (algebraMap F E))
    (Associated.of_eq (mappedPolynomial_fixed p₀ σ))
  have hf : f.toRingHom.comp s.toRingHom =
      (centralizerAlgebraAut σ γ).toRingHom.comp f.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · ext z
      simp [f, s, centralizerAlgebraAut]
    · simp [f, s, centralizerAlgebraAut]
  exact DFunLike.congr_fun hf _

/-- Express the matrix norm condition as a product in the actual tensor
algebra over the base characteristic algebra. -/
theorem isNorm_iff_charpolyTensor_product (hσ : IsCyclicAlgebra σ l)
    (hγ : IsRegularSemisimple γ) :
    IsNorm σ l γ ↔ ∃ b : (AdjoinRoot p₀ ⊗[F] E)ˣ,
      ((List.range l).map fun i => (tensorFactorAut (AdjoinRoot p₀) σ ^ i) b.val).prod =
        AdjoinRoot.root p₀ ⊗ₜ 1 := by
  let e := charpolyTensorEquiv (E := E) γ
  let s := tensorFactorAut (AdjoinRoot p₀) σ
  let t := centralizerAlgebraAut σ γ
  have commute (i : ℕ) (x : AdjoinRoot p₀ ⊗[F] E) :
      e ((s ^ i) x) = (t ^ i) (e x) := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ s, pow_succ t, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih,
        charpolyTensorEquiv_intertwine]
  have product (b : (AdjoinRoot p₀ ⊗[F] E)ˣ) :
      e (((List.range l).map fun i => (s ^ i) b.val).prod) =
        ((List.range l).map fun i => (t ^ i) (Units.map e.toMonoidHom b).val).prod := by
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod <| List.map_congr_left fun i _ => commute i b.val
  rw [isNorm_iff_centralizerAlgebra_product σ γ hσ hγ]
  constructor
  · rintro ⟨b, hb⟩
    let u := Units.map e.symm.toMonoidHom b
    have hu : Units.map e.toMonoidHom u = b := Units.ext (e.apply_symm_apply b.val)
    refine ⟨u, e.injective ?_⟩
    rw [product u, hu, hb, charpolyTensorEquiv_root_tmul_one]
  · rintro ⟨b, hb⟩
    refine ⟨Units.map e.toMonoidHom b, ?_⟩
    rw [← product b]
    change e (((List.range l).map fun i => (tensorFactorAut (AdjoinRoot p₀) σ ^ i) b.val).prod) = _
    rw [hb, charpolyTensorEquiv_root_tmul_one]

end Matrix

/-- The regular norm criterion in the tensor product of the base characteristic
algebra with the upper coefficient algebra. -/
def RegularNormTensorAlgebraStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [CommRing E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ (γ : GeneralLinear n F), IsRegularSemisimple γ →
      let p := γ.val.charpoly
      IsNorm σ l γ ↔ ∃ b : (AdjoinRoot p ⊗[F] E)ˣ,
        ((List.range l).map fun i => (tensorFactorAut (AdjoinRoot p) σ ^ i) b.val).prod =
          AdjoinRoot.root p ⊗ₜ 1

theorem regularNormTensorAlgebra : RegularNormTensorAlgebraStatement.{u, v} := by
  intro F _ E _ _ σ l n hσ γ hγ
  exact isNorm_iff_charpolyTensor_product σ γ hσ hγ

end Langlands.BaseChange
