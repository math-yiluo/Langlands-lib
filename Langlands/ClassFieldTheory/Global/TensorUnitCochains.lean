import Langlands.ClassFieldTheory.Global.TensorUnitShapiro
import Langlands.ClassFieldTheory.Local.RelativeH1Proof
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction
import Mathlib.FieldTheory.SplittingField.Construction

/-! # Primitives and finite refinements of tensor-unit cochains -/

noncomputable section

universe u

open CategoryTheory groupCohomology Polynomial
open scoped TensorProduct

namespace Langlands.ClassFieldTheory.Global.TensorUnitShapiro

open ClassFieldTheory.Local GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false

variable {F B L : Type u} [Field F] [Field B] [Field L] [Algebra F B] [Algebra F L]

/-- The crossed coboundary of a unit of the actual tensor algebra. -/
def tensorCoboundary (x : (B ⊗[F] L)ˣ) (σ : Gal(L/F)) : (B ⊗[F] L)ˣ :=
  tensorAction F B L σ x / x

/-- The degree-two differential in the multiplicative notation for tensor units. -/
def tensorDifferential (c : Gal(L/F) → (B ⊗[F] L)ˣ) (σ τ : Gal(L/F)) : (B ⊗[F] L)ˣ :=
  tensorAction F B L σ (c τ) / c (σ * τ) * c σ

theorem tensorAction_mul (σ τ : Gal(L/F)) (x : (B ⊗[F] L)ˣ) :
    tensorAction F B L (σ * τ) x = tensorAction F B L σ (tensorAction F B L τ x) :=
  congrArg Additive.toMul (LinearMap.congr_fun (map_mul (tensorUnitRepresentation F B L).ρ σ τ)
    (Additive.ofMul x))

/-- A tensor-unit coboundary has trivial degree-two differential. -/
theorem tensorDifferential_tensorCoboundary (x : (B ⊗[F] L)ˣ) (σ τ : Gal(L/F)) :
    tensorDifferential (tensorCoboundary x) σ τ = 1 := by
  simp only [tensorDifferential, tensorCoboundary, _root_.map_div, tensorAction_mul]
  rw [div_div_div_comm, div_self', div_mul_cancel]

variable [Algebra B L] [IsScalarTower F B L] [FiniteDimensional F B] [FiniteDimensional F L]
  [IsGalois F L] [Algebra.IsSeparable F B]

/-- Hilbert 90 for the actual tensor-unit coefficient module. -/
theorem exists_tensorCoboundary (c : Gal(L/F) → (B ⊗[F] L)ˣ)
    (hc : ∀ σ τ, c (σ * τ) = tensorAction F B L σ (c τ) * c σ) :
    ∃ x : (B ⊗[F] L)ˣ, ∀ σ, tensorCoboundary x σ = c σ := by
  let A := tensorUnitRepresentation F B L
  let z : cocycles₁ A := ⟨Additive.ofMul ∘ c, (mem_cocycles₁_iff _).mpr hc⟩
  let : FiniteDimensional B L := FiniteDimensional.right F B L
  have : IsGalois B L := IsGalois.tower_top_of_isGalois F B L
  let hsub : Subsingleton (relativeCohomology B L 1) := finiteRelativeH1Vanishing B L
  have hz : H1π A z = 0 := by
    apply (cohomologyIso F B L 1).toLinearEquiv.injective
    exact hsub.elim _ _
  obtain ⟨x, hx⟩ := (H1π_eq_zero_iff z).mp hz
  exact ⟨Additive.toMul x, fun σ => congrFun hx σ⟩

section Extension

variable (M : Type u) [Field M] [Algebra F M] [Algebra L M] [IsScalarTower F L M]

/-- Extend the right coefficient field of the tensor unit. -/
def extendTensorUnit : (B ⊗[F] L)ˣ →* (B ⊗[F] M)ˣ :=
  Units.map (Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom F L M)).toMonoidHom

omit [Algebra B L] [IsScalarTower F B L] [FiniteDimensional F B] [FiniteDimensional F L]
  [Algebra.IsSeparable F B] in
/-- Scalar extension of tensor units is equivariant for restriction of automorphisms. -/
theorem extendTensorUnit_action (σ : Gal(M/F)) (x : (B ⊗[F] L)ˣ) :
    tensorAction F B M σ (extendTensorUnit M x) =
      extendTensorUnit M (tensorAction F B L (σ.restrictNormal L) x) := by
  apply Units.ext
  change Algebra.TensorProduct.lTensor (S := B) B σ.toAlgHom
      (Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom F L M) (x : B ⊗[F] L)) =
    Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom F L M)
      (Algebra.TensorProduct.lTensor (S := B) B (σ.restrictNormal L).toAlgHom (x : B ⊗[F] L))
  have h : σ.toAlgHom.comp (IsScalarTower.toAlgHom F L M) =
      (IsScalarTower.toAlgHom F L M).comp (σ.restrictNormal L).toAlgHom :=
    AlgHom.ext fun t => (σ.restrictNormal_commutes L t).symm
  have h' := congrArg (fun j : L →ₐ[F] M => Algebra.TensorProduct.lTensor (S := B) B j) h
  simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_id_comp] at h'
  exact DFunLike.congr_fun h' _

end Extension

omit [IsGalois F L] in
private theorem exists_common_roots {I : Type u} [Finite I] [CharZero F]
    (n : ℕ) (hn : n ≠ 0) (x : I → Lˣ) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : FiniteDimensional F M) (_ : IsGalois F M)
      (_ : Algebra L M) (_ : IsScalarTower F L M) (z : I → Mˣ),
        ∀ i, z i ^ n = Units.map (algebraMap L M) (x i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let p (i : I) : L[X] := X ^ n - C (x i : L)
  let f : L[X] := ∏ i, p i
  let N := f.SplittingField
  have hs (i : I) : ((p i).map (algebraMap L N)).Splits := by
    have hall := SplittingField.splits f
    rw [show f = ∏ j, p j from rfl, Polynomial.map_prod] at hall
    have hnonzero (j : I) (_ : j ∈ Finset.univ) : (p j).map (algebraMap L N) ≠ 0 := by
      apply ne_zero_of_natDegree_gt
      rw [natDegree_map, natDegree_X_pow_sub_C]
      exact Nat.pos_of_ne_zero hn
    exact (Polynomial.splits_prod_iff hnonzero).mp hall i (Finset.mem_univ i)
  have hroot (i : I) : ∃ z : Nˣ, z ^ n = Units.map (algebraMap L N) (x i) := by
    have hdeg : ((p i).map (algebraMap L N)).degree ≠ 0 := by
      apply degree_ne_of_natDegree_ne
      rwa [natDegree_map, natDegree_X_pow_sub_C]
    obtain ⟨r, hr⟩ := (hs i).exists_eval_eq_zero hdeg
    have hr' : r ^ n = algebraMap L N (x i : L) := by
      apply sub_eq_zero.mp
      simpa only [p, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
        eval_sub, eval_pow, eval_X, eval_C] using hr
    have hr₀ : r ≠ 0 := by
      intro h
      rw [h, zero_pow hn] at hr'
      exact (x i).ne_zero ((algebraMap L N).injective (hr'.symm.trans (map_zero _).symm))
    exact ⟨Units.mk0 r hr₀, Units.ext hr'⟩
  choose z hz using hroot
  let : FiniteDimensional F N := FiniteDimensional.trans F L N
  obtain ⟨M, hMfin, hMgal, ⟨j⟩⟩ := GroupScheme.exists_finite_galois_algHom F N
  let i := j.comp (IsScalarTower.toAlgHom F L N)
  let : Algebra L M := i.toRingHom.toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun a => (i.commutes a).symm
  refine ⟨M, inferInstance, inferInstance, hMfin, hMgal, inferInstance, inferInstance,
    fun k => Units.map j.toRingHom (z k), fun k => ?_⟩
  rw [← map_pow, hz]
  rfl

/-- A tensor unit has an actual `n`-th root after finite Galois refinement, for positive `n`. -/
theorem exists_tensorUnit_root [CharZero F] (n : ℕ) (hn : n ≠ 0) (x : (B ⊗[F] L)ˣ) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : FiniteDimensional F M) (_ : IsGalois F M)
      (_ : Algebra L M) (_ : IsScalarTower F L M) (y : (B ⊗[F] M)ˣ),
        y ^ n = extendTensorUnit M x := by
  let I := B →ₐ[F] L
  let hsplit (x : B) : ((minpoly F x).map (algebraMap F L)).Splits := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom F B L) (algebraMap B L).injective x]
    exact (inferInstance : Normal F L).splits (algebraMap B L x)
  let E := separableEmbeddingDecomposition F B L hsplit
  let e : B ⊗[F] L ≃+* (I → L) := (tensorEmbeddingEquiv F B L).toRingEquiv
  obtain ⟨M, _, _, _, _, _, _, z, hz⟩ := exists_common_roots (F := F) n hn
    (unitEmbeddingEquiv F B L x)
  let d : B ⊗[F] M ≃+* (I → M) := decompositionTensorEquiv F L B M I E
  let u : (B ⊗[F] M)ˣ ≃* (I → Mˣ) :=
    (Units.mapEquiv d.toMulEquiv).trans MulEquiv.piUnits
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    u.symm z, u.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  have hc (t : B ⊗[F] L) (j : I) :
      d (Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom F L M) t) j =
        algebraMap L M (e t j) := by
    induction t using TensorProduct.inductionOn with
    | tmul b l =>
      change decompositionTensorEquiv F L B M I E (b ⊗ₜ[F] algebraMap L M l) j =
        algebraMap L M (l * j b)
      rw [decompositionTensorEquiv_tmul]
      change (1 * j b) • algebraMap L M l = algebraMap L M (l * j b)
      rw [one_mul, Algebra.smul_def, map_mul, mul_comm]
    | add t s ht hs => simp only [map_add, Pi.add_apply, ht, hs]
  funext j
  change z j ^ n = u (extendTensorUnit M x) j
  rw [hz]
  apply Units.ext
  exact (hc (x : B ⊗[F] L) j).symm

/-- Existence of a tensor-unit primitive with values of `n`-th power one on a finite
Galois refinement of the original coefficient field. -/
def TensorTorsionPrimitiveAfterRefinement (n : ℕ)
    (c : Gal(L/F) × Gal(L/F) → (B ⊗[F] L)ˣ) : Prop :=
  ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : FiniteDimensional F M) (_ : IsGalois F M)
    (_ : Algebra L M) (_ : IsScalarTower F L M) (a : Gal(M/F) → (B ⊗[F] M)ˣ),
      (∀ σ, a σ ^ n = 1) ∧
      ∀ σ τ, tensorDifferential a σ τ = extendTensorUnit M (c (σ.restrictNormal L, τ.restrictNormal L))

/-- A finite Galois refinement removes the power of the primitive by Hilbert 90. -/
theorem tensorTorsionPrimitiveAfterRefinement_of_units [CharZero F]
    (n : ℕ) (hn : n ≠ 0) (c : Gal(L/F) × Gal(L/F) → (B ⊗[F] L)ˣ)
    (hpow : ∀ p, c p ^ n = 1)
    (h : ∃ b : Gal(L/F) → (B ⊗[F] L)ˣ, ∀ σ τ, tensorDifferential b σ τ = c (σ, τ)) :
    TensorTorsionPrimitiveAfterRefinement n c := by
  obtain ⟨b, hb⟩ := h
  have hp (σ τ : Gal(L/F)) : b (σ * τ) ^ n = tensorAction F B L σ (b τ ^ n) * b σ ^ n := by
    have he := congrArg (fun x : (B ⊗[F] L)ˣ => x ^ n) (hb σ τ)
    rw [hpow, tensorDifferential, mul_pow, div_pow, ← map_pow, div_mul_eq_mul_div] at he
    exact (div_eq_one.mp he).symm
  obtain ⟨x, hx⟩ := exists_tensorCoboundary (fun σ => b σ ^ n) hp
  obtain ⟨M, _, _, _, _, _, _, y, hy⟩ := exists_tensorUnit_root n hn x
  let t (σ : Gal(M/F)) := extendTensorUnit M (b (σ.restrictNormal L))
  let q := tensorCoboundary y
  have ht (σ τ : Gal(M/F)) : tensorDifferential t σ τ =
      extendTensorUnit M (c (σ.restrictNormal L, τ.restrictNormal L)) := by
    let ρ : Gal(M/F) →* Gal(L/F) := AlgEquiv.restrictNormalHom L
    change tensorAction F B M σ (extendTensorUnit M (b (ρ τ))) /
      extendTensorUnit M (b (ρ (σ * τ))) * extendTensorUnit M (b (ρ σ)) =
        extendTensorUnit M (c (ρ σ, ρ τ))
    rw [extendTensorUnit_action, map_mul ρ, ← _root_.map_div, ← map_mul]
    exact congrArg (extendTensorUnit M) (hb (ρ σ) (ρ τ))
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun σ => t σ / q σ, ?_, ?_⟩
  · intro σ
    dsimp [t, q, tensorCoboundary]
    rw [div_pow, div_pow, ← map_pow (tensorAction F B M σ), hy, extendTensorUnit_action,
      ← _root_.map_div, show tensorAction F B L (σ.restrictNormal L) x / x =
        b (σ.restrictNormal L) ^ n from hx _, map_pow, div_self']
  · intro σ τ
    change tensorAction F B M σ (t τ / q τ) / (t (σ * τ) / q (σ * τ)) * (t σ / q σ) = _
    rw [_root_.map_div, div_div_div_comm, div_mul_div_comm,
      show tensorAction F B M σ (t τ) / t (σ * τ) * t σ = _ from ht σ τ,
      show tensorAction F B M σ (q τ) / q (σ * τ) * q σ = 1 from
        tensorDifferential_tensorCoboundary y σ τ, div_one]

end Langlands.ClassFieldTheory.Global.TensorUnitShapiro
