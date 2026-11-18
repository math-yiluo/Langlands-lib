import Langlands.Algebra.BrauerCorestriction.Dimension
import Langlands.Algebra.CentralSimpleTensor
import Langlands.Algebra.CentralSimpleScalarExtension

/-!
# Central simplicity of the tensor descent

A finite tensor product of finite-dimensional central simple algebras over a field is central
simple. Consequently the tensor product of the conjugates of a finite-dimensional central simple
`L`-algebra is central simple over `N`, and its Galois-fixed algebra is a finite-dimensional
central simple `K`-algebra.
-/

universe u₁ u₂ u₃ u₄ v w

open TensorProduct PiTensorProduct
open Langlands.PiTensorSemilinear

namespace Langlands.BrauerCorestriction

section PiTensorCSA

variable (K : Type u₁) [Field K]

/-- The statement that every family of finite-dimensional central simple `K`-algebras in
universe `v` indexed by `ι` has a central simple tensor product. -/
def PiCentralSimple (ι : Type w) : Prop :=
  ∀ (B : ι → Type v) [∀ i, Ring (B i)] [∀ i, Algebra K (B i)] [∀ i, FiniteDimensional K (B i)]
    [∀ i, Algebra.IsCentral K (B i)] [∀ i, IsSimpleRing (B i)],
    Algebra.IsCentral K (⨂[K] i, B i) ∧ IsSimpleRing (⨂[K] i, B i)

theorem piCentralSimple_of_equiv {α β : Type w} (e : α ≃ β)
    (h : PiCentralSimple.{u₁, v} K α) : PiCentralSimple.{u₁, v} K β := by
  intro B _ _ _ _ _
  obtain ⟨hc, hs⟩ := h (fun i => B (e i))
  let f : (⨂[K] j, B j) ≃ₐ[K] ⨂[K] i, B (e i) :=
    AlgEquiv.ofLinearEquiv (reindex K B e.symm) (reindex_one K e.symm) (reindex_mul K e.symm)
  have := hc
  exact ⟨Algebra.IsCentral.of_algEquiv K _ _ f.symm,
    IsSimpleRing.of_ringEquiv f.symm.toRingEquiv hs⟩

theorem piCentralSimple_empty : PiCentralSimple.{u₁, v} K PEmpty := by
  intro B _ _ _ _ _
  have hsurj : Function.Surjective (algebraMap K (⨂[K] i, B i)) := by
    intro x
    refine ⟨isEmptyEquiv PEmpty x, ?_⟩
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [map_smul, isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one,
        Algebra.algebraMap_eq_smul_one, PiTensorProduct.one_def]
      congr 2
      funext i
      exact i.elim
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : Nontrivial (⨂[K] i : PEmpty, B i) := (isEmptyEquiv PEmpty).toEquiv.nontrivial
  have hinj : Function.Injective (algebraMap K (⨂[K] i, B i)) := (algebraMap K _).injective
  refine ⟨⟨fun z _ => Algebra.mem_bot.mpr (hsurj z)⟩, ?_⟩
  exact IsSimpleRing.of_ringEquiv (RingEquiv.ofBijective (algebraMap K _) ⟨hinj, hsurj⟩)
    inferInstance

theorem piCentralSimple_option {α : Type w} [Fintype α] (h : PiCentralSimple.{u₁, v} K α) :
    PiCentralSimple.{u₁, v} K (Option α) := by
  intro B _ _ _ _ _
  obtain ⟨hc, hs⟩ := h (fun i => B (some i))
  have := hc
  have := hs
  let e := Equiv.optionEquivSumPUnit.{0} α
  let l : (⨂[K] i, B i) ≃ₗ[K] (⨂[K] i : α, B (some i)) ⊗[K] B none :=
    (reindex K B e).trans ((tmulEquivDep K (fun j => B (e.symm j))).symm.trans
      (TensorProduct.congr (LinearEquiv.refl K _)
        (subsingletonEquiv (R := K) (s := fun j : PUnit => B (e.symm (Sum.inr j))) PUnit.unit)))
  have hl : ∀ f : ∀ i, B i, l (tprod K f) = tprod K (fun i => f (some i)) ⊗ₜ f none := by
    intro f
    simp only [l, LinearEquiv.trans_apply, reindex_tprod, tmulEquivDep_symm_apply]
    exact congrArg (TensorProduct.tmul K _)
      (subsingletonEquiv_apply_tprod (R := K) (s := fun j : PUnit => B (e.symm (Sum.inr j)))
        PUnit.unit _)
  let φ : MultilinearMap K B ((⨂[K] i : α, B (some i)) ⊗[K] B none) :=
    l.toLinearMap.compMultilinearMap (tprod K)
  have hφ : ∀ f, φ f = tprod K (fun i => f (some i)) ⊗ₜ f none := fun f => hl f
  let F := liftAlgHom φ
    (by rw [hφ]; rfl)
    (fun x y => by
      rw [hφ, hφ, hφ, Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod]
      rfl)
  have hF : F.toLinearMap = l.toLinearMap := by
    refine PiTensorProduct.ext ?_
    ext f
    simp [F, φ]
  have hbij : Function.Bijective F := by
    have : (F : (⨂[K] i, B i) → _) = l := congrArg DFunLike.coe hF
    rw [this]
    exact l.bijective
  let G : (⨂[K] i, B i) ≃ₐ[K] (⨂[K] i : α, B (some i)) ⊗[K] B none :=
    AlgEquiv.ofBijective F hbij
  have := Langlands.CentralSimple.isCentral_tensor K (⨂[K] i : α, B (some i)) (B none)
  have := Langlands.CentralSimple.isSimpleRing_tensor K (⨂[K] i : α, B (some i)) (B none)
  exact ⟨Algebra.IsCentral.of_algEquiv K _ _ G.symm,
    IsSimpleRing.of_ringEquiv G.symm.toRingEquiv inferInstance⟩

/-- A finite tensor product of finite-dimensional central simple algebras is central simple. -/
theorem piTensor_isCentral_isSimpleRing {ι : Type w} [Finite ι] (B : ι → Type v)
    [∀ i, Ring (B i)] [∀ i, Algebra K (B i)] [∀ i, FiniteDimensional K (B i)]
    [∀ i, Algebra.IsCentral K (B i)] [∀ i, IsSimpleRing (B i)] :
    Algebra.IsCentral K (⨂[K] i, B i) ∧ IsSimpleRing (⨂[K] i, B i) :=
  Finite.induction_empty_option (P := PiCentralSimple.{u₁, v} K)
    (fun e h => piCentralSimple_of_equiv K e h) (piCentralSimple_empty K)
    (fun h => piCentralSimple_option K h) ι B

end PiTensorCSA

section Conj

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable (A : Type u₄) [Ring A] [Algebra L A]

variable [FiniteDimensional L A] [Algebra.IsCentral L A] [IsSimpleRing A]

instance conj_isSimpleRing (σ : L →ₐ[K] N) : IsSimpleRing (Conj A σ) :=
  Langlands.CentralSimple.isSimpleRing_baseChange L A (Twist σ)

instance conj_isCentral (σ : L →ₐ[K] N) : Algebra.IsCentral N (Conj A σ) := by
  have h := Langlands.CentralSimple.isCentral_baseChange L A (Twist σ)
  refine ⟨fun z hz => ?_⟩
  have hz' : z ∈ Subalgebra.center (Twist σ) (Conj A σ) := by
    rw [Subalgebra.mem_center_iff] at hz ⊢
    exact hz
  obtain ⟨x, hx⟩ := Algebra.mem_bot.mp (h.out hz')
  exact Algebra.mem_bot.mpr ⟨x, hx⟩

end Conj

section Tensor

variable (K : Type u₁) (L : Type u₂) (N : Type u₃) [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable (A : Type u₄) [Ring A] [Algebra L A]
variable [FiniteDimensional K L] [FiniteDimensional L A] [Algebra.IsCentral L A] [IsSimpleRing A]

instance conjTensor_finiteDimensional : FiniteDimensional N (ConjTensor K L N A) :=
  PiTensorProduct.finite

theorem conjTensor_isCentral : Algebra.IsCentral N (ConjTensor K L N A) :=
  (piTensor_isCentral_isSimpleRing N (fun σ : L →ₐ[K] N => Conj A σ)).1

theorem conjTensor_isSimpleRing : IsSimpleRing (ConjTensor K L N A) :=
  (piTensor_isCentral_isSimpleRing N (fun σ : L →ₐ[K] N => Conj A σ)).2

variable [FiniteDimensional K N] [IsGalois K N]

omit [Algebra.IsCentral L A] [IsSimpleRing A] [IsGalois K N] in
/-- The tensor-descent algebra is finite-dimensional over `K`. -/
theorem finiteDimensional_corAlg : FiniteDimensional K (corAlg K L N A) :=
  (galAction K L N A).finiteDimensional_fixedSubalgebra

/-- The tensor-descent algebra is central over `K`. -/
theorem isCentral_corAlg : Algebra.IsCentral K (corAlg K L N A) := by
  have := conjTensor_isCentral K L N A
  have := conjTensor_isSimpleRing K L N A
  exact (galAction K L N A).isCentral_fixedSubalgebra

/-- The tensor-descent algebra is a simple ring. -/
theorem isSimpleRing_corAlg : IsSimpleRing (corAlg K L N A) := by
  have := conjTensor_isSimpleRing K L N A
  exact (galAction K L N A).isSimpleRing_fixedSubalgebra

end Tensor

end Langlands.BrauerCorestriction
