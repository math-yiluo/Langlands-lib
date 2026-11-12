import Langlands.Representation.CompactCoefficient.CompactFormalDegreeStatements
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.Renard.CompactRepresentation

section Tensor

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The rank-one map on the tensor product with the smooth dual. -/
def smoothEndomorphismTensorMap (ρ : Representation ℂ G V) :
    V ⊗[ℂ] SmoothDual ρ →ₗ[ℂ] Module.End ℂ V :=
  TensorProduct.lift
    ((LinearMap.smulRightₗ (R := ℂ) (M := V) (M₂ := V)).flip.compl₂
      (smoothVectors ρ.dual).subtype)

@[simp] theorem smoothEndomorphismTensorMap_tmul (ρ : Representation ℂ G V)
    (w : V) (ℓ : SmoothDual ρ) (x : V) :
    smoothEndomorphismTensorMap ρ (w ⊗ₜ ℓ) x = ℓ.val x • w := rfl

/-- The rank-one tensor map is injective, without an admissibility assumption. -/
theorem smoothEndomorphismTensorMap_injective (ρ : Representation ℂ G V) :
    Function.Injective (smoothEndomorphismTensorMap ρ) := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := SmoothDual ρ) b
  have heval (t : V ⊗[ℂ] SmoothDual ρ) (i) (x : V) :
      (E t i).val x = b.coord i (smoothEndomorphismTensorMap ρ t x) := by
    induction t using TensorProduct.inductionOn with
    | tmul w ℓ =>
        simp [E, smoothEndomorphismTensorMap_tmul, mul_comm]
    | add t s ht hs => simp [ht, hs]
  intro t s hts
  apply E.injective
  ext i x
  rw [heval, heval, hts]

/-- The tensor map has exactly the endomorphisms fixed on both sides by an
open subgroup as its image, for every admissible representation. -/
theorem smoothEndomorphismTensorMap_range (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) :
    Set.range (smoothEndomorphismTensorMap ρ) =
      {A : Module.End ℂ V | ∃ K : OpenSubgroup G, ∀ k₁ ∈ K, ∀ k₂ ∈ K,
        ρ k₁ * A * ρ k₂ = A} := by
  classical
  ext A
  constructor
  · rintro ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul w ℓ =>
        obtain ⟨K, hK⟩ := hρ.1 w
        obtain ⟨J, hJ⟩ := ℓ.property
        refine ⟨K ⊓ J, ?_⟩
        intro k₁ hk₁ k₂ hk₂
        apply LinearMap.ext
        intro x
        have hℓ : ℓ.val (ρ k₂ x) = ℓ.val x := by
          have h := congrArg (fun f : Module.Dual ℂ V => f x)
            (hJ ⟨k₂⁻¹, J.inv_mem hk₂.2⟩)
          change ℓ.val (ρ (k₂⁻¹)⁻¹ x) = ℓ.val x at h
          simpa only [inv_inv] using h
        change ρ k₁ (ℓ.val (ρ k₂ x) • w) = ℓ.val x • w
        have hw : ρ k₁ w = w := hK ⟨k₁, hk₁.1⟩
        rw [map_smul, hℓ, hw]
    | add t s ht hs =>
        obtain ⟨K, hK⟩ := ht
        obtain ⟨J, hJ⟩ := hs
        refine ⟨K ⊓ J, ?_⟩
        intro k₁ hk₁ k₂ hk₂
        rw [map_add, mul_add, add_mul, hK k₁ hk₁.1 k₂ hk₂.1,
          hJ k₁ hk₁.2 k₂ hk₂.2]
  · rintro ⟨K, hK⟩
    have hleft (k : K) (x : V) : ρ k (A x) = A x := by
      have h := LinearMap.congr_fun (hK k k.property 1 K.one_mem) x
      simpa using h
    have hright (k : K) (x : V) : A (ρ k x) = A x := by
      have h := LinearMap.congr_fun (hK 1 K.one_mem k k.property) x
      simpa using h
    let F : V →ₗ[ℂ] fixedVectors ρ K.toSubgroup :=
      A.codRestrict _ (by intro x k; exact hleft k x)
    let : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
    let b := Module.finBasis ℂ (fixedVectors ρ K.toSubgroup)
    let ℓ (i : Fin (Module.finrank ℂ (fixedVectors ρ K.toSubgroup))) : SmoothDual ρ :=
      ⟨(b.coord i).comp F, K, fun k => by
        apply LinearMap.ext
        intro x
        change b.coord i (F (ρ (k : G)⁻¹ x)) = b.coord i (F x)
        apply congrArg (b.coord i)
        exact Subtype.ext (hright k⁻¹ x)⟩
    refine ⟨∑ i, (b i).val ⊗ₜ[ℂ] ℓ i, ?_⟩
    apply LinearMap.ext
    intro x
    simp only [map_sum, LinearMap.sum_apply, smoothEndomorphismTensorMap_tmul]
    change (∑ i, b.repr (F x) i • (b i).val) = (F x).val
    exact_mod_cast congrArg Subtype.val (b.sum_repr (F x))

end Tensor

/-- Renard IV.1.4.1 for admissible smooth representations. -/
theorem smoothEndomorphismTensor : SmoothEndomorphismTensorStatement.{u, v} := by
  intro G _ _ _ _ _ _ τ hτ
  exact ⟨smoothEndomorphismTensorMap_injective τ.representation,
    smoothEndomorphismTensorMap_range τ.representation hτ⟩

end Langlands.Renard.CompactRepresentation
