import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Simple subquotients of a tensor product with a multiplicity space -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands

private theorem exists_nonzero_subquotient_of_coordinates
    {𝕜 : Type*} [Field 𝕜] {α ι V E Q : Type*}
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup Q] [Module 𝕜 Q]
    (source : ι → Module.End 𝕜 V) (act : ι → Module.End 𝕜 E)
    (target : ι → Module.End 𝕜 Q)
    (coordinates : E →ₗ[𝕜] α →₀ V) (hinj : Function.Injective coordinates)
    (hcoord : ∀ a z j, coordinates (act a z) j = source a (coordinates z j))
    (q : E →ₗ[𝕜] Q) (hq : ∀ a z, q (act a z) = target a (q z))
    {J : Submodule 𝕜 Q} (hJq : J ≤ LinearMap.range q) (hJ0 : J ≠ ⊥)
    (hJs : ∀ a x, x ∈ J → target a x ∈ J) :
    ∃ (W : Submodule 𝕜 V) (A : W →ₗ[𝕜] Q),
      LinearMap.range A ≤ J ∧ LinearMap.range A ≠ ⊥ ∧
      ∀ a (w : W), ∃ hw : source a w.val ∈ W, A ⟨_, hw⟩ = target a (A w) := by
  classical
  obtain ⟨y, hyJ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
  obtain ⟨z, rfl⟩ := hJq hyJ
  have hex : ∃ d : ℕ, ∃ x : E, q x ∈ J ∧ q x ≠ 0 ∧
      (coordinates x).support.card = d := ⟨_, z, hyJ, hy0, rfl⟩
  obtain ⟨x, hxJ, hx0, hxcard⟩ := Nat.find_spec hex
  have hcoords0 : coordinates x ≠ 0 := by
    intro h
    have hx : x = 0 := hinj (h.trans (map_zero _).symm)
    exact hx0 (by rw [hx, map_zero])
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hcoords0
  let Z : Submodule 𝕜 E := J.comap q ⊓
    (Finsupp.supported V 𝕜 (coordinates x).support).comap coordinates
  have hxZ : x ∈ Z := ⟨hxJ, Finsupp.mem_supported_support 𝕜 (coordinates x)⟩
  have hsupport (z : Z) : (coordinates z.val).support ⊆ (coordinates x).support :=
    Finset.coe_subset.mp ((Finsupp.mem_supported 𝕜 (coordinates z.val)).mp z.2.2)
  have hZ (a : ι) (z : Z) : act a z.val ∈ Z := by
    refine ⟨?_, ?_⟩
    · change q (act a z.val) ∈ J
      rw [hq]
      exact hJs a _ z.2.1
    · change coordinates (act a z.val) ∈ Finsupp.supported V 𝕜 (coordinates x).support
      apply (Finsupp.mem_supported 𝕜 _).mpr
      apply Finset.coe_subset.mpr
      intro i hi
      apply hsupport z
      rw [Finsupp.mem_support_iff] at hi ⊢
      rw [hcoord] at hi
      exact fun h => hi (by rw [h, map_zero])
  let pr : Z →ₗ[𝕜] V := (Finsupp.lapply j).comp (coordinates.comp Z.subtype)
  let g : Z →ₗ[𝕜] Q := q.comp Z.subtype
  have hker : LinearMap.ker pr ≤ LinearMap.ker g := by
    intro z hz
    change coordinates z.val j = 0 at hz
    change q z.val = 0
    by_contra hne
    have hstrict : (coordinates z.val).support ⊂ (coordinates x).support := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsupport z, ?_⟩
      intro heq
      exact (Finsupp.notMem_support_iff.mpr hz) (heq.symm ▸ hj)
    have hlt := Finset.card_lt_card hstrict
    rw [hxcard] at hlt
    exact Nat.find_min hex hlt ⟨z.val, z.2.1, hne, rfl⟩
  let A : LinearMap.range pr →ₗ[𝕜] Q :=
    ((LinearMap.ker pr).liftQ g hker).comp pr.quotKerEquivRange.symm.toLinearMap
  have hA (z : Z) : A (pr.rangeRestrict z) = q z.val := by
    change A ⟨pr z, LinearMap.mem_range_self pr z⟩ = q z.val
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hAop (a : ι) (w : LinearMap.range pr) :
      ∃ hw : source a w.val ∈ LinearMap.range pr, A ⟨_, hw⟩ = target a (A w) := by
    obtain ⟨z, rfl⟩ := pr.surjective_rangeRestrict w
    let az : Z := ⟨act a z.val, hZ a z⟩
    have hp : pr az = source a (pr.rangeRestrict z).val := hcoord a z.val j
    have hw : source a (pr.rangeRestrict z).val ∈ LinearMap.range pr :=
      LinearMap.mem_range.mpr ⟨az, hp⟩
    refine ⟨hw, ?_⟩
    rw [show (⟨source a (pr.rangeRestrict z).val, hw⟩ : LinearMap.range pr) =
      pr.rangeRestrict az from Subtype.ext hp.symm, hA, hA]
    exact hq a z.val
  have hAJ : LinearMap.range A ≤ J := by
    intro y hy
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hy
    obtain ⟨z, rfl⟩ := pr.surjective_rangeRestrict w
    rw [hA]
    exact z.2.1
  have hA0 : LinearMap.range A ≠ ⊥ := by
    intro h
    have hxmem : q x ∈ LinearMap.range A :=
      LinearMap.mem_range.mpr ⟨pr.rangeRestrict ⟨x, hxZ⟩, hA ⟨x, hxZ⟩⟩
    rw [h, Submodule.mem_bot] at hxmem
    exact hx0 hxmem
  exact ⟨_, A, hAJ, hA0, hAop⟩

/-- Suppose all source operators on `V ⊗ M` act on `V` alone. A nonzero stable
subspace `J` in the image of an equivariant map from a stable subspace of `V ⊗ M`
contains the nonzero image of an equivariant map from a stable subspace of `V`. -/
def TensorProductNonzeroSubquotientStatement
    (𝕜 : Type*) [Field 𝕜] (ι V M Q : Type*)
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup Q] [Module 𝕜 Q] : Prop :=
  ∀ (source : ι → Module.End 𝕜 V) (target : ι → Module.End 𝕜 Q)
    {S : Submodule 𝕜 (V ⊗[𝕜] M)} (q : S →ₗ[𝕜] Q)
    (hS : ∀ a (z : S), TensorProduct.map (source a) LinearMap.id z.val ∈ S),
    (∀ a (z : S), q ⟨_, hS a z⟩ = target a (q z)) →
    ∀ {J : Submodule 𝕜 Q}, J ≤ LinearMap.range q → J ≠ ⊥ →
    (∀ a x, x ∈ J → target a x ∈ J) →
    ∃ (W : Submodule 𝕜 V) (A : W →ₗ[𝕜] Q),
      LinearMap.range A ≤ J ∧ LinearMap.range A ≠ ⊥ ∧
      ∀ a (w : W), ∃ hw : source a w.val ∈ W, A ⟨_, hw⟩ = target a (A w)

/-- Suppose all source operators on `V ⊗ M` act on `V` alone. A nonzero irreducible
stable subspace `J` in the image of an equivariant map from a stable subspace of
`V ⊗ M` is the image of an equivariant map from a stable subspace of `V`. -/
def TensorProductSubquotientStatement
    (𝕜 : Type*) [Field 𝕜] (ι V M Q : Type*)
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup Q] [Module 𝕜 Q] : Prop :=
  ∀ (source : ι → Module.End 𝕜 V) (target : ι → Module.End 𝕜 Q)
    {S : Submodule 𝕜 (V ⊗[𝕜] M)} (q : S →ₗ[𝕜] Q)
    (hS : ∀ a (z : S), TensorProduct.map (source a) LinearMap.id z.val ∈ S),
    (∀ a (z : S), q ⟨_, hS a z⟩ = target a (q z)) →
    ∀ {J : Submodule 𝕜 Q}, J ≤ LinearMap.range q → J ≠ ⊥ →
    (∀ a x, x ∈ J → target a x ∈ J) →
    (∀ U : Submodule 𝕜 Q, U ≤ J →
      (∀ a x, x ∈ U → target a x ∈ U) → U = ⊥ ∨ U = J) →
    ∃ (W : Submodule 𝕜 V) (A : W →ₗ[𝕜] Q), LinearMap.range A = J ∧
      ∀ a (w : W), ∃ hw : source a w.val ∈ W, A ⟨_, hw⟩ = target a (A w)

/-- Extract a nonzero subquotient by evaluating a coordinate of minimum support. -/
theorem exists_nonzero_subquotient_of_tensorProduct
    {𝕜 : Type*} [Field 𝕜] {ι V M Q : Type*}
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup Q] [Module 𝕜 Q] : TensorProductNonzeroSubquotientStatement 𝕜 ι V M Q := by
  intro source target S q hS hq J hJq hJ0 hJs
  let coordinates : V ⊗[𝕜] M ≃ₗ[𝕜] Module.Free.ChooseBasisIndex 𝕜 M →₀ V :=
    TensorProduct.equivFinsuppOfBasisRight (Module.Free.chooseBasis 𝕜 M)
  let act (a : ι) : Module.End 𝕜 S :=
    ((TensorProduct.map (source a) LinearMap.id).comp S.subtype).codRestrict S (hS a)
  have hcoord (a : ι) (z : V ⊗[𝕜] M) (j : Module.Free.ChooseBasisIndex 𝕜 M) :
      coordinates (TensorProduct.map (source a) LinearMap.id z) j =
        source a (coordinates z j) := by
    induction z using TensorProduct.inductionOn with
    | tmul v m =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, coordinates,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add z z' hz hz' => simp only [map_add, Finsupp.add_apply, hz, hz']
  exact exists_nonzero_subquotient_of_coordinates source act target
    (coordinates.toLinearMap.comp S.subtype) (coordinates.injective.comp Subtype.val_injective)
    (fun a z j => hcoord a z.val j) q hq hJq hJ0 hJs

/-- Extract an irreducible subquotient by evaluating a coordinate of minimum support. -/
theorem exists_subquotient_of_tensorProduct
    {𝕜 : Type*} [Field 𝕜] {ι V M Q : Type*}
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup Q] [Module 𝕜 Q] : TensorProductSubquotientStatement 𝕜 ι V M Q := by
  intro source target S q hS hq J hJq hJ0 hJs hJirr
  obtain ⟨W, A, hAJ, hA0, hAop⟩ :=
    exists_nonzero_subquotient_of_tensorProduct source target q hS hq hJq hJ0 hJs
  have hAs (a : ι) (y : Q) (hy : y ∈ LinearMap.range A) :
      target a y ∈ LinearMap.range A := by
    obtain ⟨w, rfl⟩ := hy
    obtain ⟨hw, heq⟩ := hAop a w
    exact ⟨⟨_, hw⟩, heq⟩
  exact ⟨W, A, (hJirr _ hAJ hAs).resolve_left hA0, hAop⟩

end Langlands
