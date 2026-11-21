import Langlands.Automorphic.UnitaryContragredientCriterion
import Langlands.Representation.Tensor.Finite
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Joint admissibility of finite external tensors

Contraction in all but one slot turns a joint multiplicity map for the
external tensor into a multiplicity map for the selected block. The ranges
of the block maps bound the range of the original map.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace Langlands.FiniteTensor

open Module

variable {ι : Type*} [Fintype ι] [dec : DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

omit [Fintype ι] in
private theorem prod_apply_update (ell : ∀ j, V j →ₗ[ℂ] ℂ)
    (s : Finset ι) (j : ι) (v : ∀ k, V k) (z : V j) :
    (∏ k ∈ s, ell k (Function.update v j z k)) =
      ∏ k ∈ s, Function.update (fun k => ell k (v k)) j (ell j z) k := by
  have h := Pi.map_update (f := fun k => (ell k : V k → ℂ)) v j z
  exact congrArg (fun g : ι → ℂ => ∏ k ∈ s, g k) h

/-- Contract each factor except slot `i` against a specified linear functional. -/
def slotContraction (i : ι) (ell : ∀ j, V j →ₗ[ℂ] ℂ) : (⨂[ℂ] j, V j) →ₗ[ℂ] V i :=
  PiTensorProduct.lift {
    toFun := fun v => (∏ j ∈ Finset.univ.erase i, ell j (v j)) • v i
    map_update_add' := by
      intro d v j a b
      have hd : d = dec := Subsingleton.elim _ _
      subst d
      simp only [prod_apply_update]
      by_cases h : j = i
      · subst j
        simp only [Finset.prod_update_of_notMem (Finset.notMem_erase _ _),
          Function.update_self, smul_add]
      · have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
        simp only [Finset.prod_update_of_mem hj, Function.update_of_ne (Ne.symm h),
          map_add, add_mul, add_smul]
    map_update_smul' := by
      intro d v j c a
      have hd : d = dec := Subsingleton.elim _ _
      subst d
      simp only [prod_apply_update]
      by_cases h : j = i
      · subst j
        simp only [Finset.prod_update_of_notMem (Finset.notMem_erase _ _), Function.update_self]
        exact smul_comm _ _ _
      · have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
        simp only [Finset.prod_update_of_mem hj, Function.update_of_ne (Ne.symm h),
          map_smul, smul_eq_mul, smul_smul, mul_assoc] }

@[simp]
theorem slotContraction_tprod (i : ι) (ell : ∀ j, V j →ₗ[ℂ] ℂ) (v : ∀ j, V j) :
    slotContraction i ell (PiTensorProduct.tprod ℂ v) =
      (∏ j ∈ Finset.univ.erase i, ell j (v j)) • v i :=
  PiTensorProduct.lift.tprod _

/-- Contracting away the other factors intertwines the action supported in slot `i`. -/
theorem slotContraction_external_single {G : ι → Type*} [∀ j, Group (G j)]
    (ρ : ∀ j, Representation ℂ (G j) (V j)) (i : ι) (ell : ∀ j, V j →ₗ[ℂ] ℂ)
    (g : G i) (t : ⨂[ℂ] j, V j) :
    slotContraction i ell (external ρ (Pi.mulSingle i g) t) = ρ i g (slotContraction i ell t) := by
  suffices h : slotContraction i ell ∘ₗ external ρ (Pi.mulSingle i g) =
      ρ i g ∘ₗ slotContraction i ell from LinearMap.congr_fun h t
  apply PiTensorProduct.ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, external_tprod,
    slotContraction_tprod, Pi.mulSingle_eq_same, map_smul]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Pi.mulSingle_eq_of_ne (Finset.mem_erase.mp hj).1, map_one, Module.End.one_apply]

private theorem coord_slotContraction {κ : ι → Type*} (b : ∀ i, Basis (κ i) ℂ (V i))
    (p : ∀ i, κ i) (i : ι) (t : ⨂[ℂ] j, V j) :
    (b i).coord (p i) (slotContraction i (fun j => (b j).coord (p j)) t) =
      (Basis.piTensorProduct b).repr t p := by
  suffices h : (b i).coord (p i) ∘ₗ slotContraction i (fun j => (b j).coord (p j)) =
      (Basis.piTensorProduct b).coord p from LinearMap.congr_fun h t
  apply PiTensorProduct.ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    slotContraction_tprod, map_smul, smul_eq_mul, Basis.coord_apply,
    Basis.piTensorProduct_repr_tprod_apply]
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

/-- If the contractions in each slot belong to its designated subspace, the tensor
belongs to the image of the tensor product of those subspaces. -/
theorem mem_blockTensorRange_of_slotContractions (U : ∀ i, Submodule ℂ (V i))
    (t : ⨂[ℂ] j, V j)
    (ht : ∀ i (ell : ∀ j, V j →ₗ[ℂ] ℂ), slotContraction i ell t ∈ U i) :
    t ∈ LinearMap.range (PiTensorProduct.map (fun i => (U i).subtype)) := by
  classical
  choose C hC using fun i => (U i).exists_isCompl
  let bU i := Basis.ofVectorSpace ℂ (U i)
  let bC i := Basis.ofVectorSpace ℂ (C i)
  let b i := ((bU i).prod (bC i)).map ((U i).prodEquivOfIsCompl (C i) (hC i))
  let B := Basis.piTensorProduct b
  have hinl : ∀ i a, b i (Sum.inl a) = ((bU i a : U i) : V i) := by
    intro i a
    simp [b]
  have hcoord : ∀ i z (x : V i), x ∈ U i → (b i).coord (Sum.inr z) x = 0 := by
    intro i z x hx
    let y : U i := ⟨x, hx⟩
    change (b i).repr ((y : U i) : V i) (Sum.inr z) = 0
    simp [b]
  rw [← B.linearCombination_repr t, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro p hp
  have hleft (i : ι) : ∃ a, p i = Sum.inl a := by
    cases hpi : p i with
    | inl a => exact ⟨a, rfl⟩
    | inr z =>
      have h := coord_slotContraction b p i t
      rw [hpi, hcoord i z _ (ht i _)] at h
      exact False.elim ((Finsupp.mem_support_iff.mp hp) h.symm)
  choose a ha using hleft
  apply Submodule.smul_mem
  refine ⟨PiTensorProduct.tprod ℂ (fun i => bU i (a i)), ?_⟩
  rw [PiTensorProduct.map_tprod, Basis.piTensorProduct_apply]
  exact congrArg (PiTensorProduct.tprod ℂ) (funext fun i => by simp only [ha i, hinl]; rfl)

section Admissibility

variable {G K : ι → Type*} [∀ i, Group (G i)] [∀ i, Group (K i)] [∀ i, TopologicalSpace (G i)]
  (ρ : ∀ i, Representation ℂ (G i) (V i)) (κ : ∀ i, Representation ℂ (K i) (V i))

/-- For an arbitrary open product-group level, pull back along each coordinate
inclusion. Restrict the compact test along the compact coordinate inclusion. -/
theorem isJointlyAdmissible_external (h : ∀ i, IsJointlyAdmissible (ρ i) (κ i)) :
    IsJointlyAdmissible (external ρ) (external κ) := by
  intro L m σ
  let L' i := OpenSubgroup.comap (MonoidHom.mulSingle G i) (continuous_mulSingle i) L
  let σ' i := σ.comp (MonoidHom.mulSingle K i)
  let A i := jointMultiplicitySpace (ρ i) (κ i) (L' i).toSubgroup (σ' i)
  let E := Fin m → ℂ
  let U i : Submodule ℂ (V i) := ⨆ a : Fin m, (A i).map (LinearMap.applyₗ (Pi.basisFun ℂ (Fin m) a))
  have (i : ι) : FiniteDimensional ℂ (U i) := by
    have : FiniteDimensional ℂ (A i) := h i (L' i) m (σ' i)
    have (a : Fin m) : FiniteDimensional ℂ ((A i).map (LinearMap.applyₗ (Pi.basisFun ℂ (Fin m) a))) :=
      Module.Finite.map _ _
    exact Submodule.finiteDimensional_iSup _
  have hU (i : ι) (ψ : A i) (v : E) : ψ.val v ∈ U i := by
    let b := Pi.basisFun ℂ (Fin m)
    rw [← b.sum_repr v, map_sum]
    apply Submodule.sum_mem
    intro a _
    rw [map_smul]
    exact (U i).smul_mem _ (Submodule.mem_iSup_of_mem a ⟨ψ.val, ψ.property, rfl⟩)
  let A₀ := jointMultiplicitySpace (external ρ) (external κ) L.toSubgroup σ
  let S := LinearMap.range (PiTensorProduct.map (fun i => (U i).subtype))
  have : FiniteDimensional ℂ S := Module.Finite.range _
  have hS (φ : A₀) (v : E) : φ.val v ∈ S := by
    apply mem_blockTensorRange_of_slotContractions
    intro i ell
    let D := slotContraction i ell
    let ψ : A i := ⟨D ∘ₗ φ.val, ⟨fun w d => ?_, fun k w => ?_⟩⟩
    · exact hU i ψ v
    · have hd : Pi.mulSingle i (d : G i) ∈ L := d.property
      change ρ i (d : G i) (D (φ.val w)) = D (φ.val w)
      rw [← slotContraction_external_single ρ]
      exact congrArg D (φ.property.1 w ⟨_, hd⟩)
    · change D (φ.val (σ (Pi.mulSingle i k) w)) = κ i k (D (φ.val w))
      rw [φ.property.2]
      exact slotContraction_external_single κ i ell k (φ.val w)
  let R : A₀ →ₗ[ℂ] (E →ₗ[ℂ] S) := {
    toFun := fun φ => φ.val.codRestrict S (hS φ)
    map_add' := fun _ _ => LinearMap.ext fun _ => Subtype.ext rfl
    map_smul' := fun _ _ => LinearMap.ext fun _ => Subtype.ext rfl }
  exact Module.Finite.of_injective R fun φ ψ hφψ => Subtype.ext <|
    LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun hφψ v)

end Admissibility

end Langlands.FiniteTensor
