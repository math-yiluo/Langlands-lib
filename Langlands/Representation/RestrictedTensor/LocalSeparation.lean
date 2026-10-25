import Langlands.Representation.RestrictedTensor.Action
import Langlands.Representation.RestrictedTensor.Separation
import Mathlib.RepresentationTheory.Intertwining

/-! # Generic local separation of restricted tensor representations -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uG uV

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI}
variable {V : ι → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- A pure finite-stage tensor with every coordinate nonzero is nonzero,
including the tensor indexed by the empty finite set. -/
theorem stage_tprod_ne_zero (S : Finset ι) (v : ∀ i : S, V i)
    (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod K v ≠ 0 := by
  have hφ (i : S) : ∃ φ : V i →ₗ[K] K, φ (v i) = 1 :=
    Module.Projective.exists_dual_eq_one K (hv i)
  choose φ hφ using hφ
  let f : Stage K V S →ₗ[K] K :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K S K).compLinearMap φ)
  have hf : f (PiTensorProduct.tprod K v) = 1 := by simp [f, hφ]
  intro hz
  rw [hz, map_zero] at hf
  exact zero_ne_one hf

/-- Nonzero reference vectors outside the exceptional set and nontrivial local
spaces make the actual restricted tensor space nontrivial. -/
theorem space_nontrivial [∀ i, Nontrivial (V i)] (E : Finset ι) (e : ∀ i, V i)
    (hne : ∀ i ∉ E, e i ≠ 0) : Nontrivial (Space K V E e) := by
  choose v hv using (fun i : E => exists_ne (0 : V i))
  have hstage := stage_tprod_ne_zero (K := K) E v hv
  have hnonzero : of K V E e ⟨E, le_rfl⟩ (PiTensorProduct.tprod K v) ≠ 0 := by
    intro hz
    apply hstage
    apply of_injective E e hne ⟨E, le_rfl⟩
    simpa only [map_zero] using hz
  exact ⟨⟨_, 0, hnonzero⟩⟩

/-- The nonzero-reference version of restricted tensor nontriviality. -/
theorem product_nontrivial [∀ i, Nontrivial (V i)] (E : Finset ι)
    (r : ReferenceVectors V E) : Nontrivial (Product K V E r) :=
  space_nontrivial E r.family r.family_nonzero

/-- The complementary restricted tensor, retaining every exceptional index
other than the separated index. -/
abbrev LocalTensorTail (E : Finset ι) (i : ι) (e : ∀ j, V j) :=
  Space K (fun j : Outside {i} => V j) (tailSet {i} E) (fun j => e j)

/-- The complementary tensor space is nontrivial, also when its index type is empty. -/
theorem localTensorTail_nontrivial [∀ j, Nontrivial (V j)]
    (E : Finset ι) (i : ι) (e : ∀ j, V j) (hne : ∀ j ∉ E, e j ≠ 0) :
    Nontrivial (LocalTensorTail (K := K) E i e) :=
  space_nontrivial (tailSet {i} E) (fun j : Outside {i} => e j)
    (fun j hj => hne j (fun hjE => hj ((mem_tailSet {i} E j).mpr hjE)))

variable {G : ι → Type uG} [∀ i, Group (G i)]

/-- Insert one local group element into the actual cofinite restricted product. -/
def localInsertion (H : ∀ i, Subgroup (G i)) (i : ι) :
    G i →* RestrictedGroup G H :=
  RestrictedProduct.mulSingleMonoidHom H i

@[simp]
theorem localInsertion_same (H : ∀ i, Subgroup (G i)) (i : ι) (g : G i) :
    localInsertion H i g i = g :=
  RestrictedProduct.mulSingle_eq_same H i g

@[simp]
theorem localInsertion_of_ne (H : ∀ i, Subgroup (G i)) (i : ι) (g : G i)
    {j : ι} (hji : j ≠ i) : localInsertion H i g j = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne H g hji

/-- The insertion is faithful on its local group. -/
theorem localInsertion_injective (H : ∀ i, Subgroup (G i)) (i : ι) :
    Function.Injective (localInsertion H i) :=
  RestrictedProduct.mulSingle_injective H i

/-- On the separated space, the local group acts on its own factor and trivially
on the complementary restricted tensor. -/
def separatedLocalRepresentation (ρ : ∀ i, Representation K (G i) (V i))
    (E : Finset ι) (i : ι) (e : ∀ j, V j) :
    Representation K (G i) (V i ⊗[K] LocalTensorTail (K := K) E i e) :=
  (ρ i).tprod (Representation.trivial K (G i) (LocalTensorTail (K := K) E i e))

@[simp]
theorem separatedLocalRepresentation_tmul (ρ : ∀ i, Representation K (G i) (V i))
    (E : Finset ι) (i : ι) (e : ∀ j, V j) (g : G i)
    (x : V i) (y : LocalTensorTail (K := K) E i e) :
    separatedLocalRepresentation ρ E i e g (x ⊗ₜ[K] y) = ρ i g x ⊗ₜ[K] y := rfl

/-- Restriction of the constructed restricted-product representation along insertion. -/
def tensorLocalRepresentation (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i) (i : ι) :
    Representation K (G i) (Space K V E e) :=
  (representation H ρ E e he).comp (localInsertion H i)

/-- The published algebraic local separation intertwines insertion with the
local action on the first tensor factor. -/
theorem localSeparation_intertwines (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (hne : ∀ i ∉ E, e i ≠ 0) (i : ι) (g : G i) :
    (localSeparation E i e hne).toLinearMap.comp
        (representation H ρ E e he (localInsertion H i g)) =
      (separatedLocalRepresentation ρ E i e g).comp
        (localSeparation E i e hne).toLinearMap := by
  apply hom_ext_cofinal {i}
  intro S hS v
  have hi : i ∈ S.1 := hS (Finset.mem_singleton_self i)
  have hg : ∀ j ∉ S.1, localInsertion H i g j ∈ H j := by
    intro j hj
    rw [localInsertion_of_ne H i g (fun h : j = i => hj (h.symm ▸ hi))]
    exact (H j).one_mem
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [representation_pure_of_mem H ρ E e he _ S hg]
  rw [localSeparation_pure E i e hne S hi, localSeparation_pure E i e hne S hi,
    separatedLocalRepresentation_tmul, localInsertion_same]
  congr 2
  funext j
  have hji : j.1.1 ≠ i := fun h => j.1.2 (Finset.mem_singleton.mpr h)
  simp [localInsertion_of_ne H i g hji]

/-- Genuine representation equivalence exposing one factor of the actual
restricted tensor representation. -/
def localTensorSeparation (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (hne : ∀ i ∉ E, e i ≠ 0) (i : ι) :
    (tensorLocalRepresentation H ρ E e he i).Equiv
      (separatedLocalRepresentation ρ E i e) :=
  Representation.Equiv.mk (localSeparation E i e hne)
    (localSeparation_intertwines H ρ E e he hne i)

@[simp]
theorem localTensorSeparation_pure (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (hne : ∀ i ∉ E, e i ≠ 0) (i : ι) (S : Index E) (hi : i ∈ S.1)
    (v : ∀ j : S.1, V j) :
    localTensorSeparation H ρ E e he hne i (pure E e S v) =
      v ⟨i, hi⟩ ⊗ₜ[K]
        pure (tailSet {i} E) (fun j : Outside {i} => e j)
          ⟨tailSet {i} S.1, tailSet_mono {i} S.2⟩
          (fun j => v ⟨j.1.1, Finset.mem_subtype.mp j.2⟩) :=
  localSeparation_pure E i e hne S hi v

/-- Insertion after reassembly changes only the exposed local factor. -/
theorem tensorLocalRepresentation_reassemble (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
    (hne : ∀ i ∉ E, e i ≠ 0) (i : ι) (g : G i)
    (x : V i) (y : LocalTensorTail (K := K) E i e) :
    tensorLocalRepresentation H ρ E e he i g
        ((localTensorSeparation H ρ E e he hne i).symm (x ⊗ₜ[K] y)) =
      (localTensorSeparation H ρ E e he hne i).symm (ρ i g x ⊗ₜ[K] y) := by
  let q := localTensorSeparation H ρ E e he hne i
  exact (LinearMap.congr_fun (q.symm.isIntertwining' g) (x ⊗ₜ[K] y)).symm

/-- The same equivalence for the nonzero-reference product representation. -/
def productLocalTensorSeparation (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation K (G i) (V i)) (E : Finset ι) (r : ReferenceVectors V E)
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi)
    (i : ι) :
    Representation.Equiv ((productRepresentation H ρ E r hr).comp (localInsertion H i))
      (separatedLocalRepresentation ρ E i r.family) :=
  localTensorSeparation H ρ E r.family
    (fun j hj g hg => by
      simpa only [ReferenceVectors.family_of_not_mem r hj] using hr j hj g hg)
    r.family_nonzero i

end Langlands.RestrictedTensor
