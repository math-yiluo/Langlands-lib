import Langlands.Representation.Tensor.CharacterLocalization
import Mathlib.Topology.LocallyConstant.Basic

/-! Coordinate restrictions of characters of a finite product subgroup, and the decomposition
of every such character as the product character of its restrictions. -/

noncomputable section

namespace Langlands.FiniteTensor

universe uR uI uG

variable {R : Type uR} [CommRing R] {ι : Type uI}
variable {H : ι → Type uG} [∀ i, Group (H i)]
variable (U : ∀ i, Subgroup (H i))

section Inclusion

open scoped Classical in
/-- Insertion of the `i`th factor subgroup into the product subgroup: the tuple is `u` in
coordinate `i` and `1` in every other coordinate. -/
def coordinateInclusion (i : ι) : U i →* Subgroup.pi Set.univ U where
  toFun u := ⟨Pi.mulSingle i (u : H i),
    (Subgroup.mulSingle_mem_pi i _).mpr fun _ => u.property⟩
  map_one' := Subtype.ext (Pi.mulSingle_one i)
  map_mul' u v := Subtype.ext (Pi.mulSingle_mul i (u : H i) v)

@[simp] theorem coordinateInclusion_apply_self (i : ι) (u : U i) :
    (coordinateInclusion U i u).val i = u := by
  classical
  exact Pi.mulSingle_eq_same (M := H) i (u : H i)

theorem coordinateInclusion_apply_of_ne {i j : ι} (h : j ≠ i) (u : U i) :
    (coordinateInclusion U i u).val j = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := H) h (u : H i)

/-- The underlying tuple is `Pi.mulSingle`, for every decidable-equality instance. -/
theorem coe_coordinateInclusion [DecidableEq ι] (i : ι) (u : U i) :
    (coordinateInclusion U i u).val = Pi.mulSingle i (u : H i) := by
  funext j
  by_cases h : j = i
  · subst h
    rw [coordinateInclusion_apply_self, Pi.mulSingle_eq_same]
  · rw [coordinateInclusion_apply_of_ne U h, Pi.mulSingle_eq_of_ne h]

/-- The `i`th coordinate of the insertion, as an element of `U i`, is `u`. -/
@[simp] theorem coordinateInclusion_coord_self (i : ι) (u : U i) :
    (⟨(coordinateInclusion U i u).val i,
      (coordinateInclusion U i u).property i (Set.mem_univ i)⟩ : U i) = u :=
  Subtype.ext (coordinateInclusion_apply_self U i u)

/-- Every other coordinate of the insertion, as an element of its subgroup, is `1`. -/
theorem coordinateInclusion_coord_of_ne {i j : ι} (h : j ≠ i) (u : U i) :
    (⟨(coordinateInclusion U i u).val j,
      (coordinateInclusion U i u).property j (Set.mem_univ j)⟩ : U j) = 1 :=
  Subtype.ext (coordinateInclusion_apply_of_ne U h u)

theorem coordinateInclusion_injective (i : ι) : Function.Injective (coordinateInclusion U i) := by
  intro u v huv
  rw [← coordinateInclusion_coord_self U i u, ← coordinateInclusion_coord_self U i v]
  simp only [huv]

end Inclusion

section Character

/-- The restriction of a product-subgroup character to the `i`th coordinate subgroup. -/
def coordinateCharacter (η : Subgroup.pi Set.univ U →* Rˣ) (i : ι) : U i →* Rˣ :=
  η.comp (coordinateInclusion U i)

@[simp] theorem coordinateCharacter_apply (η : Subgroup.pi Set.univ U →* Rˣ) (i : ι) (u : U i) :
    coordinateCharacter U η i u = η (coordinateInclusion U i u) := rfl

variable [Fintype ι]

/-- A product character takes the value of its `i`th factor on the `i`th coordinate subgroup. -/
@[simp] theorem productCharacter_coordinateInclusion (θ : ∀ i, U i →* Rˣ) (i : ι) (u : U i) :
    productCharacter U θ (coordinateInclusion U i u) = θ i u := by
  rw [productCharacter_apply, Finset.prod_eq_single i]
  · rw [coordinateInclusion_coord_self]
  · intro j _ hji
    rw [coordinateInclusion_coord_of_ne U hji, map_one]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Restricting a product character to a coordinate recovers that factor. -/
@[simp] theorem coordinateCharacter_productCharacter (θ : ∀ i, U i →* Rˣ) (i : ι) :
    coordinateCharacter U (productCharacter U θ) i = θ i :=
  MonoidHom.ext (productCharacter_coordinateInclusion U θ i)

/-- Every character of the product subgroup is the product of its coordinate restrictions. -/
@[simp] theorem productCharacter_coordinateCharacter (η : Subgroup.pi Set.univ U →* Rˣ) :
    productCharacter U (coordinateCharacter U η) = η := by
  classical
  refine MonoidHom.ext fun u => ?_
  let piece (s : Finset ι) : Subgroup.pi Set.univ U :=
    ⟨s.piecewise u.val (1 : ∀ j, H j), fun j _ => by
      by_cases hj : j ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hj]
        exact u.property j (Set.mem_univ j)
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hj]
        exact one_mem (U j)⟩
  have key (s : Finset ι) :
      ∏ j ∈ s, coordinateCharacter U η j ⟨u.val j, u.property j (Set.mem_univ j)⟩ =
        η (piece s) := by
    induction s using Finset.induction_on with
    | empty =>
      have h : piece ∅ = 1 := Subtype.ext (Finset.piecewise_empty u.val (1 : ∀ j, H j))
      rw [Finset.prod_empty, h, map_one]
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, ih, coordinateCharacter_apply, ← map_mul]
      congr 1
      apply Subtype.ext
      funext k
      rw [Subgroup.coe_mul, Pi.mul_apply]
      change (coordinateInclusion U j _).val k * s.piecewise u.val 1 k =
        (insert j s).piecewise u.val 1 k
      by_cases hk : k = j
      · subst hk
        rw [coordinateInclusion_apply_self, Finset.piecewise_eq_of_notMem _ _ _ hj,
          Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_self k s), Pi.one_apply, mul_one]
      · rw [coordinateInclusion_apply_of_ne U hk, one_mul, Finset.piecewise_insert_of_ne _ _ _ hk]
  rw [productCharacter_apply, key]
  congr 1
  exact Subtype.ext (Finset.piecewise_univ _ _)

/-- Characters of the product subgroup correspond to tuples of factor characters. -/
def productCharacterEquiv : (∀ i, U i →* Rˣ) ≃ (Subgroup.pi Set.univ U →* Rˣ) where
  toFun := productCharacter U
  invFun := coordinateCharacter U
  left_inv θ := funext (coordinateCharacter_productCharacter U θ)
  right_inv := productCharacter_coordinateCharacter U

@[simp] theorem productCharacterEquiv_apply (θ : ∀ i, U i →* Rˣ) :
    productCharacterEquiv U θ = productCharacter U θ := rfl

@[simp] theorem productCharacterEquiv_symm_apply (η : Subgroup.pi Set.univ U →* Rˣ) :
    (productCharacterEquiv U).symm η = coordinateCharacter U η := rfl

end Character

section Topology

variable [∀ i, TopologicalSpace (H i)]

/-- Coordinate insertion is continuous for the subspace topologies of the product topology. -/
theorem continuous_coordinateInclusion (i : ι) : Continuous (coordinateInclusion U i) := by
  classical
  refine continuous_induced_rng.2 ?_
  have h : (Subtype.val ∘ coordinateInclusion U i) = fun u : U i => Pi.mulSingle i (u : H i) :=
    funext (coe_coordinateInclusion U i)
  rw [h]
  exact (continuous_mulSingle i).comp continuous_subtype_val

/-- Coordinate restrictions of a locally constant `R`-valued character are locally constant. -/
theorem isLocallyConstant_coordinateCharacter {η : Subgroup.pi Set.univ U →* Rˣ}
    (hη : IsLocallyConstant fun u => (η u : R)) (i : ι) :
    IsLocallyConstant fun u => (coordinateCharacter U η i u : R) :=
  hη.comp_continuous (continuous_coordinateInclusion U i)

/-- Coordinate restrictions of a locally constant unit-valued character are locally constant. -/
theorem isLocallyConstant_coordinateCharacter_units {η : Subgroup.pi Set.univ U →* Rˣ}
    (hη : IsLocallyConstant η) (i : ι) : IsLocallyConstant (coordinateCharacter U η i) :=
  hη.comp_continuous (continuous_coordinateInclusion U i)

/-- Coordinate restrictions of a continuous `R`-valued character are continuous. -/
theorem continuous_coordinateCharacter [TopologicalSpace R] {η : Subgroup.pi Set.univ U →* Rˣ}
    (hη : Continuous fun u => (η u : R)) (i : ι) :
    Continuous fun u => (coordinateCharacter U η i u : R) :=
  hη.comp (continuous_coordinateInclusion U i)

end Topology

end Langlands.FiniteTensor
