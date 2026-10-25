import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Unitary central characters of finite external tensors -/

noncomputable section

open scoped TensorProduct IsMulCommutative
open Function Module

namespace Langlands.UnitaryCentralCharacter

/-- Central-character data are determined by their underlying character. -/
@[ext] theorem ext {H W : Type*} [Group H] [TopologicalSpace H]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ H W}
    {c d : UnitaryCentralCharacter σ} (h : c.character = d.character) : c = d := by
  cases c
  cases d
  cases h
  rfl

end Langlands.UnitaryCentralCharacter

namespace Langlands.FiniteTensor

universe uI uG uV

variable {ι : Type uI} {G : ι → Type uG} [∀ i, Group (G i)]

/-- Evaluation on a coordinate of the full product center. -/
def centerEval (i : ι) : Subgroup.center (∀ i, G i) →* Subgroup.center (G i) where
  toFun z := ⟨z.val i, by
    have hz : ∀ j, z.val j ∈ Subgroup.center (G j) := by
      simpa only [Subgroup.center_pi, Subgroup.mem_pi, Set.mem_univ, forall_const]
        using z.property
    exact hz i⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem centerEval_coe (i : ι) (z : Subgroup.center (∀ i, G i)) :
    (centerEval i z : G i) = z.val i := rfl

/-- Insert one central coordinate, with identity in the other coordinates. -/
def centerSingle [DecidableEq ι] (i : ι) :
    Subgroup.center (G i) →* Subgroup.center (∀ i, G i) where
  toFun z := ⟨Pi.mulSingle i (z : G i), by
    rw [Subgroup.center_pi]
    exact (Subgroup.mulSingle_mem_pi i _).mpr (fun _ => z.property)⟩
  map_one' := by apply Subtype.ext; exact Pi.mulSingle_one i
  map_mul' z w := by apply Subtype.ext; exact Pi.mulSingle_mul i _ _

@[simp] theorem centerSingle_coe [DecidableEq ι] (i : ι) (z : Subgroup.center (G i)) :
    (centerSingle i z : ∀ i, G i) = Pi.mulSingle i (z : G i) := rfl

@[simp] theorem centerEval_centerSingle_same [DecidableEq ι]
    (i : ι) (z : Subgroup.center (G i)) : centerEval i (centerSingle i z) = z := by
  apply Subtype.ext
  exact Pi.mulSingle_eq_same i _

@[simp] theorem centerEval_centerSingle_ne [DecidableEq ι]
    {i j : ι} (h : j ≠ i) (z : Subgroup.center (G i)) :
    centerEval j (centerSingle i z) = 1 := by
  apply Subtype.ext
  exact Pi.mulSingle_eq_of_ne h _

variable [∀ i, TopologicalSpace (G i)]

/-- Coordinate evaluation on centers is continuous for the subspace topologies. -/
theorem continuous_centerEval (i : ι) : Continuous (centerEval (G := G) i) :=
  ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- Central coordinate insertion is continuous for the product and subspace topologies. -/
theorem continuous_centerSingle [DecidableEq ι] (i : ι) :
    Continuous (centerSingle (G := G) i) :=
  ((continuous_mulSingle i).comp continuous_subtype_val).subtype_mk _

variable [Fintype ι]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {ρ : ∀ i, Representation ℂ (G i) (V i)}

/-- Product character evaluated on the full actual center of the product group. -/
def tensorCentralCharacter (c : ∀ i, UnitaryCentralCharacter (ρ i)) :
    Subgroup.center (∀ i, G i) →* ℂˣ where
  toFun z := ∏ i, (c i).character (centerEval i z)
  map_one' := by simp
  map_mul' z w := by simp [Finset.prod_mul_distrib]

@[simp] theorem tensorCentralCharacter_apply (c : ∀ i, UnitaryCentralCharacter (ρ i))
    (z : Subgroup.center (∀ i, G i)) :
    tensorCentralCharacter c z = ∏ i, (c i).character (centerEval i z) := rfl

/-- The product character has open kernel. -/
theorem tensorCentralCharacter_isOpen_ker [∀ i, IsTopologicalGroup (G i)]
    (c : ∀ i, UnitaryCentralCharacter (ρ i)) :
    IsOpen ((tensorCentralCharacter c).ker : Set (Subgroup.center (∀ i, G i))) := by
  let K : Subgroup (Subgroup.center (∀ i, G i)) :=
    ⨅ i, ((c i).character.comp (centerEval i)).ker
  apply Subgroup.isOpen_mono (H₁ := K)
  · intro z hz
    have hz' : ∀ i, (c i).character (centerEval i z) = 1 := by
      simpa only [K, Subgroup.mem_iInf, MonoidHom.mem_ker, MonoidHom.comp_apply] using hz
    change (∏ i, (c i).character (centerEval i z)) = 1
    simp only [hz', Finset.prod_const_one]
  · rw [show (K : Set (Subgroup.center (∀ i, G i))) =
        ⋂ i, (centerEval (G := G) i) ⁻¹' ((c i).character.ker : Set (Subgroup.center (G i))) by
      ext z
      simp only [K, SetLike.mem_coe, Subgroup.mem_iInf, Set.mem_iInter, Set.mem_preimage,
        MonoidHom.mem_ker, MonoidHom.comp_apply]]
    exact isOpen_iInter_of_finite (fun i => (c i).isOpen_ker.preimage (continuous_centerEval i))

/-- Assemble actual scalar-action data on the finite external tensor. -/
def externalUnitaryCentralCharacter [∀ i, IsTopologicalGroup (G i)]
    (c : ∀ i, UnitaryCentralCharacter (ρ i)) : UnitaryCentralCharacter (external ρ) where
  character := tensorCentralCharacter c
  isOpen_ker := tensorCentralCharacter_isOpen_ker c
  norm_eq_one z := by
    simp only [tensorCentralCharacter_apply, Units.coe_prod, norm_prod]
    simp only [(c _).norm_eq_one, Finset.prod_const_one]
  acts z x := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [map_smul, external_tprod]
      have h : (fun i => ρ i (z.val i) (v i)) =
          fun i => ((c i).character (centerEval i z) : ℂ) • v i :=
        funext (fun i => (c i).acts (centerEval i z) (v i))
      rw [h, MultilinearMap.map_smul_univ]
      simp only [tensorCentralCharacter_apply, Units.coe_prod]
      exact smul_comm _ _ _
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

@[simp] theorem externalUnitaryCentralCharacter_character [∀ i, IsTopologicalGroup (G i)]
    (c : ∀ i, UnitaryCentralCharacter (ρ i)) (z : Subgroup.center (∀ i, G i)) :
    (externalUnitaryCentralCharacter c).character z =
      ∏ i, (c i).character (centerEval i z) := rfl

/-- A central coordinate acts by the tensor character on its own factor.
The auxiliary factors are contracted against basis-coordinate functionals. -/
theorem centralCharacter_acts_factor [DecidableEq ι] [∀ i, Nontrivial (V i)]
    (c : UnitaryCentralCharacter (external ρ)) (j : ι)
    (z : Subgroup.center (G j)) (v : V j) :
    ρ j z v = (c.character (centerSingle j z) : ℂ) • v := by
  classical
  let J := ({j}ᶜ : Set ι)
  let X := PiTensorProduct ℂ (fun i : J => V i)
  let b := fun i : J => Basis.ofVectorSpace ℂ (V i)
  let a := fun i : J => Classical.choice (b i).index_nonempty
  let B := Basis.piTensorProduct b
  let e := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V j
  let q : X ⊗[ℂ] V j →ₗ[ℂ] V j :=
    (TensorProduct.lid ℂ (V j)).toLinearMap ∘ₗ LinearMap.rTensor (V j) (B.coord a)
  have hq (x : X) (w : V j) : q (x ⊗ₜ[ℂ] w) = B.coord a x • w := by
    simp [q]
  have h := c.acts (centerSingle j z) (e.symm (B a ⊗ₜ[ℂ] v))
  have he := congrArg e h
  change e (external ρ (Pi.mulSingle j (z : G j)) (e.symm (B a ⊗ₜ[ℂ] v))) =
    e ((c.character (centerSingle j z) : ℂ) • e.symm (B a ⊗ₜ[ℂ] v)) at he
  rw [external_mulSingle, split_map_slot, map_smul, e.apply_symm_apply,
    LinearMap.lTensor_tmul] at he
  have h' := congrArg q he
  rw [hq, map_smul, hq] at h'
  simpa only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_smul]
    using h'

/-- Recover the actual unitary central character of a factor by central insertion. -/
def restrictUnitaryCentralCharacter [DecidableEq ι] [∀ i, Nontrivial (V i)]
    (c : UnitaryCentralCharacter (external ρ)) (i : ι) :
    UnitaryCentralCharacter (ρ i) where
    character := c.character.comp (centerSingle i)
    isOpen_ker := c.isOpen_ker.preimage (continuous_centerSingle i)
    norm_eq_one := fun z => c.norm_eq_one (centerSingle i z)
    acts := centralCharacter_acts_factor c i

@[simp] theorem restrictUnitaryCentralCharacter_character [DecidableEq ι]
    [∀ i, Nontrivial (V i)] (c : UnitaryCentralCharacter (external ρ))
    (i : ι) (z : Subgroup.center (G i)) :
    (restrictUnitaryCentralCharacter c i).character z =
      c.character (centerSingle i z) := by
  rfl

/-- The product character restricts to the supplied character in each coordinate. -/
@[simp] theorem tensorCentralCharacter_centerSingle [DecidableEq ι]
    (c : ∀ i, UnitaryCentralCharacter (ρ i)) (i : ι) (z : Subgroup.center (G i)) :
    tensorCentralCharacter c (centerSingle i z) = (c i).character z := by
  rw [tensorCentralCharacter_apply, Finset.prod_eq_single i]
  · rw [centerEval_centerSingle_same]
  · intro j _ hji
    rw [centerEval_centerSingle_ne hji, map_one]
  · simp

omit [∀ i, TopologicalSpace (G i)] in
/-- Every element of the full product center is the product of its central coordinates. -/
theorem prod_centerSingle_centerEval [DecidableEq ι]
    (z : Subgroup.center (∀ i, G i)) :
    (∏ i, centerSingle i (centerEval i z)) = z := by
  apply Subtype.ext
  funext j
  have h : centerEval j (∏ i, centerSingle i (centerEval i z)) = centerEval j z := by
    rw [map_prod, Finset.prod_eq_single j]
    · exact centerEval_centerSingle_same j _
    · intro i _ hij
      exact centerEval_centerSingle_ne (Ne.symm hij) _
    · simp
  exact congrArg Subtype.val h

/-- The tensor character is the product of its restrictions to central coordinates. -/
theorem character_eq_prod_restrict [DecidableEq ι] [∀ i, Nontrivial (V i)]
    (c : UnitaryCentralCharacter (external ρ)) (z : Subgroup.center (∀ i, G i)) :
    c.character z = ∏ i, (restrictUnitaryCentralCharacter c i).character (centerEval i z) := by
  conv_lhs => rw [← prod_centerSingle_centerEval z, map_prod]
  rfl

/-- Assembly followed by restriction recovers each supplied factor character. -/
@[simp] theorem restrict_external_character [DecidableEq ι]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, Nontrivial (V i)]
    (c : ∀ i, UnitaryCentralCharacter (ρ i)) (i : ι) (z : Subgroup.center (G i)) :
    (restrictUnitaryCentralCharacter (externalUnitaryCentralCharacter c) i).character z =
      (c i).character z := by
  exact tensorCentralCharacter_centerSingle c i z

/-- Assembly and coordinate restriction recover the factor data, including all laws. -/
@[simp] theorem restrict_externalUnitaryCentralCharacter [DecidableEq ι]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, Nontrivial (V i)]
    (c : ∀ i, UnitaryCentralCharacter (ρ i)) (i : ι) :
    restrictUnitaryCentralCharacter (externalUnitaryCentralCharacter c) i = c i := by
  apply UnitaryCentralCharacter.ext
  apply MonoidHom.ext
  intro z
  exact restrict_external_character c i z

/-- Coordinate restriction followed by assembly recovers the tensor data. -/
@[simp] theorem external_restrictUnitaryCentralCharacter [DecidableEq ι]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, Nontrivial (V i)]
    (c : UnitaryCentralCharacter (external ρ)) :
    externalUnitaryCentralCharacter (restrictUnitaryCentralCharacter c) = c := by
  apply UnitaryCentralCharacter.ext
  apply MonoidHom.ext
  intro z
  exact (character_eq_prod_restrict c z).symm

/-- Actual unitary central-character data on a finite external tensor are
canonically equivalent to factor data when every factor is nontrivial. -/
def unitaryCentralCharacterEquiv [DecidableEq ι]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, Nontrivial (V i)] :
    (∀ i, UnitaryCentralCharacter (ρ i)) ≃ UnitaryCentralCharacter (external ρ) where
  toFun := externalUnitaryCentralCharacter
  invFun := restrictUnitaryCentralCharacter
  left_inv c := funext (restrict_externalUnitaryCentralCharacter c)
  right_inv := external_restrictUnitaryCentralCharacter

end Langlands.FiniteTensor
