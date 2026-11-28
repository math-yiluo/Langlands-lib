import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Quotients for a prescribed central character -/

namespace Langlands.FiniteRep

variable {A G C : Type*} [Group A] [Group G] [Group C]

/-- The subgroup killed by passage to a level `U` with scalar character `ω`. -/
def centralCharacterLevel (i : A →* G) (ω : A →* C) (U : Subgroup G) : Subgroup G :=
  ω.ker.map i ⊔ U

theorem le_centralCharacterLevel (i : A →* G) (ω : A →* C) (U : Subgroup G) :
    U ≤ centralCharacterLevel i ω U :=
  le_sup_right

theorem centralCharacterLevel_normal (i : A →* G) (hi : ∀ z, i z ∈ Subgroup.center G)
    (ω : A →* C) (U : Subgroup G) [U.Normal] : (centralCharacterLevel i ω U).Normal := by
  let : (ω.ker.map i).Normal := Subgroup.normal_of_le_center (by
    rintro _ ⟨z, _, rfl⟩
    exact hi z)
  unfold centralCharacterLevel
  infer_instance

theorem isOpen_centralCharacterLevel [TopologicalSpace G] [SeparatelyContinuousMul G]
    (i : A →* G) (ω : A →* C) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    IsOpen (centralCharacterLevel i ω U : Set G) :=
  Subgroup.isOpen_mono (le_centralCharacterLevel i ω U) hU

/-- Suppose the scalar image is central and `U` is normal. If they generate a finite-index
subgroup and the scalar character has finite image, killing `U` and the image of the character
kernel gives a finite quotient. -/
theorem finiteIndex_centralCharacterLevel (i : A →* G) (hi : ∀ z, i z ∈ Subgroup.center G)
    (ω : A →* C) (hω : (Set.range ω).Finite) (U : Subgroup G) [U.Normal]
    [(i.range ⊔ U).FiniteIndex] : (centralCharacterLevel i ω U).FiniteIndex := by
  let K := centralCharacterLevel i ω U
  let : K.Normal := centralCharacterLevel_normal i hi ω U
  let : Finite ω.range := hω
  have hmap : ω.ker.map i ≤ i.range := Subgroup.map_le_range _ _
  have hK : K ≤ i.range ⊔ U := sup_le_sup_right hmap U
  have hL : i.range ⊔ K = i.range ⊔ U := by
    change i.range ⊔ (ω.ker.map i ⊔ U) = _
    rw [← sup_assoc, sup_eq_left.mpr hmap]
  have hmapK : ω.ker.map i ≤ K := le_sup_left
  have hker : ω.ker ≤ K.comap i := Subgroup.map_le_iff_le_comap.mp hmapK
  have hrel : K.relIndex (i.range ⊔ U) ≠ 0 := by
    rw [← hL, Subgroup.relIndex_sup_right, ← Subgroup.index_comap]
    exact (Subgroup.finiteIndex_of_le hker).index_ne_zero
  exact ⟨(Subgroup.relIndex_mul_index hK) ▸
    mul_ne_zero hrel (Subgroup.FiniteIndex.index_ne_zero (H := i.range ⊔ U))⟩

/-- A centrally covariant function that is right invariant under `U` descends to the quotient
by `centralCharacterLevel`. -/
def descendCentralCovariantFunction (i : A →* G) (hi : ∀ z, i z ∈ Subgroup.center G)
    (ω : A →* ℂˣ) (U : Subgroup G) [U.Normal] (f : G → ℂ)
    (hω : ∀ z g, f (i z * g) = (ω z : ℂ) * f g)
    (hU : ∀ g u, u ∈ U → f (g * u) = f g) : G ⧸ centralCharacterLevel i ω U → ℂ :=
  Quotient.lift f fun a b hab => by
    have hab' : a⁻¹ * b ∈ ω.ker.map i ⊔ U := QuotientGroup.leftRel_apply.mp hab
    obtain ⟨_, ⟨z, hz, rfl⟩, u, hu, he⟩ := Subgroup.mem_sup_of_normal_right.mp hab'
    have hb : b = a * (i z * u) := by rw [he, mul_inv_cancel_left]
    rw [hb, ← mul_assoc, hU _ u hu, Subgroup.mem_center_iff.mp (hi z) a, hω z a,
      MonoidHom.mem_ker.mp hz, Units.val_one, one_mul]

@[simp]
theorem descendCentralCovariantFunction_mk (i : A →* G) (hi : ∀ z, i z ∈ Subgroup.center G)
    (ω : A →* ℂˣ) (U : Subgroup G) [U.Normal] (f : G → ℂ)
    (hω : ∀ z g, f (i z * g) = (ω z : ℂ) * f g)
    (hU : ∀ g u, u ∈ U → f (g * u) = f g) (g : G) :
    descendCentralCovariantFunction i hi ω U f hω hU (QuotientGroup.mk g) = f g :=
  rfl

end Langlands.FiniteRep
