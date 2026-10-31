import Langlands.Representation.RestrictedTensor.FiniteTail
import Langlands.Representation.Twist.Definitions
import Mathlib.Topology.LocallyConstant.Basic

/-! # Scalar characters and genuine restricted tensor twists -/

noncomputable section
open scoped Classical TensorProduct
universe uK uI uG uV uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RestrictedTensor

variable {ι : Type uI} {G : ι → Type uG} [∀ i, Group (G i)]
variable (H : ∀ i, Subgroup (G i))

/-- Enlarging the finite set makes the full integral tail smaller. -/
theorem tailReferenceSubgroup_le_of_subset {E S : Finset ι} (hES : E ⊆ S) :
    tailReferenceSubgroup H S ≤ tailReferenceSubgroup H E := by
  intro g hg
  exact ⟨fun i hi => hg.1 i (hES hi),
    fun i _ => tailReferenceSubgroup_integral H S hg i⟩

variable {M : Type uM} [CommMonoid M]

/-- Restrict an actual character along the existing singleton insertion. -/
def localCharacter (χ : RestrictedGroup G H →* M) (i : ι) : G i →* M :=
  χ.comp (RestrictedProduct.mulSingleMonoidHom H i)

@[simp]
theorem character_finiteProjection (χ : RestrictedGroup G H →* M)
    (S : Finset ι) (g : RestrictedGroup G H) :
    χ (finiteProjection H S g) = ∏ i ∈ S, localCharacter H χ i (g i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [finiteProjection_insert H S i hi, map_mul, ih, Finset.prod_insert hi]
      rfl

/-- Full-tail triviality gives the finite local-product formula on any adequate stage. -/
theorem character_eq_prod_of_tail (χ : RestrictedGroup G H →* M)
    (E : Finset ι) (hχ : ∀ t ∈ tailReferenceSubgroup H E, χ t = 1)
    (S : Finset ι) (hES : E ⊆ S) (g : RestrictedGroup G H)
    (hg : ∀ i ∉ S, g i ∈ H i) :
    χ g = ∏ i ∈ S, localCharacter H χ i (g i) := by
  have ht := hχ _ (tailReferenceSubgroup_le_of_subset H hES
    (tailProjection_mem_tailReferenceSubgroup H S g hg))
  calc
    χ g = χ (finiteProjection H S g * tailProjection H S g) := by
      rw [finiteProjection_mul_tailProjection]
    _ = χ (finiteProjection H S g) := by rw [map_mul, ht, mul_one]
    _ = _ := character_finiteProjection H χ S g

/-- Tail triviality entails triviality of each remaining integral local character. -/
theorem localCharacter_eq_one_of_tail (χ : RestrictedGroup G H →* M)
    (E : Finset ι) (hχ : ∀ t ∈ tailReferenceSubgroup H E, χ t = 1)
    (i : ι) (hi : i ∉ E) (g : G i) (hg : g ∈ H i) :
    localCharacter H χ i g = 1 := by
  apply hχ
  constructor
  · intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [RestrictedProduct.mulSingleMonoidHom, hji]
  · intro j _
    by_cases hji : j = i
    · subst j
      simpa [RestrictedProduct.mulSingleMonoidHom] using hg
    · simp [RestrictedProduct.mulSingleMonoidHom, hji]

/-- Local constancy at the identity supplies full-tail triviality for some finite set. -/
theorem exists_character_tail [∀ i, TopologicalSpace (G i)]
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (χ : RestrictedGroup G H →* M) (hχ : IsLocallyConstant χ) :
    ∃ E : Finset ι, ∀ t ∈ tailReferenceSubgroup H E, χ t = 1 := by
  have hone : (1 : RestrictedGroup G H) ∈ {t | χ t = 1} := map_one χ
  obtain ⟨E, hE⟩ := exists_tailReferenceSubgroup_subset H hH
    ((hχ.isOpen_fiber 1).mem_nhds hone)
  exact ⟨E, fun t ht => hE ht⟩

variable {K : Type uK} [Field K] {V : ι → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable (ρ : ∀ i, Representation K (G i) (V i))
variable (E : Finset ι) (e : ∀ i, V i)
variable (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i)
variable (χ : RestrictedGroup G H →* Kˣ)
variable (hχ : ∀ t ∈ tailReferenceSubgroup H E, χ t = 1)

include he hχ in
/-- The original reference vectors remain fixed for the actual local scalar twists. -/
theorem twistReference_fixed (i : ι) (hi : i ∉ E) (g : G i) (hg : g ∈ H i) :
    Langlands.twist (localCharacter H χ i) (ρ i) g (e i) = e i := by
  change (localCharacter H χ i g : K) • ρ i g (e i) = e i
  rw [localCharacter_eq_one_of_tail H χ E hχ i hi g hg, Units.val_one, one_smul]
  exact he i hi g hg

/-- Component twists act on the same constructed algebraic direct limit. -/
def twistedRepresentation : Representation K (RestrictedGroup G H) (Space K V E e) :=
  representation H (fun i => Langlands.twist (localCharacter H χ i) (ρ i))
    E e (twistReference_fixed H ρ E e he χ hχ)

/-- Twisting the genuine restricted tensor action equals the tensor of the local twists. -/
theorem twistedRepresentation_eq :
    twistedRepresentation H ρ E e he χ hχ =
      Langlands.twist χ (representation H ρ E e he) := by
  apply MonoidHom.ext
  intro g
  obtain ⟨F, _, hF⟩ := exists_finset_reference_outside H E g
  apply hom_ext_cofinal F
  intro S hFS x
  have hg : ∀ i ∉ S.1, g i ∈ H i :=
    fun i hi => hF i (fun hiF => hi (hFS hiF))
  change representation H (fun i => Langlands.twist (localCharacter H χ i) (ρ i))
      E e (twistReference_fixed H ρ E e he χ hχ) g (pure E e S x) =
    (χ g : K) • representation H ρ E e he g (pure E e S x)
  rw [representation_pure_of_mem H _ E e _ g S hg,
    representation_pure_of_mem H ρ E e he g S hg]
  change of K V E e S (PiTensorProduct.tprod K
      (fun i : S.1 => (localCharacter H χ i (g i) : K) • ρ i (g i) (x i))) =
    (χ g : K) • of K V E e S
      (PiTensorProduct.tprod K (fun i : S.1 => ρ i (g i) (x i)))
  rw [(PiTensorProduct.tprod K).map_smul_univ, map_smul]
  congr 1
  rw [← Units.coe_prod]
  apply congrArg (fun a : Kˣ => (a : K))
  exact (Finset.prod_coe_sort S.1 (fun i => localCharacter H χ i (g i))).trans
    (character_eq_prod_of_tail H χ E hχ S.1 S.2 g hg).symm

/-- The comparison is the identity on the existing restricted tensor carrier. -/
def twistEquiv :
    (Langlands.twist χ (representation H ρ E e he)).Equiv
      (twistedRepresentation H ρ E e he χ hχ) where
  toLinearEquiv := LinearEquiv.refl K _
  isIntertwining' g := by rw [twistedRepresentation_eq]; rfl

@[simp]
theorem twistEquiv_apply (x : Space K V E e) :
    twistEquiv H ρ E e he χ hχ x = x := rfl

end Langlands.RestrictedTensor
