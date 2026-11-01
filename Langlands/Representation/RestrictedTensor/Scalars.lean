import Langlands.Representation.RestrictedTensor.Twist
import Mathlib.RingTheory.PiTensorProduct

/-! # Actual restricted tensor products of scalar lines -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uG

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RestrictedTensor

variable (K : Type uK) [Field K] {ι : Type uI}

/-- Multiply the entries in an actual finite tensor product of scalar lines. -/
def scalarStageEquiv (S : Finset ι) : Stage K (fun _ : ι => K) S ≃ₗ[K] K :=
  (PiTensorProduct.constantBaseRingEquiv S K).toLinearEquiv

@[simp]
theorem scalarStageEquiv_tprod (S : Finset ι) (x : S → K) :
    scalarStageEquiv K S (PiTensorProduct.tprod K x) = ∏ i, x i :=
  PiTensorProduct.constantBaseRingEquiv_tprod x

/-- Adjoining scalar-one reference vectors does not change the product. -/
theorem scalarStageEquiv_transition {S T : Finset ι} (h : S ⊆ T) :
    (scalarStageEquiv K T).toLinearMap.comp (transition (fun _ : ι => (1 : K)) h) =
      (scalarStageEquiv K S).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, transition_tprod, scalarStageEquiv_tprod]
  let f : ι → K := fun i => if hi : i ∈ S then x ⟨i, hi⟩ else 1
  change (∏ i : T, f i) = ∏ i : S, x i
  calc
    (∏ i : T, f i) = ∏ i ∈ T, f i := Finset.prod_coe_sort T f
    _ = ∏ i ∈ S, f i :=
      (Finset.prod_subset h (fun i _ hi => by simp [f, hi])).symm
    _ = ∏ i : S, f i := (Finset.prod_coe_sort S f).symm
    _ = ∏ i : S, x i := Finset.prod_congr rfl (fun i _ => by simp [f, i.2])

/-- The compatible scalar products descend through the actual direct limit. -/
def scalarEvaluation (E : Finset ι) :
    Space K (fun _ : ι => K) E (fun _ => 1) →ₗ[K] K :=
  lift E (fun _ => 1) (fun S => (scalarStageEquiv K S.1).toLinearMap)
    (fun _ _ h x => LinearMap.congr_fun (scalarStageEquiv_transition K h) x)

@[simp]
theorem scalarEvaluation_of (E : Finset ι) (S : Index E)
    (x : Stage K (fun _ : ι => K) S.1) :
    scalarEvaluation K E (of K (fun _ : ι => K) E (fun _ => 1) S x) =
      scalarStageEquiv K S.1 x := rfl

@[simp]
theorem scalarEvaluation_pure (E : Finset ι) (S : Index E) (x : S.1 → K) :
    scalarEvaluation K E (pure E (fun _ : ι => (1 : K)) S x) = ∏ i, x i := by
  simp only [pure, scalarEvaluation_of, scalarStageEquiv_tprod]

/-- The actual restricted tensor of scalar lines with reference one is the scalar field. -/
def scalarEquiv (E : Finset ι) :
    Space K (fun _ : ι => K) E (fun _ => 1) ≃ₗ[K] K :=
  LinearEquiv.ofBijective (scalarEvaluation K E) ⟨by
    intro x y hxy
    obtain ⟨S, z, hz⟩ := exists_of E (fun _ : ι => (1 : K)) (x - y)
    have he : scalarStageEquiv K S.1 z = 0 := by
      rw [← scalarEvaluation_of, ← hz, map_sub, hxy, sub_self]
    have hz0 : z = 0 := (scalarStageEquiv K S.1).injective (by simpa using he)
    apply sub_eq_zero.mp
    rw [hz, hz0, map_zero], by
    intro c
    refine ⟨of K (fun _ : ι => K) E (fun _ => 1) ⟨E, le_rfl⟩
      ((scalarStageEquiv K E).symm c), ?_⟩
    change scalarStageEquiv K E ((scalarStageEquiv K E).symm c) = c
    exact (scalarStageEquiv K E).apply_symm_apply c⟩

@[simp]
theorem scalarEquiv_pure (E : Finset ι) (S : Index E) (x : S.1 → K) :
    scalarEquiv K E (pure E (fun _ : ι => (1 : K)) S x) = ∏ i, x i :=
  scalarEvaluation_pure K E S x

variable {G : ι → Type uG} [∀ i, Group (G i)]
variable (H : ∀ i, Subgroup (G i)) (E : Finset ι)

/-- Trivial local scalar actions fix the actual scalar-one references. -/
theorem trivialScalarReference_fixed (i : ι) (_hi : i ∉ E) (g : G i) (_hg : g ∈ H i) :
    Representation.trivial K (G i) K g (1 : K) = 1 := rfl

/-- Multiplication identifies the tensor of trivial scalar actions with the trivial action. -/
def trivialScalarTensorEquiv :
    (representation H (fun i => Representation.trivial K (G i) K)
      E (fun _ => 1) (trivialScalarReference_fixed K H E)).Equiv
      (Representation.trivial K (RestrictedGroup G H) K) :=
  Representation.Equiv.mk (scalarEquiv K E) (fun _g => by
    change (scalarEquiv K E).toLinearMap.comp
        (map E E (fun _ : ι => (1 : K)) (fun _ => 1)
          (fun _ => LinearMap.id) _) =
      LinearMap.id.comp (scalarEquiv K E).toLinearMap
    rw [map_id]
    rfl)

variable (χ : RestrictedGroup G H →* Kˣ)
variable (hχ : ∀ t ∈ tailReferenceSubgroup H E, χ t = 1)

include hχ in
/-- Full-tail triviality makes the actual local characters fix scalar one. -/
theorem characterScalarReference_fixed (i : ι) (hi : i ∉ E)
    (g : G i) (hg : g ∈ H i) :
    Langlands.characterRepresentation (localCharacter H χ i) g (1 : K) = 1 :=
  twistReference_fixed H (fun i => Representation.trivial K (G i) K)
    E (fun _ => 1) (trivialScalarReference_fixed K H E) χ hχ i hi g hg

/-- An actual tensor factorization of a character trivial on the full reference tail. -/
def characterScalarTensorEquiv :
    (representation H
      (fun i => Langlands.characterRepresentation (localCharacter H χ i))
      E (fun _ => 1) (characterScalarReference_fixed K H E χ hχ)).Equiv
      (Langlands.characterRepresentation χ) :=
  ((twistEquiv H (fun i => Representation.trivial K (G i) K)
    E (fun _ => 1) (trivialScalarReference_fixed K H E) χ hχ).symm).trans
      (Langlands.twistEquiv χ (trivialScalarTensorEquiv K H E))

@[simp]
theorem characterScalarTensorEquiv_pure (S : Index E) (x : S.1 → K) :
    characterScalarTensorEquiv K H E χ hχ
      (pure E (fun _ : ι => (1 : K)) S x) = ∏ i, x i :=
  scalarEquiv_pure K E S x

end Langlands.RestrictedTensor
