import Langlands.AlgebraicGeometry.AffineCechDeRhamSquareZeroHomotopy
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Square-zero changes of affine coordinates and differential bases -/

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineCechDeRham.RelativeForms

open scoped TensorProduct Pointwise

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}

private abbrev extended (I : Ideal R) := I.map (algebraMap R A)

private lemma mul_eq_zero_of_mem_extended (hI : I * I = ⊥) {x y : A}
    (hx : x ∈ extended I) (hy : y ∈ extended I) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rwa [← Ideal.map_mul, hI, Ideal.map_bot, Ideal.mem_bot] at h

variable (I) (hI : I * I = ⊥)
  (C : Ω[A⁄R] →ₗ[A] A) (hC : ∀ ω, C ω ∈ extended I)

/-- Add the derivation with contraction `C` to the identity algebra map. -/
def addDerivation : A →ₐ[R] A where
  toFun a := a + C (dZero R A a)
  map_zero' := by simp
  map_one' := by simp [dZero]
  map_add' a b := by simp only [map_add]; abel
  map_mul' a b := by
    change a * b + C (KaehlerDifferential.D R A (a * b)) =
      (a + C (KaehlerDifferential.D R A a)) * (b + C (KaehlerDifferential.D R A b))
    simp only [Derivation.leibniz, map_add, map_smul, smul_eq_mul]
    have hz := mul_eq_zero_of_mem_extended hI (hC (dZero R A a)) (hC (dZero R A b))
    change C (KaehlerDifferential.D R A a) * C (KaehlerDifferential.D R A b) = 0 at hz
    linear_combination -hz
  commutes' r := by
    change algebraMap R A r + C (KaehlerDifferential.D R A (algebraMap R A r)) = algebraMap R A r
    rw [Derivation.map_algebraMap, map_zero, add_zero]

@[simp]
lemma addDerivation_apply (a : A) : addDerivation I hI C hC a = a + C (dZero R A a) := rfl

lemma addDerivation_sub_mem (a : A) :
    addDerivation I hI C hC a - (AlgHom.id R A) a ∈ extended I := by
  simpa only [addDerivation_apply, AlgHom.id_apply, add_sub_cancel_left] using hC (dZero R A a)

include hI hC in
private lemma contract_dZero_eq_zero_of_mem {x : A} (hx : x ∈ extended I) :
    C (dZero R A x) = 0 := by
  change x ∈ (extended I).restrictScalars R at hx
  rw [← Ideal.smul_top_eq_map] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr a _
    rw [map_smul, ← IsScalarTower.algebraMap_smul A r, C.map_smul]
    change algebraMap R A r * C (dZero R A a) = 0
    exact mul_eq_zero_of_mem_extended hI (Ideal.mem_map_of_mem (algebraMap R A) hr) (hC _)
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

variable (D : Ω[A⁄R] →ₗ[A] A) (hD : ∀ ω, D ω ∈ extended I)

/-- The algebra maps obtained from two contractions compose by addition. -/
lemma addDerivation_comp :
    (addDerivation I hI C hC).comp (addDerivation I hI D hD) =
      addDerivation I hI (C + D) (fun ω => (extended I).add_mem (hC ω) (hD ω)) := by
  ext a
  simp only [AlgHom.comp_apply, addDerivation_apply, map_add, LinearMap.add_apply,
    contract_dZero_eq_zero_of_mem I hI C hC (hD (dZero R A a)), add_zero]
  abel

/-- An ideal-valued derivation defines an automorphism congruent to the identity. -/
def addDerivationEquiv : A ≃ₐ[R] A := by
  let hneg : ∀ ω, (-C) ω ∈ extended I := fun ω => by
    change -(C ω) ∈ I.map (algebraMap R A)
    exact (I.map (algebraMap R A)).neg_mem (hC ω)
  apply AlgEquiv.ofAlgHom (addDerivation I hI C hC) (addDerivation I hI (-C) hneg)
  · rw [addDerivation_comp]
    ext a
    simp
  · rw [addDerivation_comp]
    ext a
    simp

omit D hD in
/-- The homotopy contraction of the automorphism against the identity is
the contraction used to define its derivation. -/
lemma contractDifferenceOne_addDerivation (ω : Ω[A⁄R]) :
    contractDifferenceOne (addDerivation I hI C hC) (AlgHom.id R A) hI
      (addDerivation_sub_mem I hI C hC) ω = C ω := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, contractDifferenceOne_smul_d, map_smul]
    change (a + C (dZero R A a)) * (b + C (dZero R A b) - b) = a * C (dZero R A b)
    rw [add_sub_cancel_left, add_mul, mul_eq_zero_of_mem_extended hI (hC _) (hC _), add_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

omit D hD in
/-- A closed one-form changes by the differential of its contraction. -/
lemma mapOne_addDerivation_of_closed (ω : Ω[A⁄R]) (hω : dOne R A ω = 0) :
    mapOne (addDerivation I hI C hC) ω = ω + dZero R A (C ω) := by
  have hh := mapOne_sub_eq_d_contract_of_closed (addDerivation I hI C hC)
    (AlgHom.id R A) hI (addDerivation_sub_mem I hI C hC) hω
  rw [mapOne_id, contractDifferenceOne_addDerivation] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

section Basis

variable {M κ : Type u} [AddCommGroup M] [Module A M]
  (J : Ideal A) (hJ : J * J = ⊥) (b : Module.Basis κ A M) (w : κ → M)
  (hw : ∀ k, w k - b k ∈ J • (⊤ : Submodule A M))

private abbrev differenceMap := b.constr A (fun k => w k - b k)

include hw in
private lemma differenceMap_mem (x : M) : differenceMap b w x ∈ J • (⊤ : Submodule A M) := by
  have h : ⊤ ≤ (J • (⊤ : Submodule A M)).comap (differenceMap b w) := by
    rw (config := { occs := .pos [1] }) [← b.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    change differenceMap b w (b k) ∈ J • (⊤ : Submodule A M)
    rw [Module.Basis.constr_basis]
    exact hw k
  exact h (Submodule.mem_top (x := x))

include hJ hw in
private lemma differenceMap_sq (x : M) : differenceMap b w (differenceMap b w x) = 0 := by
  let p := differenceMap b w
  have hp : p.range ≤ J • (⊤ : Submodule A M) := by
    rintro _ ⟨y, rfl⟩
    exact differenceMap_mem J b w hw y
  have hx : p (p x) ∈ (J • (⊤ : Submodule A M)).map p :=
    Submodule.mem_map_of_mem (differenceMap_mem J b w hw x)
  rw [Submodule.map_smul'', Submodule.map_top] at hx
  have hle : J • p.range ≤ J • J • (⊤ : Submodule A M) :=
    Submodule.smul_le.mpr fun _ hr _ hy => Submodule.smul_mem_smul hr (hp hy)
  have hy := hle hx
  rw [← Submodule.mul_smul, hJ, Submodule.bot_smul, Submodule.mem_bot] at hy
  exact hy

include hJ hw in
/-- Vectors congruent to a basis modulo an ideal times the module again form
a basis if the ideal is square-zero. -/
def basisOfCongruentVectors : Module.Basis κ A M := by
  let p := differenceMap b w
  have hp (x : M) : p (p x) = 0 := differenceMap_sq J hJ b w hw x
  refine b.map (LinearEquiv.ofLinearMap
    (LinearMap.id + p) (LinearMap.id - p) ?_ ?_)
  · apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, hp, add_zero, add_sub_cancel_right]
  · apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, hp, sub_zero, sub_add_cancel]

@[simp]
lemma basisOfCongruentVectors_apply (k : κ) :
    basisOfCongruentVectors J hJ b w hw k = w k := by
  rw [basisOfCongruentVectors, Module.Basis.map_apply]
  change b k + (b.constr A (fun i => w i - b i)) (b k) = w k
  rw [Module.Basis.constr_basis]
  abel

end Basis

end Langlands.AlgebraicGeometry.AffineCechDeRham.RelativeForms
