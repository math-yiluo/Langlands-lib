import Langlands.Automorphic.UnitaryContragredientCriterion
import Langlands.Representation.Smooth.SmallRealizationProof

/-! # Finiteness of central orbits from joint admissibility -/

noncomputable section

open scoped BigOperators Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

section Permutation

variable {K Q E : Type*} [Group K] [Group Q] [AddCommGroup E] [Module ℂ E]

/-- The action on families in a representation, combining the original action
with left translation of the group index. -/
def permutedFamilyAction (p : K →* Q) (σ : Representation ℂ K E) :
    Representation ℂ K (Q → E) where
  toFun k :=
    { toFun := fun f q => σ k (f ((p k)⁻¹ * q))
      map_add' _ _ := funext fun _ => map_add _ _ _
      map_smul' _ _ := funext fun _ => map_smul _ _ _ }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext q
    change σ 1 (f ((p 1)⁻¹ * q)) = f q
    simp
  map_mul' k l := by
    apply LinearMap.ext
    intro f
    funext q
    change σ (k * l) (f ((p (k * l))⁻¹ * q)) =
      σ k (σ l (f ((p l)⁻¹ * ((p k)⁻¹ * q))))
    simp only [map_mul, Module.End.mul_apply, mul_inv_rev, mul_assoc]

end Permutation

section Center

variable {G K V Z : Type*} [Group G] [TopologicalSpace G] [Group K]
  [AddCommGroup V] [Module ℂ V] [CommRing Z] [Algebra ℂ Z]

/-- Apply an element of the commutative acting algebra to a fixed vector. -/
def centralOrbitMap (D : Z →ₐ[ℂ] Module.End ℂ V) (v : V) : Z →ₗ[ℂ] V :=
  (LinearMap.applyₗ (R := ℂ) v).comp D.toLinearMap

theorem centralOrbitMap_apply (D : Z →ₐ[ℂ] Module.End ℂ V) (v : V) (z : Z) :
    centralOrbitMap D v z = D z v := rfl

/-- If the compact action normalizes the center action through a finite
image, all center translates of a compact-finite, finite-level vector
are values of intertwiners from one finite-dimensional compact representation. -/
theorem finiteDimensional_range_centralOrbitMap
    (ρ : Representation ℂ G V) (κ : Representation ℂ K V) (D : Z →ₐ[ℂ] Module.End ℂ V)
    (a : K →* (Z ≃ₐ[ℂ] Z)) [Finite a.range]
    (hJ : IsJointlyAdmissible ρ κ)
    (hcomm : ∀ g k v, ρ g (κ k v) = κ k (ρ g v))
    (hρD : ∀ g z v, ρ g (D z v) = D z (ρ g v))
    (hκD : ∀ k z v, κ k (D z v) = D (a k z) (κ k v))
    (v : V) (hv : FiniteVectors.IsFiniteVector κ v)
    (L : OpenSubgroup G) (hL : ∀ l : L, ρ l.val v = v) :
    FiniteDimensional ℂ (LinearMap.range (centralOrbitMap D v)) := by
  classical
  let E := FiniteVectors.orbitSubrepresentation κ v
  let : FiniteDimensional ℂ E.toSubmodule := hv
  have hE : E.toSubmodule ≤ fixedVectors ρ L.toSubgroup := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩ l
    change ρ l.val (κ k v) = κ k v
    rw [hcomm, hL l]
  let Q := a.range
  let : Fintype Q := Fintype.ofFinite Q
  let p : K →* Q := a.rangeRestrict
  let P := permutedFamilyAction p E.toRepresentation
  let T (z : Z) : (Q → E.toSubmodule) →ₗ[ℂ] V :=
    { toFun := fun f => ∑ q : Q, D (q.val z) (f q).val
      map_add' f g := by simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib]
      map_smul' c f := by
        simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, RingHom.id_apply, Finset.smul_sum] }
  have hTfix (z : Z) (f : Q → E.toSubmodule) (l : L) : ρ l.val (T z f) = T z f := by
    change ρ l.val (∑ q : Q, D (q.val z) (f q).val) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by
      rw [hρD]
      exact congrArg (D (q.val z)) (hE (f q).property l)
  have hTκ (z : Z) (k : K) (f : Q → E.toSubmodule) : T z (P k f) = κ k (T z f) := by
    change (∑ q : Q, D (q.val z) (κ k (f ((p k)⁻¹ * q)).val)) =
      κ k (∑ q : Q, D (q.val z) (f q).val)
    rw [map_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft (p k)⁻¹)
    intro q
    change D (q.val z) (κ k (f ((p k)⁻¹ * q)).val) =
      κ k (D (((p k)⁻¹ * q).val z) (f ((p k)⁻¹ * q)).val)
    rw [hκD]
    have h : a k * ((p k)⁻¹ * q).val = q.val :=
      congrArg Subtype.val (mul_inv_cancel_left (p k) q)
    exact congrArg (fun b : Z ≃ₐ[ℂ] Z => D (b z) (κ k (f ((p k)⁻¹ * q)).val)) h.symm
  let e := (Module.finBasis ℂ (Q → E.toSubmodule)).equivFun
  let τ := transportRepresentation P e
  let U := jointMultiplicitySpace ρ κ L.toSubgroup τ
  let : FiniteDimensional ℂ U := hJ L _ τ
  let v₀ : E.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan κ v⟩
  let f₀ : Q → E.toSubmodule := Pi.single (1 : Q) v₀
  let x := e f₀
  let ev : U →ₗ[ℂ] V := (LinearMap.applyₗ (R := ℂ) x).comp U.subtype
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range ev)
  rintro _ ⟨z, rfl⟩
  let φ := (T z).comp e.symm.toLinearMap
  have hφ : φ ∈ U := by
    refine ⟨fun w l => hTfix z (e.symm w) l, fun k w => ?_⟩
    change T z (e.symm (e (P k (e.symm w)))) = κ k (T z (e.symm w))
    rw [LinearEquiv.symm_apply_apply]
    exact hTκ z k (e.symm w)
  refine ⟨⟨φ, hφ⟩, ?_⟩
  change T z (e.symm (e f₀)) = D z v
  rw [LinearEquiv.symm_apply_apply]
  change (∑ q : Q, D (q.val z) (f₀ q).val) = D z v
  rw [Finset.sum_eq_single (1 : Q)]
  · simp only [f₀, Pi.single_eq_same]
    rfl
  · intro q _ hq
    simp only [f₀, Pi.single_eq_of_ne hq, Submodule.coe_zero, map_zero]
  · simp

/-- A finite-dimensional central orbit gives a single finite-codimensional
ideal annihilating the vector. -/
theorem exists_cofiniteIdeal_annihilates_of_finite_centralOrbit
    (D : Z →ₐ[ℂ] Module.End ℂ V) (v : V)
    (hv : FiniteDimensional ℂ (LinearMap.range (centralOrbitMap D v))) :
    ∃ I : Ideal Z, Module.Finite ℂ (Z ⧸ I.restrictScalars ℂ) ∧ ∀ z ∈ I, D z v = 0 := by
  let I : Ideal Z :=
    { carrier := {z | D z v = 0}
      zero_mem' := by simp
      add_mem' := fun {z w} hz hw => by
        change D (z + w) v = 0
        rw [map_add, LinearMap.add_apply, hz, hw, add_zero]
      smul_mem' := fun z {w} hw => by
        change D (z * w) v = 0
        rw [map_mul, Module.End.mul_apply, hw, map_zero] }
  let A := centralOrbitMap D v
  have hker : I.restrictScalars ℂ = A.ker := by
    ext z
    exact LinearMap.mem_ker.symm
  refine ⟨I, ?_, fun _ hz => hz⟩
  rw [hker]
  exact Module.Finite.of_injective (LinearMap.quotKerEquivRange A).toLinearMap
    (LinearMap.quotKerEquivRange A).injective

end Center

end Langlands
