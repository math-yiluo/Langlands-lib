import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Exponent weights of the actual adjoint action over arbitrary rings -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

variable {R : CommRingCat.{u}} (I : Type u) [Fintype I] [DecidableEq I]

/-- The monomial of an integral exponent, evaluated at the actual universal
point of a split torus over any commutative ring. -/
theorem exponentValue_universalPoint_ring (m : I → ℤ) :
    exponentValue I (algebraPointsEquiv I _ (universalPoint (R := R) I))
      (Multiplicative.ofAdd m) = exponentUnit I m := by
  rw [algebraPointsEquiv_universalPoint]
  let f := (AddMonoidAlgebra.of R (I → ℤ)).toHomUnits
  let h : (I → ℤ) →+ Additive (AddMonoidAlgebra R (I → ℤ))ˣ :=
    { toFun := fun n => Additive.ofMul (f (Multiplicative.ofAdd n))
      map_zero' := congrArg Additive.ofMul (map_one f)
      map_add' := fun n p => congrArg Additive.ofMul
        (map_mul f (Multiplicative.ofAdd n) (Multiplicative.ofAdd p)) }
  have hm : (∑ j : I, m j • Pi.single j (1 : ℤ)) = m := by
    ext j
    simp [Pi.single_apply]
  have hh := congrArg Additive.toMul
    (map_sum h (fun j => m j • Pi.single j (1 : ℤ)) Finset.univ)
  rw [hm] at hh
  simp only [map_zsmul] at hh
  simpa [h, f, exponentValue, exponentUnit] using hh.symm

variable (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec R) I ⟶ G)

/-- The integral-exponent weight space of the actual adjoint action. Its
equation is required on every test algebra over the arbitrary base ring. -/
def exponentWeightSpace (m : I → ℤ) : Submodule R (Additive (lieKernel G R)) where
  carrier := {X | ∀ (A : Type u) [CommRing A] [Algebra R A] (t : I → Aˣ),
    adjoint G A ((algebraPointsEquiv I A).symm t ≫ i.hom.hom)
        (lieKernelMapLinear G (Algebra.ofId R A) X) =
      (exponentValue I t (Multiplicative.ofAdd m) : A) •
        lieKernelMapLinear G (Algebra.ofId R A) X}
  zero_mem' := by
    intro A _ _ t
    rw [map_zero, map_zero, smul_zero]
  add_mem' := by
    intro X Y hX hY A _ _ t
    rw [map_add, map_add, hX A t, hY A t, smul_add]
  smul_mem' := by
    intro c X hX A _ _ t
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, hX A t, smul_comm]

variable [LocallyOfFiniteType G.X.hom]

/-- Each universal adjoint coefficient belongs to its actual exponent weight space. -/
theorem universalAdjointCoefficients_mem_exponentWeightSpace
    (X : Additive (lieKernel G R)) (m : I → ℤ) :
    universalAdjointCoefficients I G i X m ∈ exponentWeightSpace I G i m :=
  fun _ _ _ t => universalAdjointCoefficients_weight I G i t X m

/-- A vector satisfying the all-test exponent equation has a coefficient
family concentrated at that exponent. -/
theorem universalAdjointCoefficients_of_mem_exponentWeightSpace
    (m : I → ℤ) (X : Additive (lieKernel G R))
    (hX : X ∈ exponentWeightSpace I G i m) :
    universalAdjointCoefficients I G i X = Finsupp.single m X := by
  apply universalAdjointCoefficients_of_monomial
  have h := hX (AddMonoidAlgebra R (I → ℤ))
    (algebraPointsEquiv I _ (universalPoint (R := R) I))
  rw [MulEquiv.symm_apply_apply, exponentValue_universalPoint_ring] at h
  exact h

open Classical in
/-- The actual adjoint Lie module is the internal direct sum of its
integral-exponent weight spaces over an arbitrary base ring. -/
@[instance_reducible]
def exponentAdjointDecomposition :
    DirectSum.Decomposition (exponentWeightSpace I G i) :=
  Langlands.LinearAlgebra.finsuppDecomposition _
    (universalAdjointCoefficients I G i)
    (universalAdjointCoefficients_mem_exponentWeightSpace I G i)
    (fun m X => universalAdjointCoefficients_of_mem_exponentWeightSpace
      I G i m X X.property)
    (universalAdjointCoefficients_sum I G i)

/-- The integral-exponent weight spaces form an internal direct sum. -/
theorem isInternal_exponentWeightSpace :
    DirectSum.IsInternal (exponentWeightSpace I G i) := by
  let := exponentAdjointDecomposition I G i
  exact DirectSum.Decomposition.isInternal _

/-- The actual weight projection is the corresponding universal adjoint coefficient. -/
def exponentProjection (m : I → ℤ) :
    Additive (lieKernel G R) →ₗ[R] exponentWeightSpace I G i m where
  toFun X := ⟨universalAdjointCoefficients I G i X m,
    universalAdjointCoefficients_mem_exponentWeightSpace I G i X m⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [map_add, Finsupp.add_apply, Submodule.coe_add]
  map_smul' c X := by
    apply Subtype.ext
    simp only [map_smul, Finsupp.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply]

@[simp]
theorem exponentProjection_apply (m : I → ℤ) (X : Additive (lieKernel G R)) :
    (exponentProjection I G i m X : Additive (lieKernel G R)) =
      universalAdjointCoefficients I G i X m := rfl

@[simp]
theorem exponentProjection_subtype (m : I → ℤ)
    (X : exponentWeightSpace I G i m) :
    exponentProjection I G i m X = X := by
  classical
  apply Subtype.ext
  change universalAdjointCoefficients I G i X m = _
  rw [universalAdjointCoefficients_of_mem_exponentWeightSpace I G i m X X.property,
    Finsupp.single_eq_same]

/-- Every actual exponent weight space is a direct summand of the actual Lie module. -/
theorem exponentProjection_comp_subtype (m : I → ℤ) :
    (exponentProjection I G i m).comp (exponentWeightSpace I G i m).subtype =
      LinearMap.id := by
  apply LinearMap.ext
  intro X
  exact exponentProjection_subtype I G i m X

end Langlands.GroupScheme.splitTorus

namespace Langlands.GroupScheme.splitTorus

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

omit [DecidableEq I] in
/-- Over a field, the relative exponent weight space is precisely the
existing actual character weight space with the same exponent. -/
theorem exponentWeightSpace_eq_weightSpace (m : I → ℤ) :
    exponentWeightSpace I G i m =
      weightSpace i ((characterLatticeEquiv k I).symm m) := by
  ext X
  constructor
  · intro h A _ _ t
    have h' := h A (algebraPointsEquiv I A t)
    rw [MulEquiv.symm_apply_apply,
      ← characterValue_characterLatticeEquiv_symm k I] at h'
    exact h'
  · intro h A _ _ t
    have h' := (mem_weightSpace.mp h) A ((algebraPointsEquiv I A).symm t)
    rw [characterValue_characterLatticeEquiv_symm, MulEquiv.apply_symm_apply] at h'
    exact h'

end Langlands.GroupScheme.splitTorus
