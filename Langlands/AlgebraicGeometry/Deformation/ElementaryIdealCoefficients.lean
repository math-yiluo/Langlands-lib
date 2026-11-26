import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor
import Langlands.AlgebraicGeometry.SquareZeroAffineComparison
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # Constant coordinates of an elementary ideal on flat affine tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open IsLocalRing
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryIdealCoefficients

open SquareZeroAffinePairs ElementaryKernelTensor

@[instance_reducible] private def quotientModule {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (L : Ideal A) (hL : L ≤ Module.annihilator A M) : Module (A ⧸ L) M :=
  Module.compHom M (Ideal.Quotient.lift L (Module.toAddMonoidEnd A M) hL)

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (I : Ideal R) [hI : Fact (maximalIdeal R * I = ⊥)]
  (C : Type u) [CommRing C] [Algebra R C]

/-- The section ring of the residue fibre of an affine test. -/
abbrev Fibre := C ⧸ (maximalIdeal R).map (algebraMap R C)

/-- The scalar-extended ideal as a submodule of the original test ring. -/
abbrev Extended := I.map (algebraMap R C)

local notation "k" => ResidueField R
local notation "D" => Fibre (R := R) C
local notation "J" => Extended I C
local notation "mC" => Ideal.map (algebraMap R C) (maximalIdeal R)

/-- Quotient map of a test to its residue fibre. -/
abbrev reduce : C →+* D := Ideal.Quotient.mk mC

lemma extended_mul_maximal : mC * J = ⊥ := by
  rw [← Ideal.map_mul, hI.out, Ideal.map_bot]

lemma extended_squareZero (h : I ≤ maximalIdeal R) : J ^ 2 = ⊥ := by
  rw [pow_two]
  exact le_bot_iff.mp ((Ideal.mul_mono_left (Ideal.map_mono h)).trans_eq (extended_mul_maximal I C))

omit hI in
lemma reduce_extended (h : I ≤ maximalIdeal R) (x : J) : reduce (R := R) C x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.map_mono h x.property)

/-- The annihilating maximal ideal descends scalars on the original elementary ideal. -/
scoped instance residueModule : Module k I := quotientModule (maximalIdeal R) (by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  exact Ideal.mem_bot.mp (hI.out ▸ Ideal.mul_mem_mul hr x.property))

@[simp] lemma residue_smul (r : R) (x : I) : (residue R r) • x = r • x := rfl

scoped instance residueTower : IsScalarTower R k I := IsScalarTower.of_algebraMap_smul (residue_smul I)

scoped instance finiteResidueModule [IsArtinianRing R] : Module.Finite k I := by
  let f : I →ₛₗ[residue R] I :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ (residue_smul I r x).symm }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- The extended ideal is a module over the residue fibre ring. -/
scoped instance fibreModule : Module D J := quotientModule mC (by
  intro c hc
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  exact Ideal.mem_bot.mp (extended_mul_maximal I C ▸ Ideal.mul_mem_mul hc x.property))

@[simp] lemma reduce_smul (c : C) (x : J) : reduce (R := R) C c • x = c • x := rfl

scoped instance fibreTower : IsScalarTower C D J := IsScalarTower.of_algebraMap_smul (reduce_smul I C)

scoped instance fibreAlgebra : Algebra k D :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- The `k`-action is induced by the residue-fibre algebra. -/
scoped instance extendedResidueModule : Module k J := Module.compHom J (algebraMap k D)

scoped instance extendedResidueTower : IsScalarTower k D J := IsScalarTower.of_algebraMap_smul (by
  intro _ _; rfl)

/-- The original ideal maps into the extended ideal with its residue-field action. -/
def extend : I →ₗ[k] J where
  toFun x := ⟨algebraMap R C x, Ideal.mem_map_of_mem _ x.property⟩
  map_add' x y := Subtype.ext (map_add (algebraMap R C) (x : R) (y : R))
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := residue_surjective a
    apply Subtype.ext
    rw [RingHom.id_apply, residue_smul]
    change algebraMap R C (r * (x : R)) = algebraMap R C r * algebraMap R C (x : R)
    exact map_mul _ _ _

/-- Canonical map of residue coefficients to the extended ideal. -/
def fibreTensorMap : D ⊗[k] I →ₗ[D] J := (extend I C).liftBaseChange D

@[simp] theorem fibreTensorMap_tmul (c : C) (x : I) :
    (fibreTensorMap I C (reduce (R := R) C c ⊗ₜ[k] x)).val =
      c * algebraMap R C x.val := by
  rw [fibreTensorMap, LinearMap.liftBaseChange_tmul, reduce_smul]
  rfl

private theorem fibreTensorMap_bijective [Module.Flat R C] :
    Function.Bijective (fibreTensorMap I C) := by
  let : Algebra C (k ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
  let eD : D ≃ₐ[k] k ⊗[R] C :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (maximalIdeal R)
  let E := TensorProduct.congr eD.toLinearEquiv (LinearEquiv.refl k I)
  let e := (coefficientTensorEquiv (A := R) (K := k) (R := C) (M := I)).toAddEquiv.trans
    (idealTensorEquiv (R := C) I).toAddEquiv
  suffices (fibreTensorMap I C : D ⊗[k] I → J) = e ∘ E by
    rw [this]
    exact e.bijective.comp E.bijective
  funext x
  induction x using TensorProduct.inductionOn with
  | tmul d a =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective d
    apply Subtype.ext
    change (fibreTensorMap I C (reduce (R := R) C c ⊗ₜ[k] a)).val = _
    rw [fibreTensorMap_tmul]
    change c * algebraMap R C a.val = (idealTensorEquiv I
      (coefficientTensorEquiv (eD (reduce (R := R) C c) ⊗ₜ[k] a))).val
    rw [show eD (reduce (R := R) C c) = 1 ⊗ₜ[R] c from rfl,
      coefficientTensorEquiv_tmul, one_smul, idealTensorEquiv_tmul, mul_comm]
  | add x y hx hy =>
    simp only [Function.comp_apply] at hx hy ⊢
    rw [map_add, map_add, map_add, hx, hy]

/-- Over a flat affine test the coefficient map identifies the extended ideal with
extension of the original residue vector space. -/
def fibreTensorEquiv [Module.Flat R C] : D ⊗[k] I ≃ₗ[D] J :=
  LinearEquiv.ofBijective (fibreTensorMap I C) (fibreTensorMap_bijective I C)

variable {C} {C' : Type u} [CommRing C'] [Algebra R C'] (f : C →ₐ[R] C')

omit [IsLocalRing R] hI in
lemma map_extended_le : Ideal.map f.toRingHom J ≤ Extended I C' := by
  rw [Ideal.map_map]
  change Ideal.map ((f : C →+* C').comp (algebraMap R C)) I ≤ _
  rw [f.comp_algebraMap]

/-- Residue-fibre algebra map associated with a map of tests. -/
def fibreMap : Fibre (R := R) C →ₐ[k] Fibre (R := R) C' where
  __ := Ideal.quotientMap ((maximalIdeal R).map (algebraMap R C')) f.toRingHom (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_map]
    change Ideal.map ((f : C →+* C').comp (algebraMap R C)) (maximalIdeal R) ≤ _
    rw [f.comp_algebraMap])
  commutes' x := by
    obtain ⟨r, rfl⟩ := residue_surjective x
    change Ideal.Quotient.mk _ (f (algebraMap R C r)) =
      Ideal.Quotient.mk _ (algebraMap R C' r)
    rw [f.commutes]

@[simp] theorem fibreMap_reduce (c : C) : fibreMap f (reduce (R := R) C c) =
    reduce (R := R) C' (f c) := rfl

/-- The map of the actual extended ideals, linear over the map of residue fibres. -/
def extendedMap : J →ₛₗ[(fibreMap f).toRingHom] Extended I C' :=
  mapReducedIdeal J (reduce (R := R) C) Ideal.Quotient.mk_surjective (reduce_smul I C)
    (Extended I C') (reduce (R := R) C') (reduce_smul I C') f.toRingHom (map_extended_le I f)
    (fibreMap f).toRingHom (RingHom.ext fun _ ↦ rfl)

@[simp] lemma extendedMap_val (x : J) : (extendedMap I f x).val = f x.val := rfl

variable {ι : Type*}

/-- The basis on an extended elementary ideal obtained by flat base change. -/
def extendedBasis (b : Module.Basis ι k I) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] : Module.Basis ι (Fibre (R := R) T) (Extended I T) :=
  (b.baseChange (Fibre (R := R) T)).map (fibreTensorEquiv I T)

@[simp] theorem extendedBasis_val (b : Module.Basis ι k I) (T : Type u) [CommRing T]
    [Algebra R T] [Module.Flat R T] (i : ι) :
    (extendedBasis I b T i).val = algebraMap R T (b i).val := by
  change (fibreTensorMap I T ((b.baseChange (Fibre (R := R) T)) i)).val = _
  rw [Module.Basis.baseChange_apply, ← map_one (reduce (R := R) T), fibreTensorMap_tmul, one_mul]

/-- Coordinates in the extended basis restrict along the residue-fibre ring map. -/
theorem extendedBasis_equivFun_map [Fintype ι] (b : Module.Basis ι k I)
    [Module.Flat R C] [Module.Flat R C'] (x : J) (i : ι) :
    (extendedBasis I b C').equivFun (extendedMap I f x) i =
      fibreMap f ((extendedBasis I b C).equivFun x i) := by
  have h := congrArg (extendedMap I f) ((extendedBasis I b C).sum_repr x)
  rw [map_sum] at h
  have hb (j : ι) : extendedMap I f (extendedBasis I b C j) = extendedBasis I b C' j := by
    apply Subtype.ext
    rw [extendedMap_val, extendedBasis_val, extendedBasis_val, f.commutes]
  simp only [map_smulₛₗ, hb] at h
  rw [← h, map_sum]
  classical
  simp [Module.Basis.equivFun_apply, Finsupp.single_apply, mul_ite]

end Langlands.AlgebraicGeometry.Deformation.ElementaryIdealCoefficients
