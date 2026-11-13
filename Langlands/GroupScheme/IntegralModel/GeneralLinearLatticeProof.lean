import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Proof: the general linear integral model attached to a full lattice -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace GeneralLinear

section MatrixAlgebra

variable {R K : Type u} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {n : ℕ}

/-- An invertible matrix over the fraction field comes from `GL_n(R)` exactly when it and its
inverse both have all entries in `R`. -/
theorem mem_range_map_iff_exists_map (X : GL (Fin n) K) :
    X ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range ↔
      (∃ C : Matrix (Fin n) (Fin n) R, C.map (algebraMap R K) = (X : Matrix (Fin n) (Fin n) K)) ∧
      ∃ D : Matrix (Fin n) (Fin n) R,
        D.map (algebraMap R K) = ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  constructor
  · rintro ⟨Y, rfl⟩
    refine ⟨⟨(Y : Matrix (Fin n) (Fin n) R), rfl⟩, ⟨((Y⁻¹ : GL (Fin n) R) : Matrix _ _ R), ?_⟩⟩
    rw [← map_inv]
    rfl
  · rintro ⟨⟨C, hC⟩, ⟨D, hD⟩⟩
    have hinj : Function.Injective ((algebraMap R K).mapMatrix (m := Fin n)) :=
      Matrix.map_injective (IsFractionRing.injective R K)
    have hCD : C * D = 1 := hinj (by
      rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hC, hD]
      exact X.mul_inv)
    have hDC : D * C = 1 := hinj (by
      rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hC, hD]
      exact X.inv_mul)
    refine ⟨⟨C, D, hCD, hDC⟩, ?_⟩
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact congrFun (congrFun hC i) j

end MatrixAlgebra

section Lattice

variable {R K : Type u} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {n : ℕ}
  {Λ : Submodule R (Fin n → K)} [Submodule.IsLattice K Λ]
  (b : Module.Basis (Fin n) R Λ)

/-- The `K`-linear automorphism of `K^n` sending the standard basis to an `R`-basis of the
lattice. -/
def latticeCoordEquiv : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  (b.extendOfIsLattice K).equivFun.symm

theorem latticeCoordEquiv_apply (c : Fin n → K) :
    latticeCoordEquiv b c = ∑ j, c j • (b j : Fin n → K) := by
  simp [latticeCoordEquiv, Module.Basis.equivFun_symm_apply]

theorem latticeCoordEquiv_single (j : Fin n) :
    latticeCoordEquiv b (Pi.single j 1) = (b j : Fin n → K) := by
  simp [latticeCoordEquiv]

/-- The lattice is the image of the integral coordinate vectors. -/
theorem mem_lattice_iff (v : Fin n → K) :
    v ∈ Λ ↔ ∃ c : Fin n → R, latticeCoordEquiv b (fun i => algebraMap R K (c i)) = v := by
  constructor
  · intro hv
    refine ⟨b.repr ⟨v, hv⟩, ?_⟩
    rw [latticeCoordEquiv_apply]
    conv_rhs => rw [show v = ((⟨v, hv⟩ : Λ) : Fin n → K) from rfl, ← b.sum_repr ⟨v, hv⟩]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul_of_tower, algebraMap_smul]
  · rintro ⟨c, rfl⟩
    rw [latticeCoordEquiv_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [algebraMap_smul]
    exact Λ.smul_mem _ (b j).2

/-- The invertible matrix whose columns are the vectors of an `R`-basis of the lattice. -/
def latticeMatrix : GL (Fin n) K where
  val := LinearMap.toMatrix' (latticeCoordEquiv b : (Fin n → K) →ₗ[K] (Fin n → K))
  inv := LinearMap.toMatrix' ((latticeCoordEquiv b).symm : (Fin n → K) →ₗ[K] (Fin n → K))
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro v
    simp [Module.End.mul_apply]
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro v
    simp [Module.End.mul_apply]

theorem latticeMatrix_mulVec (v : Fin n → K) :
    (latticeMatrix b : Matrix (Fin n) (Fin n) K) *ᵥ v = latticeCoordEquiv b v :=
  LinearMap.toMatrix'_mulVec _ v

theorem latticeMatrix_inv_mulVec (v : Fin n → K) :
    ((latticeMatrix b)⁻¹ : GL (Fin n) K) *ᵥ v = (latticeCoordEquiv b).symm v :=
  LinearMap.toMatrix'_mulVec _ v

/-- A matrix carries the lattice into itself exactly when its conjugate by the lattice matrix
has all entries in `R`. -/
theorem forall_mulVec_mem_iff (A : Matrix (Fin n) (Fin n) K) :
    (∀ v ∈ Λ, A *ᵥ v ∈ Λ) ↔
      ∃ C : Matrix (Fin n) (Fin n) R, C.map (algebraMap R K) =
        (((latticeMatrix b)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A *
          (latticeMatrix b : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro h
    have hc : ∀ j, ∃ c : Fin n → R,
        latticeCoordEquiv b (fun i => algebraMap R K (c i)) = A *ᵥ (b j : Fin n → K) :=
      fun j => (mem_lattice_iff b _).1 (h _ (b j).2)
    choose c hc using hc
    refine ⟨Matrix.of fun i j => c j i, ?_⟩
    ext i j
    have hcol : ((((latticeMatrix b)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A *
        (latticeMatrix b : Matrix (Fin n) (Fin n) K)) *ᵥ Pi.single j 1 =
          fun i => algebraMap R K (c j i) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, latticeMatrix_mulVec,
        latticeMatrix_inv_mulVec, latticeCoordEquiv_single, ← hc j,
        LinearEquiv.symm_apply_apply]
    have hij := congrFun hcol i
    rw [Matrix.mulVec_single_one] at hij
    rw [Matrix.map_apply, Matrix.of_apply]
    exact hij.symm
  · rintro ⟨C, hC⟩ v hv
    obtain ⟨c, rfl⟩ := (mem_lattice_iff b v).1 hv
    refine (mem_lattice_iff b _).2 ⟨C *ᵥ c, ?_⟩
    have hmap : (fun i => algebraMap R K ((C *ᵥ c) i)) =
        C.map (algebraMap R K) *ᵥ fun i => algebraMap R K (c i) :=
      funext fun i => RingHom.map_mulVec (algebraMap R K) C c i
    rw [hmap, hC, ← latticeMatrix_mulVec, ← latticeMatrix_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul]

/-- **The lattice stabilizer.** A rational point of `GL_n` stabilizes the lattice exactly when
its matrix, conjugated by the lattice matrix, lies in the image of `GL_n(R)`. -/
theorem stabilizesLattice_iff [IsDomain R]
    (g : rationalPoints (groupScheme (Fin n) (CommRingCat.of K))) :
    StabilizesLattice Λ g ↔
      (latticeMatrix b)⁻¹ * rationalPointsEquiv n (CommRingCat.of K) g * latticeMatrix b ∈
        (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range := by
  rw [mem_range_map_iff_exists_map]
  unfold StabilizesLattice
  rw [forall_mulVec_mem_iff b, forall_mulVec_mem_iff b]
  have hinv : ((latticeMatrix b)⁻¹ * rationalPointsEquiv n (CommRingCat.of K) g *
      latticeMatrix b)⁻¹ =
        (latticeMatrix b)⁻¹ * (rationalPointsEquiv n (CommRingCat.of K) g)⁻¹ * latticeMatrix b := by
    group
  rw [hinv, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
  simp only [Matrix.coe_units_inv]

end Lattice

section ConjugatedModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] {n : ℕ}

/-- The standard general linear group over `R`, whose generic identification is the standard
base-change identification followed by the inner automorphism of `GL_n` over `K` given by
conjugation by the rational point with matrix `B`. -/
def conjugatedStandardIntegralModel (B : Langlands.GeneralLinear n K) :
    IntegralModel R K (groupScheme (Fin n) (CommRingCat.of K)) where
  group := (standardIntegralModel R K (Fin n)).group
  affine := (standardIntegralModel R K (Fin n)).affine
  flat := (standardIntegralModel R K (Fin n)).flat
  finiteType := (standardIntegralModel R K (Fin n)).finiteType
  genericIso := (standardIntegralModel R K (Fin n)).genericIso ≪≫
    (groupScheme (Fin n) (CommRingCat.of K)).innerIso
      ((rationalPointsEquiv n (CommRingCat.of K)).symm B)

/-- The conjugated model has the same group as the standard model, hence is smooth. -/
theorem conjugatedStandardIntegralModel_isSmooth (B : Langlands.GeneralLinear n K) :
    (conjugatedStandardIntegralModel R K B).IsSmooth :=
  smoothStatement (Fin n) (CommRingCat.of R)

/-- The identity of the group is an isomorphism from the standard model to the conjugated
model over the inner automorphism. -/
def conjugatedStandardIntegralModelIso (B : Langlands.GeneralLinear n K) :
    (standardIntegralModel R K (Fin n)).Iso (conjugatedStandardIntegralModel R K B)
      ((groupScheme (Fin n) (CommRingCat.of K)).innerIso
        ((rationalPointsEquiv n (CommRingCat.of K)).symm B)) where
  iso := CategoryTheory.Iso.refl (standardIntegralModel R K (Fin n)).group
  generic_comm := by
    erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Integral points of the conjugated model.** -/
theorem mem_conjugatedStandardIntegralModel_integralPoints_iff
    (B : Langlands.GeneralLinear n K)
    (g : rationalPoints (groupScheme (Fin n) (CommRingCat.of K))) :
    g ∈ (conjugatedStandardIntegralModel R K B).integralPoints ↔
      B⁻¹ * rationalPointsEquiv n (CommRingCat.of K) g * B ∈
        (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap R K)).range := by
  rw [← (conjugatedStandardIntegralModelIso R K B).map_integralPoints, Subgroup.mem_map]
  set p := (rationalPointsEquiv n (CommRingCat.of K)).symm B with hp
  have hpB : rationalPointsEquiv n (CommRingCat.of K) p = B := MulEquiv.apply_symm_apply _ _
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [mem_standardIntegralModel_integralPoints_iff] at hh
    rw [rationalPoints_map_innerIso, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, hpB]
    convert hh using 1
    group
  · intro hg
    refine ⟨p⁻¹ * g * p, ?_, ?_⟩
    · rw [mem_standardIntegralModel_integralPoints_iff, map_mul, map_mul, map_inv, hpB]
      exact hg
    · rw [rationalPoints_map_innerIso, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end ConjugatedModel

end GeneralLinear

open _root_.Langlands.GroupScheme.GeneralLinear in
/-- **The general linear integral model of a full lattice.** For a basis `b` of the lattice
`Λ`, the standard model with generic identification twisted by conjugation by the basis matrix
`B` is smooth and its integral points are exactly the stabilizer of `Λ`. -/
theorem generalLinearLatticeIntegralModel :
    GeneralLinearLatticeIntegralModelStatement.{u} := by
  intro R K _ _ _ _ _ _ n Λ hΛ
  have := hΛ
  have hrank : Module.finrank R Λ = n := by
    rw [Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]
  let b : Module.Basis (Fin n) R Λ := Module.finBasisOfFinrankEq R Λ hrank
  refine ⟨conjugatedStandardIntegralModel R K (latticeMatrix b),
    conjugatedStandardIntegralModel_isSmooth R K _, fun g => ?_⟩
  rw [mem_conjugatedStandardIntegralModel_integralPoints_iff, stabilizesLattice_iff b]

end Langlands.GroupScheme
