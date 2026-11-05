import Langlands.CommutativeAlgebra.FiniteSeparablePolynomialModel

/-! # Monic finite free models over a ring with a domain quotient -/

noncomputable section

universe u v w z

open scoped TensorProduct
open Algebra Polynomial IntermediateField

namespace Langlands.CommutativeAlgebra

/-- Base change of the actual monic quotient, with the coefficient tensor
product cancelled to the originally specified scalar algebra. -/
def adjoinRootBaseChangeEquiv (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (p : R[X]) :
    S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot (p.map (algebraMap R S)) :=
  (AdjoinRoot.tensorAlgEquiv p _ rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R S S) _ _
      (Associated.of_eq (by
        rw [Polynomial.map_map]
        congr 1
        ext r
        simp [Algebra.smul_def])))

@[simp]
theorem adjoinRootBaseChangeEquiv_root (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (p : R[X]) :
    adjoinRootBaseChangeEquiv R S p (1 ⊗ₜ[R] AdjoinRoot.root p) =
      AdjoinRoot.root (p.map (algebraMap R S)) := by
  simp only [adjoinRootBaseChangeEquiv, AlgEquiv.trans_apply,
    AdjoinRoot.tensorAlgEquiv_root, AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

@[simp]
theorem adjoinRootBaseChangeEquiv_of (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (p : R[X]) (r : R) :
    adjoinRootBaseChangeEquiv R S p (1 ⊗ₜ[R] AdjoinRoot.of p r) =
      AdjoinRoot.of (p.map (algebraMap R S)) (algebraMap R S r) := by
  simp only [adjoinRootBaseChangeEquiv, AlgEquiv.trans_apply,
    AdjoinRoot.tensorAlgEquiv_of, AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  simp [Algebra.smul_def]

variable (R : Type u) (D : Type v) (K : Type w) (L : Type z)
  [CommRing R] [CommRing D] [IsDomain D] [Field K] [Field L]
  [Algebra R D] [Algebra D K] [IsFractionRing D K]
  [Algebra D L] [Algebra K L] [IsScalarTower D K L]

/-- Lift the published domain model through a surjective coefficient map.
The actual model is the monic quotient over the original, possibly nonreduced ring. -/
structure FiniteSeparableLiftedPolynomialModel where
  quotientModel : FiniteSeparablePolynomialModel D K L
  polynomial : R[X]
  monic : polynomial.Monic
  map_eq : polynomial.map (algebraMap R D) = quotientModel.polynomial

/-- Existence uses only surjectivity onto the domain and the specified finite
separable extension of its fraction field. -/
theorem nonempty_finiteSeparableLiftedPolynomialModel
    (hsurj : Function.Surjective (algebraMap R D))
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Nonempty (FiniteSeparableLiftedPolynomialModel R D K L) := by
  let d := finiteSeparablePolynomialModel D K L
  have hlifts : d.polynomial ∈ Polynomial.lifts (algebraMap R D) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => hsurj _
  obtain ⟨p, hp, _, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts d.monic
  exact ⟨⟨d, p, hpm, hp⟩⟩

/-- A chosen actual lifted monic model of the specified extension. -/
def finiteSeparableLiftedPolynomialModel
    (hsurj : Function.Surjective (algebraMap R D))
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteSeparableLiftedPolynomialModel R D K L :=
  Classical.choice (nonempty_finiteSeparableLiftedPolynomialModel R D K L hsurj)

namespace FiniteSeparableLiftedPolynomialModel

variable {R D K L}

abbrev Carrier (d : FiniteSeparableLiftedPolynomialModel R D K L) :=
  AdjoinRoot d.polynomial

instance finite (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    Module.Finite R d.Carrier := d.monic.finite_adjoinRoot

instance free (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    Module.Free R d.Carrier := d.monic.free_adjoinRoot

instance finitePresentation (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    Algebra.FinitePresentation R d.Carrier := inferInstance

/-- Reduction is the original actual subalgebra model inside `L`. -/
def reductionEquiv (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    D ⊗[R] d.Carrier ≃ₐ[D] d.quotientModel.Carrier :=
  (adjoinRootBaseChangeEquiv R D d.polynomial).trans
    ((AdjoinRoot.algEquivOfAssociated D _ _ (Associated.of_eq d.map_eq)).trans
      d.quotientModel.presentation.toIsAdjoinRoot.adjoinRootAlgEquiv)

omit [IsDomain D] in
@[simp]
theorem reductionEquiv_tmul_root (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    d.reductionEquiv (1 ⊗ₜ[R] AdjoinRoot.root d.polynomial) =
      (⟨d.quotientModel.generator,
        Algebra.self_mem_adjoin_singleton D d.quotientModel.generator⟩ :
        d.quotientModel.Carrier) := by
  simp only [reductionEquiv, AlgEquiv.trans_apply, adjoinRootBaseChangeEquiv_root,
    AdjoinRoot.algEquivOfAssociated_root, IsAdjoinRoot.adjoinRootAlgEquiv_apply_root]
  simp [IsAdjoinRoot.root, FiniteSeparablePolynomialModel.presentation]

/-- The coefficient reduction map on the actual quotient rings. -/
def reductionMap (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    d.Carrier →+* d.quotientModel.Carrier :=
  d.reductionEquiv.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

@[simp]
theorem reductionMap_root (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    d.reductionMap (AdjoinRoot.root d.polynomial) =
      (⟨d.quotientModel.generator,
        Algebra.self_mem_adjoin_singleton D d.quotientModel.generator⟩ :
        d.quotientModel.Carrier) :=
  d.reductionEquiv_tmul_root

omit [IsDomain D] in
@[simp]
theorem reductionMap_of (d : FiniteSeparableLiftedPolynomialModel R D K L) (r : R) :
    d.reductionMap (AdjoinRoot.of d.polynomial r) =
      algebraMap D d.quotientModel.Carrier (algebraMap R D r) := by
  change d.reductionEquiv (1 ⊗ₜ[R] algebraMap R d.Carrier r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R D (D ⊗[R] d.Carrier), AlgEquiv.commutes]

omit [IsDomain D] in
theorem reductionMap_surjective (d : FiniteSeparableLiftedPolynomialModel R D K L)
    (hsurj : Function.Surjective (algebraMap R D)) :
    Function.Surjective d.reductionMap :=
  d.reductionEquiv.surjective.comp
    (Algebra.TensorProduct.includeRight_surjective d.Carrier hsurj)

variable [Algebra R K] [IsScalarTower R D K]

omit [IsDomain D] [IsFractionRing D K] [IsScalarTower D K L] in
theorem map_eq_minpoly (d : FiniteSeparableLiftedPolynomialModel R D K L) :
    d.polynomial.map (algebraMap R K) = minpoly K d.quotientModel.generator := by
  rw [IsScalarTower.algebraMap_eq R D K, ← Polynomial.map_map,
    d.map_eq, d.quotientModel.map_eq_minpoly]

/-- The generic tensor product is the original specified field extension. -/
def genericEquiv (d : FiniteSeparableLiftedPolynomialModel R D K L)
    [Algebra.IsAlgebraic K L] : K ⊗[R] d.Carrier ≃ₐ[K] L :=
  (adjoinRootBaseChangeEquiv R K d.polynomial).trans
    ((AdjoinRoot.algEquivOfAssociated K _ _ (Associated.of_eq d.map_eq_minpoly)).trans
      (IsAdjoinRoot.mkOfPrimitiveElement
        (Algebra.IsIntegral.isIntegral d.quotientModel.generator)
        d.quotientModel.primitive).adjoinRootAlgEquiv)

omit [IsDomain D] [IsFractionRing D K] [IsScalarTower D K L] in
@[simp]
theorem genericEquiv_tmul_root (d : FiniteSeparableLiftedPolynomialModel R D K L)
    [Algebra.IsAlgebraic K L] :
    d.genericEquiv (1 ⊗ₜ[R] AdjoinRoot.root d.polynomial) = d.quotientModel.generator := by
  simp [genericEquiv]

/-- The map from the actual lifted quotient into the original extension field. -/
def genericMap (d : FiniteSeparableLiftedPolynomialModel R D K L)
    [Algebra.IsAlgebraic K L] : d.Carrier →+* L :=
  d.genericEquiv.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

omit [IsDomain D] [IsFractionRing D K] [IsScalarTower D K L] in
@[simp]
theorem genericMap_root (d : FiniteSeparableLiftedPolynomialModel R D K L)
    [Algebra.IsAlgebraic K L] :
    d.genericMap (AdjoinRoot.root d.polynomial) = d.quotientModel.generator :=
  d.genericEquiv_tmul_root

omit [IsDomain D] [IsFractionRing D K] in
@[simp]
theorem genericMap_of (d : FiniteSeparableLiftedPolynomialModel R D K L)
    [Algebra.IsAlgebraic K L] (r : R) :
    d.genericMap (AdjoinRoot.of d.polynomial r) =
      algebraMap D L (algebraMap R D r) := by
  change d.genericEquiv (1 ⊗ₜ[R] algebraMap R d.Carrier r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R K (K ⊗[R] d.Carrier), AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply R D K, ← IsScalarTower.algebraMap_apply D K L]

/-- Reduction and generic base change preserve the same original coefficient
map and the same actual primitive element inside `L`. -/
theorem genericMap_eq_reductionMap (d : FiniteSeparableLiftedPolynomialModel R D K L)
    [Algebra.IsAlgebraic K L] :
    d.genericMap = d.quotientModel.Carrier.val.toRingHom.comp d.reductionMap := by
  apply AdjoinRoot.ringHom_ext
  · ext r
    simp
  · simp

end FiniteSeparableLiftedPolynomialModel

end Langlands.CommutativeAlgebra
