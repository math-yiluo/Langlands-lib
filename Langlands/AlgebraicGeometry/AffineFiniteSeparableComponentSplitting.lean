import Langlands.AlgebraicGeometry.TensorSpectrumBaseChange
import Langlands.AlgebraicGeometry.GeometricallyIrreducibleClosedCover
import Langlands.CommutativeAlgebra.FiniteTensorIdealModel
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # Finite separable splitting for affine schemes of finite type -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open TensorSpectrumBaseChange
open Langlands.CommutativeAlgebra.TensorIdealDescent

variable (K L A : Type u) [Field K] [Field L] [CommRing A]
variable [Algebra K L] [Algebra K A]

/-- Descended ideals with irreducible supports over a separably closed extension
form a geometrically irreducible closed cover over their common coefficient field. -/
theorem componentsGeometricallyIrreducible_of_tensorIdealModel
    [IsSepClosed L] {ι : Type v} [Finite ι]
    (I : ι → Ideal (L ⊗[K] A))
    (hir : ∀ i, IsIrreducible (PrimeSpectrum.zeroLocus (I i : Set (L ⊗[K] A))))
    (hcover : (⋃ i, PrimeSpectrum.zeroLocus (I i : Set (L ⊗[K] A))) = Set.univ)
    (M : FiniteTensorIdealModel K L A I) :
    ComponentsGeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap M.fieldStage (M.fieldStage ⊗[K] A)))) := by
  rcases M with ⟨E, hE, J, hfg, hmap⟩
  let q := Spec.map (CommRingCat.ofHom (fieldTensorMap K E L A).toRingHom)
  let fE := Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] A)))
  let g := Spec.map (CommRingCat.ofHom (algebraMap E L))
  let R := CommRingCat.of (E ⊗[K] A)
  let : CommRing R := inferInstance
  let J' (i : ι) : Ideal R := J i
  let j (i : ι) := Spec.map (CommRingCat.ofHom (R := R) (Ideal.Quotient.mk (R := R) (J' i)))
  have hm (i : ι) : (J i).map (fieldTensorMap K E L A).toRingHom = I i :=
    hmap i
  have hj : ∀ i, IsClosedImmersion (j i) := fun i ↦
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hg : Surjective g := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have hq : Surjective q :=
    MorphismProperty.of_isPullback (isPullback_fieldTensorMap K E L A).flip hg
  apply componentsGeometricallyIrreducible_of_finite_closed_cover j fE
  · intro i
    apply geometricallyIrreducible_quotient_of_isSepClosed_baseChange K E L A
    simpa only [J', hm i] using hir i
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, rfl⟩ := q.surjective x
    have hy : y ∈ ⋃ i, PrimeSpectrum.zeroLocus (I i : Set (L ⊗[K] A)) := by
      rw [hcover]
      trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [show Set.range (j i) = PrimeSpectrum.zeroLocus (J i : Set (E ⊗[K] A))
      from range_spec_quotient (J i)]
    have he := preimage_zeroLocus_fieldTensorMap K E L A (J i)
    rw [hm i] at he
    exact show y ∈ q ⁻¹' PrimeSpectrum.zeroLocus (J i : Set (E ⊗[K] A)) from he ▸ hi

/-- A finite-type affine scheme has geometrically irreducible actual components
after one finite intermediate extension in a separable closure. -/
theorem exists_finite_separable_tensor_components [Algebra.FiniteType K A] :
    ∃ E : IntermediateField K (SeparableClosure K), FiniteDimensional K E ∧
      ComponentsGeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] A)))) := by
  let L := SeparableClosure K
  have : IsNoetherianRing (L ⊗[K] A) := Algebra.FiniteType.isNoetherianRing L (L ⊗[K] A)
  let ι := irreducibleComponents (PrimeSpectrum (L ⊗[K] A))
  let : Finite ι := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let I (C : ι) := PrimeSpectrum.vanishingIdeal C.val
  have hV (C : ι) : PrimeSpectrum.zeroLocus (I C : Set (L ⊗[K] A)) = C.val := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact (isClosed_of_mem_irreducibleComponents C.val C.property).closure_eq
  let M := FiniteTensorIdealModel.construct I (fun C ↦ IsNoetherian.noetherian (I C))
  refine ⟨M.fieldStage, M.finite, ?_⟩
  apply componentsGeometricallyIrreducible_of_tensorIdealModel K L A I
    (fun C ↦ (hV C).symm ▸ C.property.1) _ M
  simp_rw [hV]
  rw [Set.iUnion_coe_set, ← Set.sUnion_eq_biUnion, sUnion_irreducibleComponents]

/-- One finite coefficient field splitting the actual components of a finite-type affine scheme. -/
def affineComponentSplittingField [Algebra.FiniteType K A] :
    IntermediateField K (SeparableClosure K) :=
  Classical.choose (exists_finite_separable_tensor_components K A)

/-- The chosen coefficient field is finite over the original field. -/
theorem finite_affineComponentSplittingField [Algebra.FiniteType K A] :
    FiniteDimensional K (affineComponentSplittingField K A) :=
  (Classical.choose_spec (exists_finite_separable_tensor_components K A)).1

/-- The chosen coefficient field is separable over the original field. -/
theorem separable_affineComponentSplittingField [Algebra.FiniteType K A] :
    Algebra.IsSeparable K (affineComponentSplittingField K A) := inferInstance

/-- The actual components of the tensor spectrum over the chosen field are geometrically
irreducible with their vanishing-ideal reduced closed structures. -/
theorem componentsGeometricallyIrreducible_affineComponentSplittingField
    [Algebra.FiniteType K A] :
    ComponentsGeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom
        (algebraMap (affineComponentSplittingField K A)
          (affineComponentSplittingField K A ⊗[K] A)))) :=
  (Classical.choose_spec (exists_finite_separable_tensor_components K A)).2

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
