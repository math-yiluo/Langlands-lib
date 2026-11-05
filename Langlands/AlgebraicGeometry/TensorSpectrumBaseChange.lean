import Langlands.AlgebraicGeometry.GeometricIrreducibilityFieldCriteria
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Scalar extension of tensor spectra and closed supports -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

namespace Langlands.AlgebraicGeometry.TensorSpectrumBaseChange

variable (K E L A : Type u) [Field K] [Field E] [Field L] [CommRing A]
variable [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Algebra K A]

/-- Extension of the field coefficient in a tensor product. -/
def fieldTensorMap : E ⊗[K] A →ₐ[K] L ⊗[K] A :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K A)

/-- Tensor spectra form the actual scalar-extension square. -/
theorem isPullback_fieldTensorMap :
    IsPullback (Spec.map (CommRingCat.ofHom (fieldTensorMap K E L A).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap E L))) := by
  have hE := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct K E A)
  have hL := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct K L A)
  have h₁ : Spec.map (CommRingCat.ofHom (fieldTensorMap K E L A).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[K] E ⊗[K] A).toRingHom) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp [fieldTensorMap]
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Spec.map_comp]
    congr 1
    ext k
    exact (IsScalarTower.algebraMap_apply K E L k).symm
  have hw : Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E L)) =
      Spec.map (CommRingCat.ofHom (fieldTensorMap K E L A).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] A))) := by
    simp only [← Spec.map_comp]
    congr 1
  apply IsPullback.flip
  apply IsPullback.of_bot (p := hw) (t := hE)
  simpa only [h₁, h₂] using hL

/-- Closed supports pull back by extension of their defining ideal. -/
theorem preimage_zeroLocus_fieldTensorMap (J : Ideal (E ⊗[K] A)) :
    (Spec.map (CommRingCat.ofHom (fieldTensorMap K E L A).toRingHom)) ⁻¹'
      (PrimeSpectrum.zeroLocus (J : Set (E ⊗[K] A))) =
    PrimeSpectrum.zeroLocus ((J.map (fieldTensorMap K E L A).toRingHom :
      Ideal (L ⊗[K] A)) : Set (L ⊗[K] A)) := by
  change PrimeSpectrum.comap _ ⁻¹' _ = _
  rw [PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span,
    ← Ideal.map_span, Ideal.span_eq]
  rfl

/-- The quotient immersion has exactly the ideal's zero locus as range. -/
theorem range_spec_quotient {R : Type u} [CommRing R] (J : Ideal R) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      PrimeSpectrum.zeroLocus (J : Set R) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = _
  rw [range_comap_of_surjective _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

/-- Irreducible support after extension to a separably closed field gives geometric
irreducibility of the actual quotient scheme before extension. -/
theorem geometricallyIrreducible_quotient_of_isSepClosed_baseChange [IsSepClosed L]
    (J : Ideal (E ⊗[K] A))
    (hJ : IsIrreducible (PrimeSpectrum.zeroLocus
      ((J.map (fieldTensorMap K E L A).toRingHom : Ideal (L ⊗[K] A)) : Set (L ⊗[K] A)))) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] A)))) := by
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have : IsClosedImmersion j :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let q := Spec.map (CommRingCat.ofHom (fieldTensorMap K E L A).toRingHom)
  let fE := Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] A)))
  let fL := Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A)))
  let g := Spec.map (CommRingCat.ofHom (algebraMap E L))
  have hg : Surjective g := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have hr : Set.range (pullback.snd j q) = PrimeSpectrum.zeroLocus
      ((J.map (fieldTensorMap K E L A).toRingHom : Ideal (L ⊗[K] A)) : Set (L ⊗[K] A)) := by
    rw [Scheme.Pullback.range_snd]
    dsimp only [j, q]
    rw [range_spec_quotient, preimage_zeroLocus_fieldTensorMap]
  have hir : IsIrreducible (Set.range (pullback.snd j q)) := hr ▸ hJ
  have : IrreducibleSpace (Set.range (pullback.snd j q)) :=
    isIrreducible_iff_irreducibleSpace.mp hir
  have : IrreducibleSpace (pullback j q : Scheme.{u}) :=
    (pullback.snd j q).isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr inferInstance
  have hgi : GeometricallyIrreducible (pullback.snd j q ≫ fL) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed _
  have hbase : IsPullback (pullback.fst j q) (pullback.snd j q ≫ fL) (j ≫ fE) g :=
    ((IsPullback.of_hasPullback j q).flip.paste_horiz
      (isPullback_fieldTensorMap K E L A).flip).flip
  have : GeometricallyIrreducible (pullback.snd (j ≫ fE) g) := by
    rw [← hbase.isoPullback_inv_snd, geometricallyIrreducible_iff]
    rw [MorphismProperty.cancel_left_of_respectsIso
      (geometrically (fun X : Scheme.{u} => IrreducibleSpace X)) hbase.isoPullback.inv]
    exact hgi.geometrically_irreducibleSpace
  exact geometricallyIrreducible_of_surjective_baseChange (j ≫ fE) g

end Langlands.AlgebraicGeometry.TensorSpectrumBaseChange
