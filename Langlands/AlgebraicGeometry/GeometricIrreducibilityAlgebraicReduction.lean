import Langlands.AlgebraicGeometry.GeometricIrreducibilityAssembly

universe u

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The ring-theoretic generic spreading assertion discharges the entire
arbitrary-scheme reduction. Its premise is the affine algebraic core. -/
theorem finiteTypeGeometricallyIrreducibleGenericSpreading_of_algebraic
    (hspread : ∀ (R : Type u) [CommRing R] [(nilradical R).IsPrime]
      (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
      (nilradical (AlgebraicClosure (nilradical R).ResidueField ⊗[R] B)).IsPrime →
        ∃ c : R, ¬ IsNilpotent c ∧
          ∀ (K : Type u) [Field K] (φ : R →+* K), φ c ≠ 0 →
            let : Algebra R K := φ.toAlgebra
            (nilradical (K ⊗[R] B)).IsPrime) :
    FiniteTypeGeometricallyIrreducibleGenericSpreading.{u} := by
  apply finiteTypeGeometricallyIrreducibleGenericSpreading_of_affine
  intro X Y _ _ f _ η hη hgeneric
  let R := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra R B := f.appTop.hom.toAlgebra
  have : Algebra.FiniteType R B :=
    HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance
  let η' : PrimeSpectrum R := Y.isoSpec.hom η
  have hη' : IsGenericPoint η' univ := by
    have himage := hη.image Y.isoSpec.hom.continuous
    have hrange : Set.range (fun y => Y.isoSpec.hom y) = univ :=
      Set.range_eq_univ.mpr Y.isoSpec.hom.homeomorph.surjective
    simpa only [Set.image_univ, hrange, closure_univ] using himage
  let : (nilradical R).IsPrime :=
    asIdeal_eq_nilradical_of_isGenericPoint hη' ▸ η'.isPrime
  have hgeneric' : GeometricallyIrreducible
      ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiberToSpecResidueField η') :=
    geometricallyIrreducible_fiber_of_arrowIso X.isoSpec Y.isoSpec
      (Scheme.isoSpec_hom_naturality f) η hgeneric
  have hprime : (nilradical
      (AlgebraicClosure (nilradical R).ResidueField ⊗[R] B)).IsPrime :=
    nilradical_isPrime_algebraicClosure_tensor_of_isGenericPoint R B η' hη' hgeneric'
  obtain ⟨c, hc, hfield⟩ := hspread R B hprime
  have hcη : η' ∈ PrimeSpectrum.basicOpen c :=
    (genericPoint_mem_basicOpen_iff hη' c).mpr hc
  have hgeom := geometricallyIrreducible_restrict_basicOpen_of_tensor R B c hfield
  refine ⟨Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen c, hcη, ?_⟩
  exact (geometricallyIrreducible_arrowIso_iff
    (arrowIso_morphismRestrict X.isoSpec Y.isoSpec
      (Scheme.isoSpec_hom_naturality f) (PrimeSpectrum.basicOpen c))).mpr hgeom

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
