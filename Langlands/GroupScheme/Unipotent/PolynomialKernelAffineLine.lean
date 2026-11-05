import Langlands.GroupScheme.Unipotent.AdditiveKernelGeometry
import Langlands.GroupScheme.Rational.AffineLineExtensions
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionStatement

/-! # Affine-line maps and central additive subgroups of polynomial kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k] {n : ℕ}

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))

/-- Polynomial coordinates of an actual affine-line map to the standard vector
 group, obtained from the global-function bijection. -/
def affineLinePolynomialCoordinates
    (a : A ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) : Fin n → k[X] :=
  fun i => Classical.choose
    (AdditiveGroupQuotient.bijective_eval₂RingHom_affineLine.surjective
      ((VectorGroup.coordinates (CommRingCat.of k) n A a).toAdd i))

/-- Evaluation recovers each actual global coordinate of the affine-line map. -/
@[simp]
theorem affineLinePolynomialCoordinates_eval
    (a : A ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) (i : Fin n) :
    (affineLinePolynomialCoordinates a i).eval₂ (AdditiveGroupQuotient.structureMap A)
      (AffineLine.coord (Spec (CommRingCat.of k))) =
        (VectorGroup.coordinates (CommRingCat.of k) n A a).toAdd i :=
  Classical.choose_spec
    (AdditiveGroupQuotient.bijective_eval₂RingHom_affineLine.surjective
      ((VectorGroup.coordinates (CommRingCat.of k) n A a).toAdd i))

/-- Every actual affine-line map into an additive polynomial kernel has polynomial
coordinates satisfying the exact separated-variable kernel equation. -/
theorem exists_polynomial_coordinates_of_kernel_affineLine_map
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (a : A ⟶ (kernel (polynomialRow f hf)).X) :
    ∃ φ : Fin n → k[X],
      (∀ i, (φ i).eval₂ (AdditiveGroupQuotient.structureMap A)
        (AffineLine.coord (Spec (CommRingCat.of k))) =
          (VectorGroup.coordinates (CommRingCat.of k) n A
            (a ≫ (kernelι (polynomialRow f hf)).hom.hom)).toAdd i) ∧
      (∑ i, (f i).comp (φ i)) = 0 := by
  classical
  let E : k[X] →+* Γ((A).left, ⊤) :=
    eval₂RingHom (AdditiveGroupQuotient.structureMap A)
      (AffineLine.coord (Spec (CommRingCat.of k)))
  have hE : Function.Bijective E :=
    AdditiveGroupQuotient.bijective_eval₂RingHom_affineLine
  let φ := affineLinePolynomialCoordinates (a ≫ (kernelι (polynomialRow f hf)).hom.hom)
  have hφ := affineLinePolynomialCoordinates_eval
    (a ≫ (kernelι (polynomialRow f hf)).hom.hom)
  refine ⟨φ, hφ, ?_⟩
  have hker : (a ≫ (kernelι (polynomialRow f hf)).hom.hom) ≫
      (polynomialRow f hf).hom.hom = 1 :=
    (kernelPointsEquiv (polynomialRow f hf) A a).property
  have hc := congrArg (fun b =>
    (VectorGroup.coordinates (CommRingCat.of k) 1 A b).toAdd 0) hker
  rw [comp_polynomialRow, polynomialRowPoints_coord] at hc
  simp only [map_one, toAdd_one, Pi.zero_apply] at hc
  apply hE.injective
  rw [map_sum, map_zero]
  change (∑ i, eval₂ (AdditiveGroupQuotient.structureMap A)
    (AffineLine.coord (Spec (CommRingCat.of k))) ((f i).comp (φ i))) = 0
  simpa only [eval₂_comp, show ∀ i, eval₂ (AdditiveGroupQuotient.structureMap A)
    (AffineLine.coord (Spec (CommRingCat.of k))) (φ i) =
      (VectorGroup.coordinates (CommRingCat.of k) n A
        (a ≫ (kernelι (polynomialRow f hf)).hom.hom)).toAdd i from hφ] using hc

/-- Failure of actual affine-line constancy yields a nonconstant polynomial
kernel curve, without any assumption on the cardinality of the field. -/
theorem hasNonconstantPolynomialKernelCurve_of_not_hasConstantAffineLineMaps
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hG : ¬ HasConstantAffineLineMaps (kernel (polynomialRow f hf))) :
    HasNonconstantPolynomialKernelCurve f := by
  classical
  by_contra h
  apply hG
  intro a
  obtain ⟨φ, hφ, hrel⟩ :=
    exists_polynomial_coordinates_of_kernel_affineLine_map f hf a
  have hdeg : ∀ i, (φ i).natDegree = 0 := by
    intro i
    by_contra hi
    exact h ⟨φ, ⟨i, Nat.pos_of_ne_zero hi⟩, hrel⟩
  have hb : ∀ i, (VectorGroup.coordinates (CommRingCat.of k) n A
      (a ≫ (kernelι (polynomialRow f hf)).hom.hom)).toAdd i =
        AdditiveGroupQuotient.structureMap A ((φ i).coeff 0) := by
    intro i
    rw [← hφ i, eq_C_of_natDegree_eq_zero (hdeg i), eval₂_C, coeff_C_zero]
  let ρ : A ⟶ A := toUnit A ≫ AffineLine.zeroSection (Spec (CommRingCat.of k))
  refine ⟨AffineLine.zeroSection (Spec (CommRingCat.of k)) ≫ a, ?_⟩
  apply (cancel_mono (kernelι (polynomialRow f hf)).hom.hom).mp
  apply (VectorGroup.coordinates (CommRingCat.of k) n A).injective
  apply Multiplicative.toAdd.injective
  change (VectorGroup.coordinates (CommRingCat.of k) n A
    (a ≫ (kernelι (polynomialRow f hf)).hom.hom)).toAdd =
    (VectorGroup.coordinates (CommRingCat.of k) n A
      (ρ ≫ (a ≫ (kernelι (polynomialRow f hf)).hom.hom))).toAdd
  rw [VectorGroup.coordinates_comp ρ (a ≫ (kernelι (polynomialRow f hf)).hom.hom)]
  funext i
  rw [hb i]
  change AdditiveGroupQuotient.structureMap A ((φ i).coeff 0) =
    (ρ.left.appTop.hom.comp (AdditiveGroupQuotient.structureMap A)) ((φ i).coeff 0)
  rw [AdditiveGroupQuotient.structureMap_comp]

end Langlands.GroupScheme.Unipotent
