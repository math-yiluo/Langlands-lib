import Langlands.GroupScheme.Reductive.LocalRootGroupParam
import Langlands.CommutativeAlgebra.GradedLineFlatLocal

/-! # Root-group coordinates over an arbitrary local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Polynomial

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented LocalSplitCell

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)
  [Smooth G.X.hom]

/-- A homogeneous polynomial coordinate for the dynamic root group over any local ring.
The stated field-fibre data imply polynomiality even when the base has nilpotents. -/
theorem exists_coordinate_of_flat [IsLocalRing R] {m : ℕ} (hm0 : 0 < m)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ (α : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
        (Φ : Ga K ≅ UK i mu nu K),
        (∀ (Z : Over (Spec (CommRingCat.of K)))
            (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
          (t ≫ (tK i mu K).hom.hom) *
              (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map
                (jU i mu nu)).hom.hom) *
              (t ≫ (tK i mu K).hom.hom)⁻¹ =
            VectorGroup.weightPointAction α Z t x ≫
              (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) ∧
        latticePairing _ α (splitTorus.exponentCocharacter _ I nu) = m) :
    ∃ x ∈ CommutativeAlgebra.GradedLine.homog (isGrading_unipCoaction (unipCochar i mu nu)) m,
      Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu) := by
  have := finiteType_coordU i mu nu
  have : Algebra.Smooth (CommRingCat.of R) (coordU i mu nu) :=
    (DynamicSmooth.smooth_algSpec_iff _).1 (smooth_Uc i mu nu)
  obtain ⟨α, Φ, hΦ, hm⟩ := hfib (IsLocalRing.ResidueField R)
  exact CommutativeAlgebra.GradedLine.exists_aeval_bijective_of_flat_of_universal
    (isGrading_unipCoaction (unipCochar i mu nu))
    (fun a n hn => unipCoaction_coeff_neg (unipCochar i mu nu) a hn)
    (unipCoaction_coeff_zero (unipCochar i mu nu)) hm0
    (isUniversalLine_fibre i mu nu Φ)
    (CommutativeAlgebra.GradedLine.coeff_eq_zero_of_scaling hm0
      (scaling_fibre i mu nu Φ α hΦ m hm))

/-- A chosen polynomial-coordinate equivalence for the local dynamic root group. -/
def polynomialCoordinateEquiv [IsLocalRing R] {m : ℕ} (hm0 : 0 < m)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ (α : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
        (Φ : Ga K ≅ UK i mu nu K),
        (∀ (Z : Over (Spec (CommRingCat.of K)))
            (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
          (t ≫ (tK i mu K).hom.hom) *
              (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map
                (jU i mu nu)).hom.hom) *
              (t ≫ (tK i mu K).hom.hom)⁻¹ =
            VectorGroup.weightPointAction α Z t x ≫
              (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) ∧
        latticePairing _ α (splitTorus.exponentCocharacter _ I nu) = m) :
    R[X] ≃ₐ[R] coordU i mu nu :=
  let hex := exists_coordinate_of_flat i mu nu hm0 hfib
  AlgEquiv.ofBijective (Polynomial.aeval (Classical.choose hex)) (Classical.choose_spec hex).2

end Langlands.GroupScheme.LocalRootGroup
