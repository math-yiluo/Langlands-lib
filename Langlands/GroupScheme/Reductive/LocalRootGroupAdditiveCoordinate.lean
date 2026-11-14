import Langlands.GroupScheme.Reductive.LocalRootGroupFlatCoordinate
import Langlands.GroupScheme.Dynamic.UnipotentPrimitiveCoordinate

/-! # Additive root-group coordinates over arbitrary local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Polynomial

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented LocalSplitCell

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

/-- A positive homogeneous algebra generator is additive on all root-group points. -/
theorem coordX_mul_of_homogeneous {m : ℕ} (hm : 0 < m) {x : coordU i mu nu}
    (hxm : x ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (unipCochar i mu nu)) m)
    (hx : Function.Surjective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    {T : Over (Spec (CommRingCat.of R))} (y y' : T ⟶ (Uc i mu nu).X) :
    coordX i mu nu x (y * y') = coordX i mu nu x y + coordX i mu nu x y' :=
  UnipotentPrimitive.appTop_mul (unipCochar i mu nu) hm hxm hx y y'

/-- A positive homogeneous polynomial coordinate gives an additive-group isomorphism. -/
def gaIsoUOfHomogeneous {m : ℕ} (hm : 0 < m) (x : coordU i mu nu)
    (hxm : x ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (unipCochar i mu nu)) m)
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu)) :
    Ga R ≅ Uc i mu nu :=
  gaIsoU i mu nu x hx (fun _ => coordX_mul_of_homogeneous i mu nu hm hxm hx.2)

/-- The additive-group isomorphism has the chosen coordinate. -/
theorem coordX_gaIsoUOfHomogeneous {m : ℕ} (hm : 0 < m) (x : coordU i mu nu)
    (hxm : x ∈ CommutativeAlgebra.GradedLine.homog
      (isGrading_unipCoaction (unipCochar i mu nu)) m)
    (hx : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu))
    (T : Over (Spec (CommRingCat.of R))) (c : Γ(T.left, ⊤)) :
    coordX i mu nu x (VectorGroup.scalarPoint _ T c ≫
      (gaIsoUOfHomogeneous i mu nu hm x hxm hx).hom.hom.hom) = c :=
  coordX_gaIsoU i mu nu x hx (fun _ => coordX_mul_of_homogeneous i mu nu hm hxm hx.2) T c

/-- The dynamic root group is an additive group over an arbitrary local ring,
given the equivariant positive-weight field-fibre data. -/
theorem nonempty_gaIsoU_of_flat [Smooth G.X.hom] [IsLocalRing R] {m : ℕ} (hm0 : 0 < m)
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
    Nonempty (Ga R ≅ Uc i mu nu) := by
  obtain ⟨x, hxm, hx⟩ := exists_coordinate_of_flat i mu nu hm0 hfib
  exact ⟨gaIsoUOfHomogeneous i mu nu hm0 x hxm hx⟩

end Langlands.GroupScheme.LocalRootGroup
