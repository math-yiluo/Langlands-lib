import Langlands.Global.AdelicRepresentationHeight
import Langlands.Global.PrimitiveAdelicBasis

/-! # Rational-subgroup minima for actual representation-vector heights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {n : ℕ}
  (ρ : MatrixRepresentation G (Fin n))

/-- The actual representation matrix on rational group points. -/
def rationalMatrix : RationalGroupPoints F G →* RationalGL F n :=
  ρ.affineMatrix (CommAlgCat.of F F)

/-- The actual adelic representation of a principal point is the entrywise principal matrix.
This comparison uses naturality of the given algebraic representation. -/
theorem adelicMatrix_rational (q : RationalGroupPoints F G) :
    adelicMatrix F G ρ (AdelicGroupPoints.rational F G q) =
      AdelicGL.rational F n (rationalMatrix F G ρ q) := by
  exact ρ.affineMatrix_naturality
    (CommAlgCat.ofHom (Algebra.ofId F (Adeles F))) q

/-- The published normalized primitive-vector height pulled back along the actual algebraic
representation, for a fixed rational vector. This is a vector height, rather than the
matrix-and-inverse height. -/
def orbitHeight (v : Fin n → F) (g : AdelicGroupPoints F G) : ℝ :=
  PrimitiveAdelicHeight.rationalHeight F n (adelicMatrix F G ρ g) v

theorem orbitHeight_pos {v : Fin n → F} (hv : v ≠ 0) (g : AdelicGroupPoints F G) :
    0 < orbitHeight F G ρ v g :=
  PrimitiveAdelicHeight.rationalHeight_pos F n _ v hv

/-- Right rational translation acts on the fixed rational vector through the actual
rational representation. -/
theorem orbitHeight_mul_rational (v : Fin n → F) (g : AdelicGroupPoints F G)
    (q : RationalGroupPoints F G) :
    orbitHeight F G ρ v (g * AdelicGroupPoints.rational F G q) =
      orbitHeight F G ρ ((rationalMatrix F G ρ q).val *ᵥ v) g := by
  simp only [orbitHeight, map_mul, adelicMatrix_rational]
  exact PrimitiveAdelicHeight.rationalHeight_mul_rational F n _ _ _

/-- Every rational subgroup has a height-minimizing translate for one nonzero rational
vector in one actual algebraic representation. The subgroup need not be algebraic. -/
theorem exists_min_orbitHeight (Q : Subgroup (RationalGroupPoints F G))
    (v : Fin n → F) (hv : v ≠ 0) (g : AdelicGroupPoints F G) :
    ∃ q : Q, ∀ r : Q,
      orbitHeight F G ρ v (g * AdelicGroupPoints.rational F G q) ≤
        orbitHeight F G ρ v (g * AdelicGroupPoints.rational F G r) := by
  let S : Set (Fin n → F) :=
    Set.range (fun q : Q => (rationalMatrix F G ρ q).val *ᵥ v)
  have hS : S.Nonempty := ⟨_, (1 : Q), rfl⟩
  have hzero : (0 : Fin n → F) ∉ S := by
    rintro ⟨q, hq⟩
    exact PrimitiveAdelicHeight.rational_mulVec_ne_zero F n _ hv hq
  obtain ⟨w, ⟨q, rfl⟩, hmin⟩ :=
    PrimitiveAdelicHeight.exists_min_rationalHeight_on F n (adelicMatrix F G ρ g)
      S hS hzero
  refine ⟨q, fun r => ?_⟩
  simp only [orbitHeight_mul_rational]
  exact hmin _ ⟨r, rfl⟩

/-- A chosen minimizing element of the same actual rational subgroup. -/
def minimumOrbitTranslate (Q : Subgroup (RationalGroupPoints F G))
    (v : Fin n → F) (hv : v ≠ 0) (g : AdelicGroupPoints F G) : Q :=
  (exists_min_orbitHeight F G ρ Q v hv g).choose

/-- The chosen translate cannot be improved by further right translation in that subgroup.
This is the one-representation minimum step used in reduction-theoretic height arguments. -/
theorem minimumOrbitTranslate_min (Q : Subgroup (RationalGroupPoints F G))
    (v : Fin n → F) (hv : v ≠ 0) (g : AdelicGroupPoints F G) (r : Q) :
    orbitHeight F G ρ v
        (g * AdelicGroupPoints.rational F G (minimumOrbitTranslate F G ρ Q v hv g)) ≤
      orbitHeight F G ρ v
        ((g * AdelicGroupPoints.rational F G (minimumOrbitTranslate F G ρ Q v hv g)) *
          AdelicGroupPoints.rational F G r) := by
  have h := (exists_min_orbitHeight F G ρ Q v hv g).choose_spec
    (minimumOrbitTranslate F G ρ Q v hv g * r)
  simpa only [minimumOrbitTranslate, Subgroup.coe_mul, map_mul, mul_assoc] using h

end Langlands.Global.RepresentationGrowth
