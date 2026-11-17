import Langlands.GroupScheme.Torus.ExponentCharacters
import Langlands.GroupScheme.Reductive.RelativeRootScalingTorus

/-! # Products of exponent characters and coordinate permutations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable (S : Scheme.{u}) {I J K : Type u} [Fintype I] [Fintype J] [Fintype K]

/-- The product of a finite family of actual exponent characters over any base. -/
def characterProjection (m : J → I → ℤ) : splitTorus S I ⟶ splitTorus S J :=
  Pi.lift fun j => CommGroupScheme.groupHom (exponentCharacter S I (m j))

/-- The product of characters evaluates as the specified monomials on every test. -/
theorem characterProjection_points (m : J → I → ℤ) (U : Over S)
    (x : U ⟶ (splitTorus S I).X) (j : J) :
    pointsEquiv J U (x ≫ (characterProjection S m).hom.hom) j =
      ∏ i, pointsEquiv I U x i ^ m j i := by
  rw [pointsEquiv_apply, Category.assoc, ← Grp.comp_hom_hom]
  simp only [characterProjection, Pi.lift_comp_π]
  exact pointsEquiv_exponentCharacter S I (m j) x

/-- On an affine base this is the existing monomial projection. -/
theorem characterProjection_eq_exponentTorusProjection (R : CommRingCat.{u})
    (m : J → I → ℤ) :
    characterProjection (Spec R) m = exponentTorusProjection R m := by
  apply hom_ext_points
  intro U x
  apply (pointsEquiv J U).injective
  funext j
  rw [characterProjection_points, exponentTorusProjection_points]

/-- The actual coordinate permutation, with target coordinate `j` equal to source `e j`. -/
def coordinatePermutationIso (e : J ≃ I) : splitTorus S I ≅ splitTorus S J where
  hom := Pi.lift fun j => Pi.π (fun _ : I => (Gm S).toGrp) (e j)
  inv := Pi.lift fun i => Pi.π (fun _ : J => (Gm S).toGrp) (e.symm i)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    simp
  inv_hom_id := by
    apply Pi.hom_ext
    intro j
    simp

/-- The coordinate permutation has its expected formula on arbitrary test schemes. -/
theorem coordinatePermutationIso_hom_points (e : J ≃ I) (U : Over S)
    (x : U ⟶ (splitTorus S I).X) (j : J) :
    pointsEquiv J U (x ≫ (coordinatePermutationIso S e).hom.hom.hom) j =
      pointsEquiv I U x (e j) := by
  rw [pointsEquiv_apply, Category.assoc, ← Grp.comp_hom_hom]
  simp only [coordinatePermutationIso, Pi.lift_comp_π]
  rfl

/-- Coordinate reindexing respects the identity equivalence as an actual group-scheme map. -/
theorem coordinatePermutationIso_refl : coordinatePermutationIso S (Equiv.refl I) = Iso.refl _ := by
  apply Iso.ext
  apply Pi.hom_ext
  intro i
  simp [coordinatePermutationIso]

/-- Coordinate reindexing respects composition, in its contravariant convention. -/
theorem coordinatePermutationIso_trans (e : J ≃ I) (f : K ≃ J) :
    coordinatePermutationIso S e ≪≫ coordinatePermutationIso S f = coordinatePermutationIso S (f.trans e) := by
  apply Iso.ext
  apply Pi.hom_ext
  intro k
  simp [coordinatePermutationIso]

/-- Actual character transport which permutes the chosen exponents gives precisely
the corresponding coordinate permutation after the character projections. -/
theorem characterProjection_comp_reindex
    {I' : Type u} [Fintype I']
    (τ : splitTorus S I ⟶ splitTorus S I')
    (f : (I' → ℤ) →ₗ[ℤ] (I → ℤ))
    (hτ : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X) (n : I' → ℤ),
      ∏ a, pointsEquiv I' U (x ≫ τ.hom.hom) a ^ n a =
        ∏ a, pointsEquiv I U x a ^ f n a)
    (m : J → I → ℤ) (n : K → I' → ℤ) (e : K ≃ J)
    (hm : ∀ k, f (n k) = m (e k)) :
    τ ≫ characterProjection S n =
      characterProjection S m ≫ (coordinatePermutationIso S e).hom := by
  apply hom_ext_points
  intro U x
  apply (pointsEquiv K U).injective
  funext k
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [characterProjection_points, coordinatePermutationIso_hom_points,
    characterProjection_points, hτ, hm]

/-- Every fixed finite family of character projections commutes with arbitrary base change. -/
theorem characterProjection_baseChange {S' : Scheme.{u}} (a : S' ⟶ S)
    (m : J → I → ℤ) :
    (baseChangeIso a I).hom ≫ characterProjection S' m =
      (GroupScheme.baseChange a).map (characterProjection S m) ≫
        (baseChangeIso a J).hom := by
  apply hom_ext_points
  intro U x
  apply (pointsEquiv J U).injective
  funext j
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [characterProjection_points, pointsEquiv_baseChangeIso_hom,
    pointsEquiv_baseChangeIso_hom]
  change (∏ i, pointsEquiv I ((Over.map a).obj U)
      (GroupScheme.baseChangePointsEquiv a _ U x) i ^ m j i) =
    pointsEquiv J ((Over.map a).obj U)
      (GroupScheme.baseChangePointsEquiv a _ U
        (x ≫ ((GroupScheme.baseChange a).map (characterProjection S m)).hom.hom)) j
  rw [GroupScheme.baseChangePointsEquiv_comp, characterProjection_points]

end Langlands.GroupScheme.splitTorus
