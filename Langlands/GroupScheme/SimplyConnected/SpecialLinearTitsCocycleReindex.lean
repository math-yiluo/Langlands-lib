import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleTorus

/-! # Coordinate transport for the standard special-linear diagonal weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

variable (S : Scheme.{u}) {I J : Type u} [Finite I] [Finite J] (e : I ≃ J)

/-- The natural point equivalence which renames the factors of a split torus. -/
def reindexPoints (Z : Over S) :
    (Z ⟶ (splitTorus S I).X) ≃* (Z ⟶ (splitTorus S J).X) :=
  ((pointsEquiv I Z).trans (MulEquiv.arrowCongr e (MulEquiv.refl _))).trans
    (pointsEquiv J Z).symm

theorem pointsEquiv_reindexPoints (Z : Over S) (x : Z ⟶ (splitTorus S I).X) (j : J) :
    pointsEquiv J Z (reindexPoints S e Z x) j = pointsEquiv I Z x (e.symm j) := by
  simp [reindexPoints, MulEquiv.arrowCongr_apply]

theorem reindexPoints_naturality {Z Z' : Over S} (a : Z' ⟶ Z)
    (x : Z ⟶ (splitTorus S I).X) :
    reindexPoints S e Z' (a ≫ x) = a ≫ reindexPoints S e Z x := by
  apply (pointsEquiv J Z').injective
  funext j
  rw [pointsEquiv_reindexPoints, pointsEquiv_naturality]
  change Units.map a.left.appTop.hom.toMonoidHom (pointsEquiv I Z x (e.symm j)) =
    Units.map a.left.appTop.hom.toMonoidHom (pointsEquiv J Z (reindexPoints S e Z x) j)
  rw [pointsEquiv_reindexPoints]

/-- Renaming finite factors gives an actual isomorphism of split tori. -/
def reindexIso : splitTorus S I ≅ splitTorus S J :=
  isoOfPoints (reindexPoints S e) (fun {_ _} a x => reindexPoints_naturality S e a x)

theorem pointsEquiv_reindexIso_hom (Z : Over S) (x : Z ⟶ (splitTorus S I).X) (j : J) :
    pointsEquiv J Z (x ≫ (reindexIso S e).hom.hom.hom) j =
      pointsEquiv I Z x (e.symm j) := by
  rw [reindexIso, comp_isoOfPoints_hom, pointsEquiv_reindexPoints]

/-- The same factor-renaming isomorphism in commutative group schemes. -/
def commReindexIso : commGroupScheme S I ≅ commGroupScheme S J :=
  CommGroupScheme.isoOfGroupIso (reindexIso S e)

theorem commReindexIso_hom_comp_proj (j : J) :
    (commReindexIso S e).hom ≫ proj S J j = proj S I (e.symm j) := by
  apply CommGroupScheme.hom_ext_points
  intro Z x
  apply (Gm.pointsEquiv S Z).injective
  rw [comp_groupHom_comp, comp_proj, comp_proj]
  exact pointsEquiv_reindexIso_hom S e Z x j

variable (k : Type u) [Field k] [Fintype I] [Fintype J]

/-- Pullback along factor renaming reindexes the integral exponent vector. -/
theorem commReindexIso_hom_comp_character (m : J → ℤ) :
    (commReindexIso (Spec (CommRingCat.of k)) e).hom ≫
        (characterLatticeEquiv k J).symm m =
      (characterLatticeEquiv k I).symm (fun i => m (e i)) := by
  rw [characterLatticeEquiv_symm_eq, Preadditive.comp_sum,
    characterLatticeEquiv_symm_eq]
  simp_rw [Preadditive.comp_zsmul, commReindexIso_hom_comp_proj]
  exact (Fintype.sum_equiv e _ _ fun i => by simp).symm

end splitTorus

namespace SpecialLinear

variable {n : Type} [Fintype n] [DecidableEq n] (p : n) (k : Type u) [Field k]

/-- The diagonal-entry character is the character attached to its published exponent vector. -/
theorem diagonalWeight_eq_characterLatticeEquiv_symm (i : n) :
    diagonalWeight p (Spec (CommRingCat.of k)) i =
      (splitTorus.characterLatticeEquiv k (ULift.{u} (OffPivot p))).symm
        (fun c => weightCoord p i c.down) := by
  rw [splitTorus.characterLatticeEquiv_symm_eq]
  rfl

/-- Integral character coordinates of the diagonal-entry character. -/
theorem characterCoordEquiv_diagonalWeight (i : n) :
    GeneralLinear.characterCoordEquiv (OffPivot p) k
        (diagonalWeight p (Spec (CommRingCat.of k)) i) = weightCoord p i := by
  funext c
  rw [GeneralLinear.characterCoordEquiv_apply, diagonalWeight_eq_characterLatticeEquiv_symm,
    AddEquiv.apply_symm_apply]

/-- Weight differences agree with the corresponding integral-coordinate character. -/
theorem diagonalWeight_sub_eq_characterCoordEquiv_symm (i j : n) :
    diagonalWeight p (Spec (CommRingCat.of k)) i -
        diagonalWeight p (Spec (CommRingCat.of k)) j =
      (GeneralLinear.characterCoordEquiv (OffPivot p) k).symm
        (weightCoord p i - weightCoord p j) := by
  apply (GeneralLinear.characterCoordEquiv (OffPivot p) k).injective
  rw [map_sub, characterCoordEquiv_diagonalWeight, characterCoordEquiv_diagonalWeight,
    LinearEquiv.apply_symm_apply]

end SpecialLinear

end Langlands.GroupScheme
