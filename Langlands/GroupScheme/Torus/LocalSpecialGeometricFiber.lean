import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.IsomorphismLocus
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Comparing local special fibres and closed geometric fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSpecialGeometricFiber

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The ring-theoretic residue field and the scheme-theoretic residue field at
the closed point of a local spectrum are canonically isomorphic. -/
def closedPointResidueFieldIso :
    CommRingCat.of (IsLocalRing.ResidueField A) ≅
      (Spec (CommRingCat.of A)).residueField (IsLocalRing.closedPoint A) :=
  (RingEquiv.ofBijective
    (algebraMap (A ⧸ IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField _)).toCommRingCatIso ≪≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) (IsLocalRing.closedPoint A)).symm

/-- The residue-field comparison respects the actual maps to the local base. -/
theorem closedPointResidueFieldIso_comp_special :
    Spec.map (closedPointResidueFieldIso A).hom ≫
        Spec.algebraMap A (IsLocalRing.ResidueField A) =
      (Spec (CommRingCat.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [closedPointResidueFieldIso, Iso.trans_hom, Iso.symm_hom,
    Spec.map_comp, Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1

/-- The chosen geometric point at the closed point factors through the
ring-theoretic residue-field quotient. -/
def closedGeometricPointFactor :
    Spec (CommRingCat.of
      (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField (IsLocalRing.closedPoint A)))) ⟶
        Spec (CommRingCat.of (IsLocalRing.ResidueField A)) :=
  toAlgebraicClosure ((Spec (CommRingCat.of A)).residueField (IsLocalRing.closedPoint A)) ≫
    Spec.map (closedPointResidueFieldIso A).hom

theorem closedGeometricPointFactor_comp_special :
    closedGeometricPointFactor A ≫ Spec.algebraMap A (IsLocalRing.ResidueField A) =
      geometricPoint (Spec (CommRingCat.of A)) (IsLocalRing.closedPoint A) := by
  dsimp only [closedGeometricPointFactor, geometricPoint]
  rw [Category.assoc, closedPointResidueFieldIso_comp_special]

/-- The actual geometric fibre at the closed point is the indicated base
change of the ring-theoretic special fibre. -/
def specialGeometricFiberIso (G : GroupScheme (Spec (CommRingCat.of A))) :
    geometricFiber G (IsLocalRing.closedPoint A) ≅
      (GroupScheme.baseChange (closedGeometricPointFactor A)).obj
        ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G) :=
  eqToIso (congrArg (fun b => (GroupScheme.baseChange b).obj G)
    (closedGeometricPointFactor_comp_special A).symm) ≪≫
      baseChangeCompIso (Spec.algebraMap A (IsLocalRing.ResidueField A))
        (closedGeometricPointFactor A) G

/-- An isomorphism on the special fibre is an isomorphism on the chosen
geometric fibre at the closed point. -/
theorem isIso_geometric_of_special {G H : GroupScheme (Spec (CommRingCat.of A))}
    (j : G ⟶ H)
    [IsIso ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map j)] :
    IsIso ((GroupScheme.baseChange
      (geometricPoint (Spec (CommRingCat.of A)) (IsLocalRing.closedPoint A))).map j) := by
  rw [← closedGeometricPointFactor_comp_special A]
  exact (TorusIsomorphismLocus.isIso_comp_baseChange_iff
    (Spec.algebraMap A (IsLocalRing.ResidueField A)) (closedGeometricPointFactor A) j).mpr
      inferInstance

end Langlands.GroupScheme.LocalSpecialGeometricFiber
