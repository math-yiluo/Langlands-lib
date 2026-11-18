import Langlands.GroupScheme.Torus.LocalSpecialGeometricFiber
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcTransfer
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable

/-! # Actual diagonalizations of local special fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSpecialGeometricFiber

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- Multiplicative type of the chosen closed geometric fibre implies
multiplicative type of the ring-theoretic special fibre. -/
theorem specialFiber_isMultiplicativeType
    (G : GroupScheme (Spec (CommRingCat.of A)))
    (hG : IsMultiplicativeType (geometricFiber G (IsLocalRing.closedPoint A))) :
    IsMultiplicativeType
      ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G) := by
  let k := IsLocalRing.ResidueField A
  let K := AlgebraicClosure
    ((Spec (CommRingCat.of A)).residueField (IsLocalRing.closedPoint A))
  let b := closedGeometricPointFactor A
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  apply IsMultiplicativeType.of_fieldExtension (k := k) (K := K)
  change IsMultiplicativeType ((GroupScheme.baseChange
    (Spec.map (Spec.preimage b))).obj _)
  rw [Spec.map_preimage]
  exact hG.of_iso (specialGeometricFiberIso A G).symm

/-- A character group and an actual diagonalization of the special fibre
using exactly the base change of the relative model over the local ring. -/
structure SpecialFiberDiagonalization
    (G : GroupScheme (Spec (CommRingCat.of A))) where
  characters : Type u
  [characterGroup : AddCommGroup characters]
  [finitelyGenerated : AddGroup.FG characters]
  iso : (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj
      (RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of A)) characters) ≅
    (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G

attribute [instance] SpecialFiberDiagonalization.characterGroup
  SpecialFiberDiagonalization.finitelyGenerated

/-- Choose the special-fibre diagonalization required by strict-Henselian
clopen lifting, directly from the closed geometric-fibre hypothesis. -/
def specialFiberDiagonalization [IsSepClosed (IsLocalRing.ResidueField A)]
    (G : GroupScheme (Spec (CommRingCat.of A)))
    (hG : IsMultiplicativeType (geometricFiber G (IsLocalRing.closedPoint A))) :
    SpecialFiberDiagonalization A G :=
  Classical.choice (by
    obtain ⟨M, hM, hfg, ⟨e⟩⟩ :=
      MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _
        (specialFiber_isMultiplicativeType A G hG)
    exact ⟨{
      characters := M
      characterGroup := hM
      finitelyGenerated := hfg
      iso := RelativeMultiplicativeType.diagonalizableBaseChangeIso
        (Spec.algebraMap A (IsLocalRing.ResidueField A)) M ≪≫
          (Diagonalizable.relativeModelIso
            (CommRingCat.of (IsLocalRing.ResidueField A)) M).symm ≪≫ e.symm }⟩)

end Langlands.GroupScheme.LocalSpecialGeometricFiber
