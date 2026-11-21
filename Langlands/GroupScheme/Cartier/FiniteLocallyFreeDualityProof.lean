import Langlands.GroupScheme.Cartier.FiniteLocallyFreeDualityStatement
import Langlands.GroupScheme.Cartier.FiniteDualAffineCharacters
import Langlands.GroupScheme.Cartier.FiniteDualGeometry
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Finite locally free Cartier duality over an affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier

namespace FiniteDual

variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]

/-- The character comparison is an isomorphism on all tests by Zariski descent. -/
def characterIso :
    additivePoints (specGroup R (Dual R A)).toGrp ≅ characters (specGroup R A) := by
  haveI : IsIso (characterComparison R A) :=
    isIso_additivePoints_characters_of_bijective (characterComparison R A)
      (fun C _ _ => (affineCharacterEquiv R A C).bijective)
  exact asIso (characterComparison R A)

@[simp] theorem characterIso_apply (T : Over (Spec R)) (y : T ⟶ (specGroup R (Dual R A)).X) :
    (characterIso R A).hom.app (op T) (Additive.ofMul y) = characterOfPoint R A y := rfl

set_option maxHeartbeats 2600000 in
private theorem dualityOfSpectrum :
    ∃ (D : CommGroupScheme (Spec R))
      (dual : additivePoints D.toGrp ≅ characters (specGroup R A))
      (bidual : additivePoints (specGroup R A).toGrp ≅ characters D),
      IsFinite D.X.hom ∧ Flat D.X.hom ∧ LocallyOfFinitePresentation D.X.hom ∧
        ∀ (T : Over (Spec R)) (x : T ⟶ (specGroup R A).X) (y : T ⟶ D.X),
          evaluation (bidual.hom.app (op T) (Additive.ofMul x)) y =
            evaluation (dual.hom.app (op T) (Additive.ofMul y)) x := by
  let D := specGroup R (Dual R A)
  let G₂ := specGroup R (Dual R (Dual R A))
  let e : specGroup R A ≅ G₂ := CommGroupScheme.isoOfGroupIso
    ((hopfSpec R).mapIso (CommHopfAlgCat.isoMk (bidualEquiv R A).symm).op)
  obtain ⟨hFinite, hFlat, hPresentation⟩ := algSpec_finiteLocallyFree (R := R) (Dual R A)
  refine ⟨D, characterIso R A, additivePointsIso e ≪≫ characterIso R (Dual R A),
    hFinite, hFlat, hPresentation, ?_⟩
  intro T x y
  simp only [Iso.trans_hom, NatTrans.comp_app, AddCommGrpCat.comp_apply,
    additivePointsIso_hom_app]
  have he : (CommGroupScheme.groupHom e.hom).hom.hom =
      specMap (bidualEquiv R A).symm.toAlgEquiv.toAlgHom := rfl
  rw [he]
  let x₂ : T ⟶ G₂.X := x ≫ specMap (bidualEquiv R A).symm.toAlgEquiv.toAlgHom
  erw [characterIso_apply R (Dual R A) T x₂, characterIso_apply R A T y]
  exact (characterOfPoint_evaluation R (Dual R A) x₂ y).trans
    ((schemePairing_bidual R A T x y).trans (characterOfPoint_evaluation R A y x).symm)

end FiniteDual

open FiniteDual

/-- Finite locally free Cartier duality and its evaluation equation on every test scheme. -/
theorem finiteLocallyFreeCartierDuality : FiniteLocallyFreeCartierDualityStatement := by
  intro R G hFinite hFlat hPresentation
  have : IsAffine G.X.left := isAffine_of_isFinite G.toGrp
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  have : Coalgebra.IsCocomm R A := affineCoordinates_isCocomm G
  have : Module.Finite R A := hopfAlgebra_finite G.toGrp
  have : Module.Projective R A := hopfAlgebra_projective G.toGrp
  let e : specGroup R A ≅ G := CommGroupScheme.isoOfGroupIso (AffineCoordinates.hopfSpecIso G.toGrp)
  exact finiteCartierDual_of_iso e.symm (dualityOfSpectrum R A)

end Langlands.GroupScheme.Cartier
