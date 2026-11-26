import Langlands.Global.AdelicWeilTopology
import Langlands.Global.AdelicWeilNormOneQuotient
import Langlands.GroupScheme.AffineWeilBilinearSpecialFibre

/-! # Naturality of the adelic Weil point comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {G H : GroupScheme (Spec (CommRingCat.of L))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The canonical comparison of full adelic points commutes with a group homomorphism. -/
theorem adelicPointsEquiv_map (f : G ⟶ H)
    (x : AdelicGroupPoints K (AffineWeil.groupScheme K L G)) :
    adelicPointsEquiv K L H (AdelicGroupPoints.map K _ _ (AffineWeil.map K L f) x) =
      AdelicGroupPoints.map L G H f (adelicPointsEquiv K L G x) := by
  rw [adelicPointsEquiv_apply, adelicPointsEquiv_apply]
  change H.affinePointMap (CommAlgCat.ofHom (numberFieldAdeleTensorMap K L))
    (AffineWeil.pointsEquiv K L H (Adeles K)
      ((AffineWeil.groupScheme K L G).affinePointsTarget (AffineWeil.map K L f)
        (CommAlgCat.of K (Adeles K)) x)) =
    G.affinePointsTarget f (CommAlgCat.of L (Adeles L))
      (G.affinePointMap (CommAlgCat.ofHom (numberFieldAdeleTensorMap K L))
        (AffineWeil.pointsEquiv K L G (Adeles K) x))
  rw [AffineWeil.map_affinePoints]
  exact DFunLike.congr_fun (G.affinePointsTarget_naturality f
    (CommAlgCat.ofHom (numberFieldAdeleTensorMap K L))) _

end Langlands.Global.AdelicWeilRestriction

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- The actual full adelic point isomorphism of two group schemes over the same number field. -/
def adelicPointsIso (e : G ≅ H) : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F H where
  toMulEquiv := ((yonedaGrp.mapIso e).app (Opposite.op
    ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))))).groupIsoToMulEquiv
  continuous_toFun := (map F G H e.hom).continuous
  continuous_invFun := (map F H G e.inv).continuous

@[simp]
theorem adelicPointsIso_apply (e : G ≅ H) (x : AdelicGroupPoints F G) :
    adelicPointsIso F e x = map F G H e.hom x := rfl

end Langlands.Global.AdelicGroupPoints
