import Langlands.GroupScheme.AffineCorepresented
import Langlands.Algebra.GroupLikeReconstruction

/-! # Hopf coordinates and group-like reconstruction for affine group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- The commutative coordinate Hopf algebra of an actual affine group scheme. -/
abbrev hopfAlgebra : CommHopfAlgCat.{u} R :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj (op (coordinateCogroup G))

/-- The Hopf algebra construction retains the chosen affine coordinate algebra. -/
theorem hopfAlgebra_coe : (hopfAlgebra G : Type u) = algebra G :=
  rfl

/-- Relative spectrum of the coordinate Hopf algebra recovers the actual group
scheme with its multiplication, identity and inverse. -/
def hopfSpecIso : (hopfSpec R).obj (op (hopfAlgebra G)) ≅ G :=
  (algSpec R).mapGrp.mapIso
    (((commHopfAlgCatEquivCogrpCommAlgCat R).counitIso.app
      (op (coordinateCogroup G))).unop.symm) ≪≫
    coordinateCogroupIso G

/-- An equivalence of the coordinate Hopf algebra with a supplied commutative Hopf
algebra gives an actual group-scheme isomorphism from its relative spectrum. -/
def isoOfBialgEquiv (B : CommHopfAlgCat.{u} R) (e : hopfAlgebra G ≃ₐc[R] B) :
    (hopfSpec R).obj (op B) ≅ G :=
  (hopfSpec R).mapIso
    (((CommHopfAlgCat.ofIsoSelf (hopfAlgebra G)).symm ≪≫
      CommHopfAlgCat.isoMk e ≪≫ CommHopfAlgCat.ofIsoSelf B).op) ≪≫
    hopfSpecIso G

/-- The coordinate character group, written multiplicatively as group-like
elements of the Hopf algebra. -/
abbrev groupLikeGroup : Type u :=
  GroupLike R (hopfAlgebra G)

/-- The group algebra of the coordinate group-like elements, with its standard
commutative Hopf-algebra structure. -/
abbrev groupLikeHopfAlgebra : CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.of R (_root_.MonoidAlgebra R (groupLikeGroup G))

section Domain

variable [IsDomain R] [Module.IsTorsionFree R (hopfAlgebra G)]

/-- An affine group scheme whose coordinate algebra is spanned by group-like
elements is the relative spectrum of their group algebra. -/
def groupLikeSpecIso
    (h : Submodule.span R {a : hopfAlgebra G | IsGroupLikeElem R a} = ⊤) :
    (hopfSpec R).obj (op (groupLikeHopfAlgebra G)) ≅ G :=
  isoOfBialgEquiv G (groupLikeHopfAlgebra G)
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike h).symm

end Domain

end Langlands.GroupScheme.AffineCoordinates
