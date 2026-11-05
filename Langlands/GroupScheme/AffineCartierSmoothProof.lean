import Langlands.GroupScheme.AffineCartierSmoothStatement
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.AnthropicFLT.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.Algebra.CharP.Algebra

/-! # Cartier smoothness for actual affine group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace AffineCartierSmoothProof

variable {k : Type u} [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Cartier reducedness of the actual affine group, via its coordinate Hopf algebra. -/
lemma isReduced : AlgebraicGeometry.IsReduced G.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Algebra.FiniteType k (AffineCoordinates.hopfAlgebra G) :=
    AffineCoordinates.algebraFiniteType G
  have : _root_.IsReduced (AffineCoordinates.hopfAlgebra G) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero k _
  let e : Spec (CommRingCat.of (AffineCoordinates.hopfAlgebra G)) ≅ G.X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso (AffineCoordinates.hopfSpecIso G))
  exact isReduced_of_isOpenImmersion e.inv

/-- Reapply Cartier reducedness to every field-valued base change. -/
lemma geometricallyReduced : GeometricallyReduced G.X.hom := by
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  let φ : k →+* K := (Spec.preimage y).hom
  have : CharZero K := charZero_of_injective_ringHom φ.injective
  let H := (GroupScheme.baseChange y).obj G
  have : IsAffineHom H.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom y)
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom y)
    infer_instance
  exact isReduced H

end AffineCartierSmoothProof

/-- Every affine group scheme locally of finite type over a characteristic-zero
field is smooth. -/
theorem affineCartierSmooth : AffineCartierSmoothStatement.{u} := by
  intro k _ _ G hA hft
  let := hA
  let := hft
  have : GeometricallyReduced G.X.hom := AffineCartierSmoothProof.geometricallyReduced G
  let : GrpObj (Over.mk G.X.hom) := inferInstanceAs (GrpObj G.X)
  exact smooth_of_grpObj G.X.hom

end Langlands.GroupScheme
