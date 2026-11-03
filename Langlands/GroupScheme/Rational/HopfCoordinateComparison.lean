import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.Rational.CharacterUnits

/-! # Comparison of Hopf coordinates with the actual Lie coordinate algebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

local instance instHopfCoordinateComparison1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The two affine coordinate choices are compared through their presentations
of the same actual group scheme. -/
def lieCoordinateAlgEquiv : hopfAlgebra G ≃ₐ[R] Lie.coordinateAlgebra G :=
  CommAlgCat.algEquivOfIso
    (algSpec.fullyFaithful.preimageIso
      (Lie.coordinateIso G ≪≫ (coordinateSchemeIso G).symm)).unop

theorem pointEquiv_lieCoordinateAlgEquiv :
    pointEquiv G (Lie.coordinateAlgebra G)
        (CommAlgCat.ofHom (lieCoordinateAlgEquiv G).toAlgHom) =
      (Lie.coordinateIso G).hom := by
  change (algSpec R).map
      (algSpec.fullyFaithful.preimage
        ((Lie.coordinateIso G).hom ≫ (coordinateSchemeIso G).inv)) ≫
      (coordinateSchemeIso G).hom = _
  rw [algSpec.fullyFaithful.map_preimage]
  simp

theorem pointEquiv_comp_lieCoordinateAlgEquiv {C : CommAlgCat.{u} R}
    (f : Lie.coordinateAlgebra G →ₐ[R] C) :
    pointEquiv G C (CommAlgCat.ofHom (f.comp (lieCoordinateAlgEquiv G).toAlgHom)) =
      (Lie.pointCoordinates G).symm f := by
  change pointEquiv G C
      (CommAlgCat.ofHom (lieCoordinateAlgEquiv G).toAlgHom ≫ CommAlgCat.ofHom f) = _
  rw [pointEquiv_comp]
  change (algSpec R).map (CommAlgCat.ofHom f).op ≫
      pointEquiv G (Lie.coordinateAlgebra G)
        (CommAlgCat.ofHom (lieCoordinateAlgEquiv G).toAlgHom) = _
  rw [pointEquiv_lieCoordinateAlgEquiv]
  rfl

theorem pointEquiv_hopf_counit :
    pointEquiv G (CommAlgCat.of R R)
      (CommAlgCat.ofHom (Bialgebra.counitAlgHom R (hopfAlgebra G))) = 1 := by
  let _ : GrpObj (coordinateCogroup G).X := (coordinateCogroup G).grp
  change (algSpec R).map
      (1 : op (CommAlgCat.of R R) ⟶ (coordinateCogroup G).X) ≫
      (coordinateCogroupIso G).hom.hom.hom = _
  rw [Functor.map_one, MonObj.one_comp]

theorem pointEquiv_hopf_mul {C : CommAlgCat.{u} R}
    (f g : hopfAlgebra G →ₐ[R] C) :
    pointEquiv G C (CommAlgCat.ofHom
      ((Algebra.TensorProduct.productMap f g).comp
        (Bialgebra.comulAlgHom R (hopfAlgebra G)))) =
      pointEquiv G C (CommAlgCat.ofHom f) *
        pointEquiv G C (CommAlgCat.ofHom g) := by
  let _ : GrpObj (coordinateCogroup G).X := (coordinateCogroup G).grp
  change (algSpec R).map
      ((CommAlgCat.ofHom f).op * (CommAlgCat.ofHom g).op) ≫
      (coordinateCogroupIso G).hom.hom.hom = _
  rw [Functor.map_mul, MonObj.mul_comp]
  rfl

/-- The affine coordinate comparison preserves evaluation at the identity. -/
theorem coordinateOrigin_comp_lieCoordinateAlgEquiv :
    (Lie.coordinateOrigin G).comp (lieCoordinateAlgEquiv G).toAlgHom =
      Bialgebra.counitAlgHom R (hopfAlgebra G) := by
  have h : CommAlgCat.ofHom
      ((Lie.coordinateOrigin G).comp (lieCoordinateAlgEquiv G).toAlgHom) =
      CommAlgCat.ofHom (Bialgebra.counitAlgHom R (hopfAlgebra G)) := by
    apply (pointEquiv G (CommAlgCat.of R R)).injective
    rw [pointEquiv_comp_lieCoordinateAlgEquiv, pointEquiv_hopf_counit]
    exact (Lie.pointCoordinates G).symm_apply_apply 1
  exact congrArg CommAlgCat.Hom.hom h

/-- Pointwise counit compatibility for the actual coordinate comparison. -/
theorem lieCoordinateAlgEquiv_counit (a : hopfAlgebra G) :
    Lie.coordinateOrigin G (lieCoordinateAlgEquiv G a) =
      Bialgebra.counitAlgHom R (hopfAlgebra G) a :=
  DFunLike.congr_fun (coordinateOrigin_comp_lieCoordinateAlgEquiv G) a

section Field

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]

/-- The comparison carries the Hopf comultiplication to the actual coordinate
comultiplication, defined using the product of the two universal points. -/
theorem comul_comp_lieCoordinateAlgEquiv :
    (Algebra.TensorProduct.map (lieCoordinateAlgEquiv H).toAlgHom
        (lieCoordinateAlgEquiv H).toAlgHom).comp
      (Bialgebra.comulAlgHom (CommRingCat.of k) (hopfAlgebra H)) =
        (CharacterUnits.comul H).comp (lieCoordinateAlgEquiv H).toAlgHom := by
  have ht : Algebra.TensorProduct.map (lieCoordinateAlgEquiv H).toAlgHom
      (lieCoordinateAlgEquiv H).toAlgHom =
      Algebra.TensorProduct.productMap
        ((CharacterUnits.inclLeft H).comp (lieCoordinateAlgEquiv H).toAlgHom)
        ((CharacterUnits.inclRight H).comp (lieCoordinateAlgEquiv H).toAlgHom) := by
    ext <;> simp
  have h : CommAlgCat.ofHom
      ((Algebra.TensorProduct.map (lieCoordinateAlgEquiv H).toAlgHom
        (lieCoordinateAlgEquiv H).toAlgHom).comp
          (Bialgebra.comulAlgHom (CommRingCat.of k) (hopfAlgebra H))) =
      CommAlgCat.ofHom
        ((CharacterUnits.comul H).comp (lieCoordinateAlgEquiv H).toAlgHom) := by
    apply (pointEquiv H (CommAlgCat.of (CommRingCat.of k)
      (CharacterUnits.Coord H ⊗[CommRingCat.of k] CharacterUnits.Coord H))).injective
    rw [ht, pointEquiv_hopf_mul]
    erw [pointEquiv_comp_lieCoordinateAlgEquiv H
        (C := CommAlgCat.of (CommRingCat.of k)
          (CharacterUnits.Coord H ⊗[CommRingCat.of k] CharacterUnits.Coord H))
        (CharacterUnits.inclLeft H),
      pointEquiv_comp_lieCoordinateAlgEquiv H
        (C := CommAlgCat.of (CommRingCat.of k)
          (CharacterUnits.Coord H ⊗[CommRingCat.of k] CharacterUnits.Coord H))
        (CharacterUnits.inclRight H),
      pointEquiv_comp_lieCoordinateAlgEquiv H
        (C := CommAlgCat.of (CommRingCat.of k)
          (CharacterUnits.Coord H ⊗[CommRingCat.of k] CharacterUnits.Coord H))
        (CharacterUnits.comul H)]
    simp only [CharacterUnits.comul, Equiv.symm_apply_apply]
    rw [CharacterUnits.affinePointMap_universalPoint_eq H (CharacterUnits.inclLeft H),
      CharacterUnits.affinePointMap_universalPoint_eq H (CharacterUnits.inclRight H)]
  exact congrArg CommAlgCat.Hom.hom h

/-- Pointwise comultiplication compatibility, with the field as scalar type. -/
theorem lieCoordinateAlgEquiv_comul (a : hopfAlgebra H) :
    (Algebra.TensorProduct.map
      (lieCoordinateAlgEquiv H).toAlgHom (lieCoordinateAlgEquiv H).toAlgHom)
      (Bialgebra.comulAlgHom k (hopfAlgebra H) a) =
        CharacterUnits.comul H (lieCoordinateAlgEquiv H a) :=
  DFunLike.congr_fun (comul_comp_lieCoordinateAlgEquiv H) a

end Field

end Langlands.GroupScheme.AffineCoordinates
