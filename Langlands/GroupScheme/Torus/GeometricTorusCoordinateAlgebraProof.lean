import Langlands.GroupScheme.Torus.GeometricTorusCoordinateAlgebraStatement
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # The coordinate algebra of a torus over the algebraic closure -/

noncomputable section

open AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateAlgebra_of_isSplitTorus {k : Type u} [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.toGrp.X.hom]
    (hT : IsSplitTorus T.toGrp) :
    ∃ e : AddMonoidAlgebra k (characterLattice T) ≃ₐ[k] Lie.coordinateAlgebra T.toGrp,
      ∀ χ : characterLattice T,
        e (AddMonoidAlgebra.single χ 1) =
          (SplitCharacterPoint.value χ (Lie.universalPoint T.toGrp)).val := by
  let A := AddMonoidAlgebra k (characterLattice T)
  let B := Lie.coordinateAlgebra T.toGrp
  let x := Lie.universalPoint T.toGrp
  let y := SplitCharacterPoint.universalPoint hT
  let f : A →ₐ[k] B := SplitCharacterPoint.pointLift x
  let g : B →ₐ[k] A := Lie.pointCoordinates T.toGrp y
  have hfg : f.comp g = AlgHom.id k B := by
    calc
      _ = Lie.pointCoordinates T.toGrp (Lie.affineMap T.toGrp f y) :=
        (Lie.pointCoordinates_naturality T.toGrp f y).symm
      _ = _ := by
        change Lie.pointCoordinates T.toGrp
          (Lie.affineMap T.toGrp (SplitCharacterPoint.pointLift x)
            (SplitCharacterPoint.universalPoint hT)) = _
        rw [SplitCharacterPoint.affineMap_pointLift, Lie.pointCoordinates_universalPoint]
  have hy : Lie.affineMap T.toGrp g x = y := by
    calc
      _ = (Lie.pointCoordinates T.toGrp).symm g := Lie.affineMap_universalPoint T.toGrp g
      _ = _ := (Lie.pointCoordinates T.toGrp).symm_apply_apply y
  have hgf : g.comp f = AlgHom.id k A := by
    refine AddMonoidAlgebra.algHom_ext (fun χ => ?_) (Subsingleton.elim _ _)
    change g (SplitCharacterPoint.pointLift x (AddMonoidAlgebra.single χ 1)) =
      AddMonoidAlgebra.single χ 1
    rw [SplitCharacterPoint.pointLift_single, map_one, one_mul,
      ← SplitCharacterPoint.value_affineMap g, hy, SplitCharacterPoint.value_universalPoint,
      SplitCharacterPoint.monomialUnit_val]
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, fun χ => ?_⟩
  change SplitCharacterPoint.pointLift x (AddMonoidAlgebra.single χ 1) = _
  rw [SplitCharacterPoint.pointLift_single, map_one, one_mul]

/-- The geometric fibre is split, and its character evaluations give the coordinate isomorphism. -/
theorem geometricTorusCoordinateAlgebra : GeometricTorusCoordinateAlgebraStatement.{u} := by
  intro F _ T hT K S
  have hS : IsTorus S.toGrp := hT.baseChange (K := K)
  have hsplit : IsSplitTorus S.toGrp := hS.isSplitTorus_of_finiteGaloisSplitting
    torusFiniteGaloisSplitting
  let : IsAffineHom S.toGrp.X.hom := hsplit.isAffineHom
  exact ⟨inferInstance, coordinateAlgebra_of_isSplitTorus S hsplit⟩

end Langlands.GroupScheme
