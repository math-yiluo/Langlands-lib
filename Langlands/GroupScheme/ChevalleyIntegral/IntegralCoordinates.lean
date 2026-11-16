import Langlands.GroupScheme.ChevalleyIntegral.FieldEmbedding
import Langlands.GroupScheme.ChevalleyIntegral.ModelComparison

/-! # Integral coordinate tori and the field-comparison adapter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence SplitExistence.ChevalleyData

section CoordinateComparison

variable (R : CommRingCat.{u}) (I : Type u) [Fintype I] [DecidableEq I]

/-- The full coordinate lattice identifies its diagonalizable group with the
coordinate split torus over any ring. -/
def coordinateTorusIsoOver :
    (Diagonalizable.groupScheme R (I → ℤ)).toGrp ≅ splitTorus (Spec R) I :=
  Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))

theorem coordinateTorusIsoOver_points (T : Over (Spec R))
    (x : T ⟶ (Diagonalizable.groupScheme R (I → ℤ)).X) :
    splitTorus.pointsEquiv I T (x ≫ (coordinateTorusIsoOver R I).hom.hom.hom) =
      Diagonalizable.splitPointsEquiv R (AddEquiv.refl (I → ℤ)) T x :=
  isoOfPointModels_hom _ _ _ _
    (Diagonalizable.splitPointsEquiv_naturality R (AddEquiv.refl (I → ℤ)))
    (fun a y => splitTorus.pointsEquiv_naturality I a y) T x

variable {R} {R' : CommRingCat.{u}} (a : Spec R' ⟶ Spec R)

/-- The full-lattice coordinate comparison commutes with arbitrary base change. -/
theorem coordinateTorusIsoOver_baseChange :
    (baseChange a).map (coordinateTorusIsoOver R I).hom ≫
        (splitTorus.baseChangeIso a I).hom =
      (Diagonalizable.baseChangeIso a (I → ℤ)).hom ≫
        (coordinateTorusIsoOver R' I).hom := by
  apply hom_ext_points
  intro T x
  apply (splitTorus.pointsEquiv I T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, splitTorus.pointsEquiv_baseChangeIso_hom]
  change splitTorus.pointsEquiv I ((Over.map a).obj T)
      (baseChangePointsEquiv a _ T
        (x ≫ ((baseChange a).map (coordinateTorusIsoOver R I).hom).hom.hom)) = _
  rw [baseChangePointsEquiv_comp, coordinateTorusIsoOver_points,
    Grp.comp_hom_hom, ← Category.assoc, coordinateTorusIsoOver_points]
  funext j
  exact (congrArg (fun χ => χ (.ofAdd (Pi.single j 1)))
    (Diagonalizable.characterPointsEquiv_baseChangeIso_hom a (I → ℤ) T x)).symm

/-- The inverse comparison commutes with the canonical source identifications. -/
theorem coordinateTorusIsoOver_inv_baseChange :
    (splitTorus.baseChangeIso a I).inv ≫
        (baseChange a).map (coordinateTorusIsoOver R I).inv =
      (coordinateTorusIsoOver R' I).inv ≫
        (Diagonalizable.baseChangeIso a (I → ℤ)).inv := by
  have h : (baseChange a).mapIso (coordinateTorusIsoOver R I) ≪≫
        splitTorus.baseChangeIso a I =
      Diagonalizable.baseChangeIso a (I → ℤ) ≪≫ coordinateTorusIsoOver R' I :=
    Iso.ext (coordinateTorusIsoOver_baseChange I a)
  exact congrArg Iso.inv h

end CoordinateComparison

section IntegralModel

variable {I J : Type u} [Fintype I] [DecidableEq I]
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  (D : ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)

/-- The full coordinate torus in the one fixed integral model. -/
def integralCoordinateTorus :
    splitTorus (Spec (CommRingCat.of R)) I ⟶ (genericModel D R K C).group :=
  (coordinateTorusIsoOver (CommRingCat.of R) I).inv ≫ torus D R K C

theorem integralCoordinateTorus_closed :
    IsClosedSubgroup (integralCoordinateTorus D R K C) :=
  (IsClosedSubgroup.of_iso (coordinateTorusIsoOver (CommRingCat.of R) I).symm).comp
    (torus_closed D R K C)

variable (k : Type u) [Field k] [Algebra R k]

/-- Base change of the single integral coordinate torus is its field expression. -/
theorem baseChange_integralCoordinateTorus :
    splitTorus.baseChangeHom (K := k) (genericModel D R K C).group I
        (integralCoordinateTorus D R K C) =
      CommGroupScheme.groupHom (coordinateTorusIso k I).inv ≫
        fieldTorus D R K C k (CommRingCat.ofHom (algebraMap R k)) := by
  dsimp only [splitTorus.baseChangeHom, integralCoordinateTorus]
  rw [Functor.map_comp, ← Category.assoc, coordinateTorusIsoOver_inv_baseChange]
  rw [Category.assoc]
  rfl

variable (H : D.ChevGroup k)

/-- The closed field embedding preserves the coordinate torus. -/
theorem coordinateTorusHom_fieldEmbedding :
    coordinateTorusHom H ≫
        fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H =
      splitTorus.baseChangeHom (K := k) (genericModel D R K C).group I
        (integralCoordinateTorus D R K C) := by
  rw [baseChange_integralCoordinateTorus, coordinateTorusHom, Category.assoc,
    torus_fieldEmbedding]

end IntegralModel

/-- If the closed field embeddings are isomorphisms, the one integral model has
the compatible field comparisons required by the integral-existence reduction. -/
theorem hasFieldComparisons_of_fieldEmbedding_isIso
    {I J : Type u} [Fintype I] [DecidableEq I] [Finite J]
    {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
    (D : ChevalleyData P b)
    (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)
    (h : ∀ (k : Type u) [Field k] [Algebra R k],
      ∃ H : D.ChevGroup k,
        IsIso (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H)) :
    HasFieldComparisons D (genericModel D R K C).group
      (integralCoordinateTorus D R K C) := by
  intro k _ _
  obtain ⟨H, hH⟩ := h k
  let := hH
  let e := asIso (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H)
  refine ⟨H, e.symm, ?_⟩
  rw [← coordinateTorusHom_fieldEmbedding D R K C k H]
  change (coordinateTorusHom H ≫ e.hom) ≫ e.inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme.ChevalleyIntegral
