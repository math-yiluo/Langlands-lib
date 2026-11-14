import Langlands.GroupScheme.RelativeLevi.ModuliValue
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties

/-! # Comparing the actual geometric fibres after arbitrary base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeLevi

variable {S T : Scheme.{u}} (b : T ⟶ S) (t : T)

/-- The residue-field map of a base morphism, expressed as an algebra. -/
def residueFieldAlgebra :
    Algebra (S.residueField (b t)) (T.residueField t) :=
  (b.residueFieldMap t).hom.toAlgebra

/-- A compatible map between the chosen algebraic closures of the residue fields. -/
def geometricPointMap :
    Spec (CommRingCat.of (AlgebraicClosure (T.residueField t))) ⟶
      Spec (CommRingCat.of (AlgebraicClosure (S.residueField (b t)))) :=
  letI := residueFieldAlgebra b t
  algebraicClosureBaseMap (S.residueField (b t)) (T.residueField t)

/-- The chosen geometric points form a commutative square over the base map. -/
theorem geometricPointMap_comp :
    geometricPointMap b t ≫ geometricPoint S (b t) =
      geometricPoint T t ≫ b := by
  letI := residueFieldAlgebra b t
  unfold geometricPointMap geometricPoint
  rw [← Category.assoc, algebraicClosureBaseMap_comp, Category.assoc]
  change toAlgebraicClosure (T.residueField t) ≫
      Spec.map (b.residueFieldMap t) ≫ S.fromSpecResidueField (b t) =
    (toAlgebraicClosure (T.residueField t) ≫ T.fromSpecResidueField t) ≫ b
  rw [b.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]

/-- The geometric fibre after changing the base is the original geometric
fibre pulled back along the compatible extension of algebraic closures. -/
def geometricFiberBaseChangeIso :
    baseChange (geometricPoint S (b t)) ⋙ baseChange (geometricPointMap b t) ≅
      baseChange b ⋙ baseChange (geometricPoint T t) :=
  (Functor.mapGrpNatIso
      (Over.pullbackComp (geometricPointMap b t) (geometricPoint S (b t))) ≪≫
    Functor.mapGrpCompIso).symm ≪≫
  eqToIso (congrArg (fun f => baseChange f) (geometricPointMap_comp b t)) ≪≫
  Functor.mapGrpNatIso (Over.pullbackComp (geometricPoint T t) b) ≪≫
    Functor.mapGrpCompIso

/-- The comparison identifies the actual geometric-fibre homomorphisms. -/
theorem geometricFiberHom_baseChange_eq {U P : GroupScheme S} (r : U ⟶ P) :
    geometricFiberHom ((baseChange b).map r) t =
      ((geometricFiberBaseChangeIso b t).app U).inv ≫
        (baseChange (geometricPointMap b t)).map (geometricFiberHom r (b t)) ≫
          ((geometricFiberBaseChangeIso b t).app P).hom := by
  have h := (geometricFiberBaseChangeIso b t).hom.naturality r
  rw [Iso.eq_inv_comp]
  exact h.symm

/-- A radical assertion on the extended original geometric fibre transports
to the geometric fibre of the base-changed homomorphism. -/
theorem geometricFiber_radical_of_extension {U P : GroupScheme S} (r : U ⟶ P)
    (h : IsUnipotentRadical
      ((baseChange (geometricPointMap b t)).map (geometricFiberHom r (b t)))) :
    IsUnipotentRadical (geometricFiberHom ((baseChange b).map r) t) := by
  rw [geometricFiberHom_baseChange_eq]
  exact (h.comp_iso ((geometricFiberBaseChangeIso b t).app P)).precomp_iso
    ((geometricFiberBaseChangeIso b t).app U).symm

end Langlands.GroupScheme.RelativeLevi
