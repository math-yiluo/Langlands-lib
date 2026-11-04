import Langlands.GroupScheme.Torus.CocharacterFiniteGaloisDescent
import Mathlib.FieldTheory.IsSepClosed

/-! # Geometric vanishing of cocharacters of commutative groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Absence of base-field torus maps kills geometric cocharacters of an affine
commutative group locally of finite type, without a smoothness assumption. -/
def CommutativeGeometricCocharacterVanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffine Z.toGrp.X.left] [LocallyOfFiniteType Z.toGrp.X.hom],
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range f = ⊥) →
    ∀ nu : (Gm (Spec (CommRingCat.of (AlgebraicClosure k)))).toGrp ⟶
      ((CommGroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj Z).toGrp,
      nu = 0

namespace CocharacterDatum

variable {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffine Z.toGrp.X.left] [LocallyOfFiniteType Z.toGrp.X.hom]
    (hZ : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range f = ⊥)

include hZ

/-- A geometric multiplicative universal point is the identity if all
base-field torus maps vanish. -/
theorem multiplicativePoint_eq_one_over_algebraicClosure
    (x : multiplicativePoints Z (AlgebraicClosure k) (PUnit.{u+1} → ℤ)) : x = 1 := by
  let F := SeparableClosure k
  obtain ⟨y, hy, hyx⟩ :=
    x.property.exists_coeffMap_eq_of_isPurelyInseparable (F := F)
  have hyone : (⟨y, hy⟩ : multiplicativePoints Z F (PUnit.{u+1} → ℤ)) = 1 :=
    multiplicativePoint_eq_one_of_isGalois hZ F _
  apply Subtype.ext
  rw [← hyx, show y = 1 from congrArg Subtype.val hyone, map_one]
  rfl

/-- Every actual geometric cocharacter of an affine finite type commutative
group vanishes when all maps from base-field tori vanish. -/
theorem gm_hom_eq_zero_over_algebraicClosure
    (nu : (Gm (Spec (CommRingCat.of (AlgebraicClosure k)))).toGrp ⟶
      ((CommGroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj Z).toGrp) :
    nu = 0 := by
  apply (gmHomEquivMultiplicativePoints (Z := Z) (AlgebraicClosure k)).injective
  rw [gmHomEquivMultiplicativePoints_zero]
  exact multiplicativePoint_eq_one_over_algebraicClosure hZ _

end CocharacterDatum

/-- The geometric cocharacter vanishing implication in the original universe. -/
theorem commutativeGeometricCocharacterVanishing :
    CommutativeGeometricCocharacterVanishingStatement.{u} := by
  intro k _ Z _ _ hZ nu
  exact CocharacterDatum.gm_hom_eq_zero_over_algebraicClosure hZ nu

end Langlands.GroupScheme
