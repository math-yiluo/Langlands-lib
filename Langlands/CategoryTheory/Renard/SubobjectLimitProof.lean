import Langlands.CategoryTheory.Renard.SubobjectLimitStatements

/-!
# Renard A.IV: subobject intersections and unions as limits and colimits

The category on `Subobject X` is the thin category of its factorization
order, so Mathlib's preorder (co)limit comparisons apply to the discrete
family. The only reconciliation is between the range of the discrete
functor's object map and the range of the family itself.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.SubobjectLimit

universe vC uC uI

/-- The objects of a discrete diagram are exactly the members of its family. -/
private theorem range_discrete_functor_obj {P : Type*} [Category P] {I : Type*}
    (F : I → P) :
    Set.range (Discrete.functor F).obj = Set.range F := by
  ext x
  constructor
  · rintro ⟨⟨i⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i⟩, rfl⟩

/-- A supplied cone is limiting exactly when its vertex is the intersection. -/
theorem intersectionLimitStatement : IntersectionLimitStatement.{vC, uC, uI} := by
  intro C _ X I F t
  rw [← range_discrete_functor_obj F]
  exact ⟨fun ⟨ht⟩ => Preorder.isGLB_of_isLimit _ ht,
    fun h => ⟨Preorder.isLimitOfIsGLB _ t h⟩⟩

/-- A supplied cocone is colimiting exactly when its vertex is the union. -/
theorem unionColimitStatement : UnionColimitStatement.{vC, uC, uI} := by
  intro C _ X I F t
  rw [← range_discrete_functor_obj F]
  exact ⟨fun ⟨ht⟩ => Preorder.isLUB_of_isColimit _ ht,
    fun h => ⟨Preorder.isColimitOfIsLUB _ t h⟩⟩

/-- The unchanged intersection-then-union aggregate at three independent
universes. -/
theorem subobjectLimitStatements : SubobjectLimitStatements.{vC, uC, uI} :=
  ⟨intersectionLimitStatement.{vC, uC, uI}, unionColimitStatement.{vC, uC, uI}⟩

end Langlands.Renard.SubobjectLimit
