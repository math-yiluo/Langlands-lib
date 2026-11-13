import Langlands.GroupScheme.Dynamic.BaseUnipotentFibresStatement
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Unipotent fibres of dynamic subgroups over any base scheme: proof -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- Pull back the representative to each field-valued point and apply the field
unipotence theorem, using the actual arbitrary-base-change comparison of dynamic
unipotent subgroup functors. -/
theorem dynamicBaseUnipotentFibres : DynamicBaseUnipotentFibresStatement.{u} := by
  intro S G _ _ χ H j hj K _ y
  let : IsAffineHom ((GroupScheme.baseChange y).obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom y ‹_›
  let : LocallyOfFiniteType ((GroupScheme.baseChange y).obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) G.X.hom y ‹_›
  have hjK := hj.baseChange y
  rw [← Dynamic.unipotent_baseChange] at hjK
  exact dynamicUnipotentUnipotence K _ (Dynamic.baseChangeCocharacter y χ) _ _ hjK

end Langlands.GroupScheme
