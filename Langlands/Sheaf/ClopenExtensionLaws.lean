import Langlands.Sheaf.ClopenExtension

/-!
# Naturality and nested images of clopen zero extension

These laws use the actual finite-gluing zero extension for all-open sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.ClopenExtension

open CategoryTheory TopologicalSpace Opposite

universe u v

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{v} X)

/-- Restricting through an intermediate open agrees with direct restriction. -/
theorem restrict_comp {U V : Opens X} (hUV : U ≤ V) :
    restrict F V ≫ F.presheaf.map (homOfLE hUV : U ⟶ V).op = restrict F U := by
  rw [← F.presheaf.map_comp]
  rfl

/-- Extension vanishes on every open contained in the complementary open. -/
theorem extend_restrict_of_le_complement
    (U : Opens X) (hU : IsClosed (U : Set X))
    (W : Opens X) (hW : W ≤ complement U hU) :
    extend F U hU ≫ restrict F W = 0 := by
  rw [← restrict_comp F hW, ← Category.assoc, extend_restrict_complement]
  simp

/-- Actual sheaf morphisms commute with zero extension. -/
theorem extend_naturality {G : TopCat.Sheaf AddCommGrpCat.{v} X}
    (α : F ⟶ G) (U : Opens X) (hU : IsClosed (U : Set X)) :
    extend F U hU ≫ α.hom.app (op ⊤) =
      α.hom.app (op U) ≫ extend G U hU := by
  apply extend_unique G U hU
  · rw [Category.assoc, ← α.hom.naturality, ← Category.assoc]
    simp
  · rw [Category.assoc, ← α.hom.naturality, ← Category.assoc]
    simp

/-- Open complements reverse the inclusion of closed opens. -/
theorem complement_le_complement {U V : Opens X}
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) (hUV : U ≤ V) :
    complement V hV ≤ complement U hU := by
  intro x hx hxU
  exact hx (hUV hxU)

/-- Extending from the smaller clopen and then from the larger one changes nothing. -/
theorem extend_nested {U V : Opens X}
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) (hUV : U ≤ V) :
    extend F U hU ≫ restrict F V ≫ extend F V hV = extend F U hU := by
  rw [← Category.assoc]
  symm
  apply extend_unique F V hV
  · rfl
  · exact extend_restrict_of_le_complement F U hU (complement V hV)
      (complement_le_complement hU hV hUV)

/-- The actual additive subgroup of global sections extended from a clopen open. -/
def image (U : Opens X) (hU : IsClosed (U : Set X)) :
    AddSubgroup (F.presheaf.obj (op ⊤)) :=
  (extend F U hU).hom.range

/-- Nested clopen opens give nested actual additive subgroup ranges. -/
theorem image_mono {U V : Opens X}
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) (hUV : U ≤ V) :
    image F U hU ≤ image F V hV := by
  rintro s ⟨t, rfl⟩
  refine ⟨restrict F V (extend F U hU t), ?_⟩
  exact congrArg (fun f => f t) (extend_nested F hU hV hUV)

end Langlands.Sheaf.ClopenExtension
