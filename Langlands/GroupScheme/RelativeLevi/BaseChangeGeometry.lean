import Langlands.GroupScheme.RelativeLevi.GeometricFiberComparison
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange

/-! # Geometric ingredients for relative Levi base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S T : Scheme.{u}} {L U P : GroupScheme S}

/-- The given base morphism preserves every actual relative radical in `P`.
This is a condition on base change, not an assertion that the condition holds. -/
def RelativeLevi.PreservesUnipotentRadicals (b : T ⟶ S) (P : GroupScheme S) : Prop :=
  ∀ (V : GroupScheme S) (r : V ⟶ P), IsRelativeUnipotentRadical r →
    IsRelativeUnipotentRadical ((baseChange b).map r)

/-- The actual subgroup multiplication remains an isomorphism after any base change. -/
theorem isIso_subgroupMultiplication_baseChange (b : T ⟶ S)
    (l : L ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)] :
    IsIso (subgroupMultiplication ((baseChange b).map l) ((baseChange b).map r)) := by
  have he : subgroupMultiplication ((baseChange b).map l) ((baseChange b).map r) =
      (subgroupMultiplicationBaseChangeIso b L U).inv ≫
        (Over.pullback b).map (subgroupMultiplication l r) := by
    rw [← subgroupMultiplication_baseChange b l r, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- An actual relative Levi presentation forces its ambient group to be smooth. -/
theorem IsRelativeLeviSubgroup.smooth_ambient {l : L ⟶ P}
    (hl : IsRelativeLeviSubgroup l) : Smooth P.X.hom := by
  obtain ⟨U, r, hr, hm⟩ := hl.exists_unipotentRadical
  letI : IsIso (subgroupMultiplication l r) := hm
  exact smooth_of_over_iso (asIso (subgroupMultiplication l r)).symm
    (smooth_tensor L.X U.X hl.smooth hr.smooth)

/-- The geometric radical assertions after the compatible closure extensions
suffice for relative-radical preservation. The extension assertions are premises. -/
theorem IsRelativeUnipotentRadical.baseChange_of_geometric_extension
    {r : U ⟶ P} (hr : IsRelativeUnipotentRadical r) (b : T ⟶ S)
    (hext : ∀ t : T, IsUnipotentRadical
      ((baseChange (RelativeLevi.geometricPointMap b t)).map
        (RelativeLevi.geometricFiberHom r (b t)))) :
    IsRelativeUnipotentRadical ((baseChange b).map r) where
  isClosedSubgroup := hr.isClosedSubgroup.baseChange b
  smooth := by
    letI : Smooth U.X.hom := hr.smooth
    change Smooth (CategoryTheory.Limits.pullback.snd U.X.hom b)
    infer_instance
  isNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hr.isNormal.baseChange b
  geometricFiber t := RelativeLevi.geometricFiber_radical_of_extension b t r (hext t)

/-- Preserving the supplied radicals suffices to preserve any actual relative
Levi inclusion; the multiplication isomorphism is preserved without conditions. -/
theorem IsRelativeLeviSubgroup.baseChange_of_radical_preservation
    {l : L ⟶ P} (hl : IsRelativeLeviSubgroup l) (b : T ⟶ S)
    (hrad : RelativeLevi.PreservesUnipotentRadicals b P) :
    IsRelativeLeviSubgroup ((baseChange b).map l) where
  isClosedSubgroup := hl.isClosedSubgroup.baseChange b
  smooth := by
    letI : Smooth L.X.hom := hl.smooth
    change Smooth (CategoryTheory.Limits.pullback.snd L.X.hom b)
    infer_instance
  exists_unipotentRadical := by
    obtain ⟨V, r, hr, hm⟩ := hl.exists_unipotentRadical
    letI : IsIso (subgroupMultiplication l r) := hm
    exact ⟨(baseChange b).obj V, (baseChange b).map r, hrad V r hr,
      isIso_subgroupMultiplication_baseChange b l r⟩

end Langlands.GroupScheme
