import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionStatement
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Transporting the geometric Borel witness of a parabolic subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]

/-- Pull back the factorization through a parabolic and identify the resulting
target with the geometric base change over the new field. -/
def baseChangeBorelFactor
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (c : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      Spec (CommRingCat.of (AlgebraicClosure k)))
    (e : GroupScheme.baseChange (toAlgebraicClosure k) ⋙ GroupScheme.baseChange c ≅
      GroupScheme.baseChange b ⋙ GroupScheme.baseChange (toAlgebraicClosure K))
    {P : GroupScheme (Spec (CommRingCat.of k))}
    {B : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (f : B ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj P) :
    (GroupScheme.baseChange c).obj B ⟶
      (GroupScheme.baseChange (toAlgebraicClosure K)).obj
        ((GroupScheme.baseChange b).obj P) :=
  (GroupScheme.baseChange c).map f ≫ (e.app P).hom

/-- Naturality of the comparison preserves the actual subgroup factorization. -/
theorem baseChangeBorelFactor_comp
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (c : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      Spec (CommRingCat.of (AlgebraicClosure k)))
    (e : GroupScheme.baseChange (toAlgebraicClosure k) ⋙ GroupScheme.baseChange c ≅
      GroupScheme.baseChange b ⋙ GroupScheme.baseChange (toAlgebraicClosure K))
    {P G : GroupScheme (Spec (CommRingCat.of k))}
    {B : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (i : P ⟶ G)
    (j : B ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
    (f : B ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj P)
    (hf : f ≫ (GroupScheme.baseChange (toAlgebraicClosure k)).map i = j) :
    baseChangeBorelFactor b c e f ≫
        (GroupScheme.baseChange (toAlgebraicClosure K)).map
          ((GroupScheme.baseChange b).map i) =
      (GroupScheme.baseChange c).map j ≫ (e.app G).hom := by
  change ((GroupScheme.baseChange c).map f ≫ e.hom.app P) ≫
      (GroupScheme.baseChange b ⋙ GroupScheme.baseChange (toAlgebraicClosure K)).map i =
    (GroupScheme.baseChange c).map j ≫ e.hom.app G
  rw [Category.assoc, ← e.hom.naturality i, ← Category.assoc,
    Functor.comp_map, ← Functor.map_comp, hf]

/-- A natural comparison and preservation of the geometric Borel witness suffice
to extend the actual parabolic inclusion. The Borel-preservation premise is
explicit and is not proved here. -/
theorem IsParabolicSubgroup.baseChange_of_geometricBorel
    {P G : GroupScheme (Spec (CommRingCat.of k))} {i : P ⟶ G}
    (hi : IsParabolicSubgroup i)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (c : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      Spec (CommRingCat.of (AlgebraicClosure k)))
    (e : GroupScheme.baseChange (toAlgebraicClosure k) ⋙ GroupScheme.baseChange c ≅
      GroupScheme.baseChange b ⋙ GroupScheme.baseChange (toAlgebraicClosure K))
    (hBorel : ∀
      (B : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
      (j : B ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G),
      IsBorelSubgroup j → IsBorelSubgroup ((GroupScheme.baseChange c).map j)) :
    IsParabolicSubgroup ((GroupScheme.baseChange b).map i) := by
  refine ⟨hi.isClosedSubgroup.baseChange b, ?_, ?_⟩
  · have : Smooth P.X.hom := hi.smooth
    change Smooth (pullback.snd P.X.hom b)
    infer_instance
  · obtain ⟨B, j, f, hj, hf⟩ := hi.exists_isBorelSubgroup
    refine ⟨(GroupScheme.baseChange c).obj B,
      (GroupScheme.baseChange c).map j ≫ (e.app G).hom,
      baseChangeBorelFactor b c e f,
      (hBorel B j hj).comp_iso (e.app G), ?_⟩
    exact baseChangeBorelFactor_comp b c e i j f hf

end Langlands.GroupScheme
