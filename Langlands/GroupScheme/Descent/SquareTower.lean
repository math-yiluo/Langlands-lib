import Langlands.GroupScheme.Descent.SquareSemilinear

/-! # Tower coherence of commuting-square comparisons -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (b : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Two successive commuting-square comparisons and the integral tower
comparison equal the generic tower comparison and the composite square. -/
theorem squareComparison_tower
    {S T : Scheme.{u}} (c : T ⟶ S)
    (a b d : S ⟶ S) (hab : a ≫ b = d)
    (v w z : T ⟶ T) (hvw : v ≫ w = z)
    (hvc : v ≫ c = c ≫ a) (hwc : w ≫ c = c ≫ b)
    (hzc : z ≫ c = c ≫ d) (G : GroupScheme S) :
    (baseChange v).map (squareComparison c w b c hwc G).hom ≫
        (squareComparison c v a c hvc ((baseChange b).obj G)).hom ≫
          (baseChange c).map (pullbackComparison b a d hab G).hom =
      (pullbackComparison w v z hvw ((baseChange c).obj G)).hom ≫
        (squareComparison c z d c hzc G).hom := by
  apply hom_ext_pullback_tower d c G
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  conv_lhs =>
    erw [map_fst_assoc c (pullbackComparison b a d hab G).hom,
      pullbackComparison_hom_fst b a d hab G]
    erw [squareComparison_hom_fst_fst_assoc c v a c hvc ((baseChange b).obj G)
      (pullback.fst G.X.hom b)]
    erw [map_fst_assoc v (squareComparison c w b c hwc G).hom]
    rw [squareComparison_hom_fst_fst c w b c hwc G]
  conv_rhs =>
    erw [squareComparison_hom_fst_fst c z d c hzc G]
    erw [pullbackComparison_hom_fst_assoc w v z hvw ((baseChange c).obj G)]

/-- The actual comparison obtained by traversing two commuting squares and
then collapsing the integral pullback tower. -/
def squareTowerComparison {S T : Scheme.{u}} (c : T ⟶ S)
    (a b d : S ⟶ S) (hab : a ≫ b = d)
    (v w : T ⟶ T) (hvc : v ≫ c = c ≫ a) (hwc : w ≫ c = c ≫ b)
    (G : GroupScheme S) :
    (baseChange v).obj ((baseChange w).obj ((baseChange c).obj G)) ≅
      (baseChange c).obj ((baseChange d).obj G) :=
  (baseChange v).mapIso (squareComparison c w b c hwc G) ≪≫
    squareComparison c v a c hvc ((baseChange b).obj G) ≪≫
      (baseChange c).mapIso (pullbackComparison b a d hab G)

/-- The constructed comparison also traverses the generic tower first. -/
theorem squareTowerComparison_eq {S T : Scheme.{u}} (c : T ⟶ S)
    (a b d : S ⟶ S) (hab : a ≫ b = d)
    (v w z : T ⟶ T) (hvw : v ≫ w = z)
    (hvc : v ≫ c = c ≫ a) (hwc : w ≫ c = c ≫ b)
    (hzc : z ≫ c = c ≫ d) (G : GroupScheme S) :
    squareTowerComparison c a b d hab v w hvc hwc G =
      pullbackComparison w v z hvw ((baseChange c).obj G) ≪≫
        squareComparison c z d c hzc G := by
  apply Iso.ext
  simpa only [squareTowerComparison, Iso.trans_hom, Functor.mapIso_hom] using
    squareComparison_tower c a b d hab v w z hvw hvc hwc hzc G

/-- Canonical semilinear transport of a group pulled back from an original
base satisfies the usual tower law. -/
theorem descentBaseChangeIso_tower {B S : Scheme.{u}}
    (p : S ⟶ B) (a b d : S ⟶ S) (hab : a ≫ b = d)
    (ha : a ≫ p = p) (hb : b ≫ p = p) (hd : d ≫ p = p)
    (G : GroupScheme B) :
    pullbackComparison b a d hab ((baseChange p).obj G) ≪≫
        descentBaseChangeIso p d hd G =
      (baseChange a).mapIso (descentBaseChangeIso p b hb G) ≪≫
        descentBaseChangeIso p a ha G := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Grp.comp_hom_hom,
      Over.comp_left, Category.assoc, descentBaseChangeIso_hom_fst]
    erw [pullbackComparison_hom_fst_assoc b a d hab ((baseChange p).obj G)]
    erw [map_fst_assoc a (descentBaseChangeIso p b hb G).hom]
    rw [descentBaseChangeIso_hom_fst]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

end Langlands.GroupScheme.Descent
