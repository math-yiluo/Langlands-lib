import Langlands.GroupScheme.Rational.UnipotentRadicalDescent
import Langlands.GroupScheme.CocharacterTransportNaturality

/-! # Semilinear coherence for commuting pullback squares -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

variable {B S U V : Scheme.{u}}

/-- Compare the two successive group pullbacks in a commuting square. -/
def squareComparison (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (G : GroupScheme B) :
    (baseChange c).obj ((baseChange b).obj G) ≅
      (baseChange e).obj ((baseChange d).obj G) :=
  pullbackComparison b c (e ≫ d) h G ≪≫
    (pullbackComparison d e (e ≫ d) rfl G).symm

/-- The comparison preserves the projection to the original group. -/
@[reassoc] theorem squareComparison_hom_fst_fst
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (G : GroupScheme B) :
    (squareComparison b c d e h G).hom.hom.hom.left ≫
        pullback.fst ((baseChange d).obj G).X.hom e ≫ pullback.fst G.X.hom d =
      pullback.fst ((baseChange b).obj G).X.hom c ≫ pullback.fst G.X.hom b := by
  simp only [squareComparison, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom,
    Over.comp_left, Category.assoc, pullbackComparison_inv_fst,
    pullbackComparison_hom_fst]

/-- The comparison is natural in the original group. -/
@[reassoc] theorem squareComparison_naturality
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) {G H : GroupScheme B} (f : G ⟶ H) :
    (baseChange c).map ((baseChange b).map f) ≫
        (squareComparison b c d e h H).hom =
      (squareComparison b c d e h G).hom ≫
        (baseChange e).map ((baseChange d).map f) := by
  simp only [squareComparison, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, pullbackComparison_naturality, Category.assoc,
    pullbackComparison_inv_naturality]
  simp only [Category.assoc]

/-- Morphisms into an iterated pullback are determined by their projection
all the way to the original group. -/
theorem hom_ext_pullback_tower (b : S ⟶ B) (c : V ⟶ S) (G : GroupScheme B)
    {H : GroupScheme V}
    {f g : H ⟶ (baseChange c).obj ((baseChange b).obj G)}
    (h : f.hom.hom.left ≫ pullback.fst ((baseChange b).obj G).X.hom c ≫
        pullback.fst G.X.hom b =
      g.hom.hom.left ≫ pullback.fst ((baseChange b).obj G).X.hom c ≫
        pullback.fst G.X.hom b) : f = g := by
  apply (cancel_mono (pullbackComparison b c (c ≫ b) rfl G).hom).mp
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullbackComparison_hom_fst] using h
  · exact (Over.w (f ≫ (pullbackComparison b c (c ≫ b) rfl G).hom).hom.hom).trans
      (Over.w (g ≫ (pullbackComparison b c (c ≫ b) rfl G).hom).hom.hom).symm

@[reassoc] private theorem map_fst {T W : Scheme.{u}} (q : W ⟶ T)
    {G H : GroupScheme T} (f : G ⟶ H) :
    ((baseChange q).map f).hom.hom.left ≫ pullback.fst H.X.hom q =
      pullback.fst G.X.hom q ≫ f.hom.hom.left := by
  exact pullback.lift_fst _ _ _

/-- Canonical semilinear transport commutes with a commuting square. -/
theorem squareComparison_semilinear
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (a : S ⟶ S) (ha : a ≫ b = b)
    (v : V ⟶ V) (hv : v ≫ e = e) (hvc : v ≫ c = c ≫ a)
    (G : GroupScheme B) :
    (baseChange v).map (squareComparison b c d e h G).hom ≫
        (descentBaseChangeIso e v hv ((baseChange d).obj G)).hom =
      (squareComparison c v a c hvc ((baseChange b).obj G)).hom ≫
        (baseChange c).map (descentBaseChangeIso b a ha G).hom ≫
          (squareComparison b c d e h G).hom := by
  apply hom_ext_pullback_tower d e G
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    descentBaseChangeIso_hom_fst, descentBaseChangeIso_hom_fst_assoc, map_fst_assoc,
    squareComparison_hom_fst_fst]
  erw [map_fst_assoc v (squareComparison b c d e h G).hom]
  conv_rhs =>
    erw [squareComparison_hom_fst_fst_assoc c v a c hvc ((baseChange b).obj G)]
  rw [squareComparison_hom_fst_fst]

end Langlands.GroupScheme.Descent
