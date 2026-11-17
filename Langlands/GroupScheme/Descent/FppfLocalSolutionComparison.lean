import Langlands.GroupScheme.Descent.LocalSolutionComparison
import Langlands.GroupScheme.Descent.FppfReverseRefinement
import Langlands.GroupScheme.Descent.FppfSchemeSolution

/-! # Comparing actual solutions over nested base restrictions along fppf maps -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 2500

namespace Langlands.GroupScheme.Descent

variable {B S C V E W : Scheme.{u}}

@[reassoc] private theorem map_fst {T U : Scheme.{u}} (a : U ⟶ T)
    {G H : GroupScheme T} (f : G ⟶ H) :
    ((baseChange a).map f).hom.hom.left ≫ pullback.fst H.X.hom a =
      pullback.fst G.X.hom a ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

namespace Solution

variable {p : S ⟶ B} [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  {G H : GroupScheme S} {D : Datum p G} {F : Datum p H}

/-- Descent of a compatible homomorphism commutes with the actual quotient maps. -/
@[reassoc] theorem descendHomOfFppf_schemeProj (s : Solution D) (t : Solution F)
    (f : G ⟶ H) (hf : Compatible D F f) :
    s.schemeProj ≫ (s.descendHomOfFppf t f hf).hom.hom.left =
      f.hom.hom.left ≫ t.schemeProj := by
  have h : s.iso.inv ≫ (Langlands.GroupScheme.baseChange p).map (s.descendHomOfFppf t f hf) =
      f ≫ t.iso.inv := by
    apply (cancel_mono t.iso.hom).mp
    simp only [Category.assoc, baseChange_descendHomOfFppf, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hh := congrArg (fun a => a.hom.hom.left ≫ pullback.fst t.obj.X.hom p) h
  simpa only [schemeProj, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    map_fst] using hh

/-- Descent of a compatible isomorphism commutes with the actual quotient maps. -/
@[reassoc] theorem descendIsoOfFppf_schemeProj (s : Solution D) (t : Solution F)
    (e : G ≅ H) (he : Compatible D F e.hom) :
    s.schemeProj ≫ (s.descendIsoOfFppf t e he).hom.hom.hom.left =
      e.hom.hom.hom.left ≫ t.schemeProj :=
  s.descendHomOfFppf_schemeProj t e.hom he

end Solution

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

section FppfLocalComparison

variable (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
  (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) [Flat r] [LocallyOfFinitePresentation r] [Surjective r]
  (v : W ⟶ V) (c : E ⟶ C) (w₂ : v ≫ t = r ≫ c)
  (q' : W ⟶ S) (b' : E ⟶ B) (hq : v ≫ q = q') (hb : c ≫ b = b')
  (w' : q' ≫ p = r ≫ b')
  (s : Solution (D.reindex t q b w₁)) (a : Solution (D.reindex r q' b' w'))

/-- Actual comparison between a chosen smaller solution and the restricted larger one. -/
def fppfLocalSolutionComparison : a.obj ≅ (Langlands.GroupScheme.baseChange c).obj s.obj :=
  a.descendIsoOfFppf
    (D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s)
    (Iso.refl _) (compatible_id _)

/-- The transition map between the underlying local quotient schemes. -/
def fppfLocalSolutionMap : a.obj.X.left ⟶ s.obj.X.left :=
  (D.fppfLocalSolutionComparison t q b w₁ r v c w₂ q' b' hq hb w' s a).hom.hom.hom.left ≫
    pullback.fst s.obj.X.hom c

/-- The transition is determined by the two local quotient maps. -/
@[reassoc] theorem fppfLocalSolutionMap_proj :
    a.schemeProj ≫ D.fppfLocalSolutionMap t q b w₁ r v c w₂ q' b' hq hb w' s a =
      (pullbackComparison q v q' hq G).inv.hom.hom.left ≫
        pullback.fst ((Langlands.GroupScheme.baseChange q).obj G).X.hom v ≫
          s.schemeProj := by
  rw [fppfLocalSolutionMap, ← Category.assoc]
  change (a.schemeProj ≫ (a.descendIsoOfFppf
    (D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s)
    (Iso.refl _) (compatible_id _)).hom.hom.hom.left) ≫ _ = _
  rw [Solution.descendIsoOfFppf_schemeProj]
  change (D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s).schemeProj ≫
    pullback.fst s.obj.X.hom c = _
  exact D.localRestriction_proj t q b w₁ r v c w₂ q' b' hq hb w' s

/-- The transition map exhibits the smaller quotient as the base change of the larger. -/
theorem fppfLocalSolutionMap_square :
    IsPullback a.obj.X.hom
      (D.fppfLocalSolutionMap t q b w₁ r v c w₂ q' b' hq hb w' s a) c s.obj.X.hom := by
  let e := D.fppfLocalSolutionComparison t q b w₁ r v c w₂ q' b' hq hb w' s a
  refine (IsPullback.of_hasPullback s.obj.X.hom c).flip.of_iso'
    (((Grp.forget (Over E)) ⋙ Over.forget E).mapIso e)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change e.hom.hom.hom.left ≫ pullback.snd s.obj.X.hom c = a.obj.X.hom ≫ 𝟙 E
    exact (Over.w e.hom.hom.hom).trans (Category.comp_id _).symm
  · rfl
  · exact (Category.id_comp c).trans (Category.comp_id c).symm
  · exact (Category.id_comp s.obj.X.hom).trans (Category.comp_id s.obj.X.hom).symm

/-- The local quotient equation uniquely determines the transition map. -/
theorem fppfLocalSolutionMap_unique (f : a.obj.X.left ⟶ s.obj.X.left)
    (hf : a.schemeProj ≫ f =
      (pullbackComparison q v q' hq G).inv.hom.hom.left ≫
        pullback.fst ((Langlands.GroupScheme.baseChange q).obj G).X.hom v ≫
          s.schemeProj) :
    f = D.fppfLocalSolutionMap t q b w₁ r v c w₂ q' b' hq hb w' s a := by
  apply (cancel_epi a.schemeSolution.proj).mp
  exact hf.trans (D.fppfLocalSolutionMap_proj t q b w₁ r v c w₂ q' b' hq hb w' s a).symm

end FppfLocalComparison
end Datum
end Langlands.GroupScheme.Descent
