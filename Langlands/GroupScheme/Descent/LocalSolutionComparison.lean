import Langlands.GroupScheme.Descent.SquareComparisonProjection
import Langlands.GroupScheme.Descent.ReverseRefinement
import Langlands.GroupScheme.Descent.SchemeSolution

/-! # Comparing actual solutions over nested base restrictions -/

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

variable {p : S ⟶ B} [Etale p] [Surjective p]
  {G H : GroupScheme S} {D : Datum p G} {F : Datum p H}

/-- Descent of a compatible homomorphism commutes with the actual quotient maps. -/
@[reassoc] theorem descendHomOfEtale_schemeProj (s : Solution D) (t : Solution F)
    (f : G ⟶ H) (hf : Compatible D F f) :
    s.schemeProj ≫ (s.descendHomOfEtale t f hf).hom.hom.left =
      f.hom.hom.left ≫ t.schemeProj := by
  have h : s.iso.inv ≫ (Langlands.GroupScheme.baseChange p).map (s.descendHomOfEtale t f hf) =
      f ≫ t.iso.inv := by
    apply (cancel_mono t.iso.hom).mp
    simp only [Category.assoc, baseChange_descendHomOfEtale, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hh := congrArg (fun a => a.hom.hom.left ≫ pullback.fst t.obj.X.hom p) h
  simpa only [schemeProj, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    map_fst] using hh

/-- Descent of a compatible isomorphism commutes with the actual quotient maps. -/
@[reassoc] theorem descendIsoOfEtale_schemeProj (s : Solution D) (t : Solution F)
    (e : G ≅ H) (he : Compatible D F e.hom) :
    s.schemeProj ≫ (s.descendIsoOfEtale t e he).hom.hom.hom.left =
      e.hom.hom.hom.left ≫ t.schemeProj :=
  s.descendHomOfEtale_schemeProj t e.hom he

end Solution

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- Associativity of restriction with specified representatives of the composites. -/
theorem reindex_comp_compatible_of_eq (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c) (q' : W ⟶ S) (b' : E ⟶ B)
    (hq : v ≫ q = q') (hb : c ≫ b = b') (w' : q' ≫ p = r ≫ b') :
    Compatible ((D.reindex t q b w₁).reindex r v c w₂)
      (D.reindex r q' b' w') (pullbackComparison q v q' hq G).hom := by
  subst q'
  subst b'
  exact D.reindex_comp_compatible t q b w₁ r v c w₂

/-- Collapse restriction along two squares with specified representatives of their composites. -/
def collapseReindexSolutionOfEq (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c) (q' : W ⟶ S) (b' : E ⟶ B)
    (hq : v ≫ q = q') (hb : c ≫ b = b') (w' : q' ≫ p = r ≫ b')
    (s : Solution ((D.reindex t q b w₁).reindex r v c w₂)) :
    Solution (D.reindex r q' b' w') :=
  s.mapIso (pullbackComparison q v q' hq G)
    (D.reindex_comp_compatible_of_eq t q b w₁ r v c w₂ q' b' hq hb w')

/-- Restrict a local solution and compare it to the datum in the chosen direct coordinates. -/
def localRestriction (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c) (q' : W ⟶ S) (b' : E ⟶ B)
    (hq : v ≫ q = q') (hb : c ≫ b = b') (w' : q' ≫ p = r ≫ b')
    (s : Solution (D.reindex t q b w₁)) : Solution (D.reindex r q' b' w') :=
  D.collapseReindexSolutionOfEq t q b w₁ r v c w₂ q' b' hq hb w'
    (s.reindex r v c w₂)

/-- The descended group of a local restriction is its actual base change. -/
theorem localRestriction_obj (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c) (q' : W ⟶ S) (b' : E ⟶ B)
    (hq : v ≫ q = q') (hb : c ≫ b = b') (w' : q' ≫ p = r ≫ b')
    (s : Solution (D.reindex t q b w₁)) :
    (D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s).obj =
      (Langlands.GroupScheme.baseChange c).obj s.obj := rfl

/-- The restricted quotient map agrees with the original quotient after projection. -/
@[reassoc] theorem localRestriction_proj (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) (v : W ⟶ V) (c : E ⟶ C)
    (w₂ : v ≫ t = r ≫ c) (q' : W ⟶ S) (b' : E ⟶ B)
    (hq : v ≫ q = q') (hb : c ≫ b = b') (w' : q' ≫ p = r ≫ b')
    (s : Solution (D.reindex t q b w₁)) :
    let s' := D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s
    s'.schemeProj ≫ pullback.fst s.obj.X.hom c =
      (pullbackComparison q v q' hq G).inv.hom.hom.left ≫
        pullback.fst ((Langlands.GroupScheme.baseChange q).obj G).X.hom v ≫ s.schemeProj := by
  simp only [localRestriction, collapseReindexSolutionOfEq,
    Solution.mapIso, Solution.reindex, Solution.schemeProj, Iso.trans_inv, Functor.mapIso_inv,
    Grp.comp_hom_hom, Over.comp_left, Category.assoc, squareComparison_inv_fst_fst, map_fst_assoc]

section LocalComparison

variable (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
  (w₁ : q ≫ p = t ≫ b) (r : W ⟶ E) [Etale r] [Surjective r]
  (v : W ⟶ V) (c : E ⟶ C) (w₂ : v ≫ t = r ≫ c)
  (q' : W ⟶ S) (b' : E ⟶ B) (hq : v ≫ q = q') (hb : c ≫ b = b')
  (w' : q' ≫ p = r ≫ b')
  (s : Solution (D.reindex t q b w₁)) (a : Solution (D.reindex r q' b' w'))

/-- Actual comparison between a chosen smaller solution and the restricted larger one. -/
def localSolutionComparison : a.obj ≅ (Langlands.GroupScheme.baseChange c).obj s.obj :=
  a.descendIsoOfEtale
    (D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s)
    (Iso.refl _) (compatible_id _)

/-- The transition map between the underlying local quotient schemes. -/
def localSolutionMap : a.obj.X.left ⟶ s.obj.X.left :=
  (D.localSolutionComparison t q b w₁ r v c w₂ q' b' hq hb w' s a).hom.hom.hom.left ≫
    pullback.fst s.obj.X.hom c

/-- The transition is determined by the two local quotient maps. -/
@[reassoc] theorem localSolutionMap_proj :
    a.schemeProj ≫ D.localSolutionMap t q b w₁ r v c w₂ q' b' hq hb w' s a =
      (pullbackComparison q v q' hq G).inv.hom.hom.left ≫
        pullback.fst ((Langlands.GroupScheme.baseChange q).obj G).X.hom v ≫
          s.schemeProj := by
  rw [localSolutionMap, ← Category.assoc]
  change (a.schemeProj ≫ (a.descendIsoOfEtale
    (D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s)
    (Iso.refl _) (compatible_id _)).hom.hom.hom.left) ≫ _ = _
  rw [Solution.descendIsoOfEtale_schemeProj]
  change (D.localRestriction t q b w₁ r v c w₂ q' b' hq hb w' s).schemeProj ≫
    pullback.fst s.obj.X.hom c = _
  exact D.localRestriction_proj t q b w₁ r v c w₂ q' b' hq hb w' s

/-- The transition map exhibits the smaller quotient as the base change of the larger. -/
theorem localSolutionMap_square :
    IsPullback a.obj.X.hom
      (D.localSolutionMap t q b w₁ r v c w₂ q' b' hq hb w' s a) c s.obj.X.hom := by
  let e := D.localSolutionComparison t q b w₁ r v c w₂ q' b' hq hb w' s a
  refine (IsPullback.of_hasPullback s.obj.X.hom c).flip.of_iso'
    (((Grp.forget (Over E)) ⋙ Over.forget E).mapIso e)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change e.hom.hom.hom.left ≫ pullback.snd s.obj.X.hom c = a.obj.X.hom ≫ 𝟙 E
    exact (Over.w e.hom.hom.hom).trans (Category.comp_id _).symm
  · rfl
  · exact (Category.id_comp c).trans (Category.comp_id c).symm
  · exact (Category.id_comp s.obj.X.hom).trans (Category.comp_id s.obj.X.hom).symm

/-- The local quotient equation uniquely determines the transition map. -/
theorem localSolutionMap_unique (f : a.obj.X.left ⟶ s.obj.X.left)
    (hf : a.schemeProj ≫ f =
      (pullbackComparison q v q' hq G).inv.hom.hom.left ≫
        pullback.fst ((Langlands.GroupScheme.baseChange q).obj G).X.hom v ≫
          s.schemeProj) :
    f = D.localSolutionMap t q b w₁ r v c w₂ q' b' hq hb w' s a := by
  apply (cancel_epi a.schemeSolution.proj).mp
  exact hf.trans (D.localSolutionMap_proj t q b w₁ r v c w₂ q' b' hq hb w' s a).symm

end LocalComparison
end Datum
end Langlands.GroupScheme.Descent
