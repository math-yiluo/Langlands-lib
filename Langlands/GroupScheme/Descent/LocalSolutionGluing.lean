import Langlands.GroupScheme.Descent.LocalSolutionComparison
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Gluing supplied local solutions over a directed open cover -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 2500

namespace Langlands.GroupScheme.Descent

namespace LocalSolutionGluing

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G)
  (𝒰 : B.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]

/-- The cover obtained by restricting the original cover to each base chart. -/
abbrev cover : S.OpenCover := 𝒰.pullback₁ p

/-- The transition on the restricted original covering schemes. -/
abbrev coverMap {i j : 𝒰.I₀} (hij : i ⟶ j) := (cover (p := p) 𝒰).trans hij

@[reassoc (attr := simp)] theorem coverMap_fst {i j : 𝒰.I₀} (hij : i ⟶ j) :
    coverMap (p := p) 𝒰 hij ≫ pullback.fst p (𝒰.f j) = pullback.fst p (𝒰.f i) := by
  change pullback.map p (𝒰.f i) p (𝒰.f j) (𝟙 S) (𝒰.trans hij) (𝟙 B)
    (by simp) (by simp) ≫ _ = _
  simp

@[reassoc (attr := simp)] theorem coverMap_snd {i j : 𝒰.I₀} (hij : i ⟶ j) :
    coverMap (p := p) 𝒰 hij ≫ pullback.snd p (𝒰.f j) =
      pullback.snd p (𝒰.f i) ≫ 𝒰.trans hij := by
  change pullback.map p (𝒰.f i) p (𝒰.f j) (𝟙 S) (𝒰.trans hij) (𝟙 B)
    (by simp) (by simp) ≫ _ = _
  simp

/-- The canonical scheme map between the two restricted covering groups. -/
def groupMap {i j : 𝒰.I₀} (hij : i ⟶ j) :
    ((GroupScheme.baseChange (pullback.fst p (𝒰.f i))).obj G).X.left ⟶
      ((GroupScheme.baseChange (pullback.fst p (𝒰.f j))).obj G).X.left :=
  (pullbackComparison (pullback.fst p (𝒰.f j)) (coverMap (p := p) 𝒰 hij)
      (pullback.fst p (𝒰.f i)) (coverMap_fst (p := p) 𝒰 hij) G).inv.hom.hom.left ≫
    pullback.fst ((GroupScheme.baseChange (pullback.fst p (𝒰.f j))).obj G).X.hom
      (coverMap (p := p) 𝒰 hij)

@[reassoc (attr := simp)] theorem groupMap_fst {i j : 𝒰.I₀} (hij : i ⟶ j) :
    groupMap (p := p) (G := G) 𝒰 hij ≫ pullback.fst G.X.hom (pullback.fst p (𝒰.f j)) =
      pullback.fst G.X.hom (pullback.fst p (𝒰.f i)) := by
  simp only [groupMap, Category.assoc, pullbackComparison_inv_fst]

@[reassoc (attr := simp)] theorem groupMap_snd {i j : 𝒰.I₀} (hij : i ⟶ j) :
    groupMap (p := p) (G := G) 𝒰 hij ≫ pullback.snd G.X.hom (pullback.fst p (𝒰.f j)) =
      pullback.snd G.X.hom (pullback.fst p (𝒰.f i)) ≫ coverMap (p := p) 𝒰 hij := by
  have h := Over.w (pullbackComparison (pullback.fst p (𝒰.f j)) (coverMap (p := p) 𝒰 hij)
      (pullback.fst p (𝒰.f i)) (coverMap_fst (p := p) 𝒰 hij) G).inv.hom.hom
  change (pullbackComparison (pullback.fst p (𝒰.f j)) (coverMap (p := p) 𝒰 hij)
      (pullback.fst p (𝒰.f i)) (coverMap_fst (p := p) 𝒰 hij) G).inv.hom.hom.left ≫
    pullback.snd ((GroupScheme.baseChange (pullback.fst p (𝒰.f j))).obj G).X.hom
      (coverMap (p := p) 𝒰 hij) = pullback.snd G.X.hom (pullback.fst p (𝒰.f i)) at h
  have hh := congrArg (fun a => a ≫ coverMap (p := p) 𝒰 hij) h
  unfold groupMap
  rw [Category.assoc]
  change (pullbackComparison (pullback.fst p (𝒰.f j)) (coverMap (p := p) 𝒰 hij)
      (pullback.fst p (𝒰.f i)) (coverMap_fst (p := p) 𝒰 hij) G).inv.hom.hom.left ≫
    pullback.fst ((GroupScheme.baseChange (pullback.fst p (𝒰.f j))).obj G).X.hom
      (coverMap (p := p) 𝒰 hij) ≫
      ((GroupScheme.baseChange (pullback.fst p (𝒰.f j))).obj G).X.hom = _
  rw [pullback.condition]
  simpa only [Category.assoc] using hh

/-- The induced directed open cover of the original group scheme. -/
abbrev groupCover : G.X.left.OpenCover := (cover (p := p) 𝒰).pullback₁ G.X.hom

theorem groupMap_eq_trans {i j : 𝒰.I₀} (hij : i ⟶ j) :
    groupMap (p := p) (G := G) 𝒰 hij = (groupCover (p := p) (G := G) 𝒰).trans hij := by
  change groupMap (p := p) (G := G) 𝒰 hij =
    pullback.map G.X.hom (pullback.fst p (𝒰.f i)) G.X.hom (pullback.fst p (𝒰.f j))
      (𝟙 _) (coverMap (p := p) 𝒰 hij) (𝟙 _) (by simp) (by simp)
  apply pullback.hom_ext <;> simp

variable [Etale p] [Surjective p]
  (s : ∀ i : 𝒰.I₀, Solution (D.baseChange (𝒰.f i)))

/-- Transition between the chosen local quotient schemes. -/
def map {i j : 𝒰.I₀} (hij : i ⟶ j) : (s i).obj.X.left ⟶ (s j).obj.X.left :=
  D.localSolutionMap (pullback.snd p (𝒰.f j)) (pullback.fst p (𝒰.f j))
    (𝒰.f j) pullback.condition (pullback.snd p (𝒰.f i)) (coverMap (p := p) 𝒰 hij)
    (𝒰.trans hij) (coverMap_snd (p := p) 𝒰 hij) (pullback.fst p (𝒰.f i))
    (𝒰.f i) (coverMap_fst (p := p) 𝒰 hij) (𝒰.trans_map hij) pullback.condition (s j) (s i)

@[reassoc] theorem proj_map {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (s i).schemeProj ≫ map D 𝒰 s hij = groupMap (p := p) (G := G) 𝒰 hij ≫ (s j).schemeProj := by
  exact D.localSolutionMap_proj _ _ _ _ _ _ _ _ _ _ _ _ _ (s j) (s i)

theorem map_square {i j : 𝒰.I₀} (hij : i ⟶ j) :
    IsPullback (s i).obj.X.hom (map D 𝒰 s hij) (𝒰.trans hij) (s j).obj.X.hom :=
  D.localSolutionMap_square _ _ _ _ _ _ _ _ _ _ _ _ _ (s j) (s i)

@[simp] theorem map_id (i : 𝒰.I₀) : map D 𝒰 s (𝟙 i) = 𝟙 _ := by
  apply (cancel_epi (s i).schemeSolution.proj).mp
  change (s i).schemeProj ≫ _ = (s i).schemeProj ≫ _
  rw [proj_map, Category.comp_id]
  have h : groupMap (p := p) (G := G) 𝒰 (𝟙 i) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [coverMap]
  rw [h, Category.id_comp]

@[simp] theorem map_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    map D 𝒰 s (hij ≫ hjk) = map D 𝒰 s hij ≫ map D 𝒰 s hjk := by
  apply (cancel_epi (s i).schemeSolution.proj).mp
  change (s i).schemeProj ≫ _ = (s i).schemeProj ≫ _
  rw [proj_map, ← Category.assoc, proj_map, Category.assoc, proj_map]
  have h : groupMap (p := p) (G := G) 𝒰 (hij ≫ hjk) =
      groupMap (p := p) (G := G) 𝒰 hij ≫ groupMap (p := p) (G := G) 𝒰 hjk := by
    apply pullback.hom_ext <;> simp [coverMap, Category.assoc]
  simp only [h, Category.assoc]

/-- The functor of chosen local quotient schemes. -/
def functor : 𝒰.I₀ ⥤ Scheme.{u} where
  obj i := (s i).obj.X.left
  map hij := map D 𝒰 s hij
  map_id := map_id D 𝒰 s
  map_comp := map_comp D 𝒰 s

/-- Structure maps of the local solutions to their base charts. -/
def natTrans : functor D 𝒰 s ⟶ 𝒰.functorOfLocallyDirected where
  app i := (s i).obj.X.hom
  naturality := by
    intro i j hij
    exact (map_square D 𝒰 s hij).w.symm

/-- The supplied solutions form an actual relative gluing datum. -/
def data : 𝒰.RelativeGluingData where
  functor := functor D 𝒰 s
  natTrans := natTrans D 𝒰 s
  equifibered := by
    intro i j hij
    exact (map_square D 𝒰 s hij).flip

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

instance : HasColimit (functor D 𝒰 s) :=
  inferInstanceAs (HasColimit (data D 𝒰 s).functor)

/-- The glued underlying quotient over the original base. -/
def obj : Over B := Over.mk (data D 𝒰 s).toBase

theorem proj_compatible {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (groupCover (p := p) (G := G) 𝒰).trans hij ≫
        (s j).schemeProj ≫ colimit.ι (functor D 𝒰 s) j =
      (s i).schemeProj ≫ colimit.ι (functor D 𝒰 s) i := by
  rw [← groupMap_eq_trans, ← Category.assoc, ← proj_map, Category.assoc]
  exact congrArg ((s i).schemeProj ≫ ·) (colimit.w (functor D 𝒰 s) hij)

/-- The local quotient maps glue on the induced open cover of the original group. -/
def proj : G.X.left ⟶ (obj D 𝒰 s).left :=
  (groupCover (p := p) (G := G) 𝒰).glueMorphismsOfLocallyDirected
    (fun i => (s i).schemeProj ≫ colimit.ι (functor D 𝒰 s) i) (proj_compatible D 𝒰 s)

@[reassoc (attr := simp)] theorem local_proj (i : 𝒰.I₀) :
    pullback.fst G.X.hom (pullback.fst p (𝒰.f i)) ≫ proj D 𝒰 s =
      (s i).schemeProj ≫ colimit.ι (functor D 𝒰 s) i :=
  (groupCover (p := p) (G := G) 𝒰).map_glueMorphismsOfLocallyDirected
    _ (proj_compatible D 𝒰 s) i

/-- The glued quotient square is cartesian, as can be checked on the induced cover of `S`. -/
theorem square : IsPullback G.X.hom (proj D 𝒰 s) p (obj D 𝒰 s).hom := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (cover (p := p) 𝒰)
  intro i
  have h := ((s i).schemeProj_square.flip.paste_horiz
    ((data D 𝒰 s).isPullback_natTrans_ι_toBase i).flip).flip
  change IsPullback (pullback.snd G.X.hom (pullback.fst p (𝒰.f i)))
    (pullback.fst G.X.hom (pullback.fst p (𝒰.f i)) ≫ proj D 𝒰 s)
    (pullback.fst p (𝒰.f i) ≫ p) (data D 𝒰 s).toBase
  rw [local_proj, pullback.condition]
  exact h

end LocalSolutionGluing
end Langlands.GroupScheme.Descent
