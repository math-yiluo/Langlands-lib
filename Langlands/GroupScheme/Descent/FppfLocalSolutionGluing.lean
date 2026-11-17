import Langlands.GroupScheme.Descent.LocalSolutionGluing
import Langlands.GroupScheme.Descent.FppfLocalSolutionComparison

/-! # Gluing supplied local solutions of fppf data over a directed open cover -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 2500

namespace Langlands.GroupScheme.Descent

namespace FppfLocalSolutionGluing

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G)
  (𝒰 : B.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]

variable [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (s : ∀ i : 𝒰.I₀, Solution (D.baseChange (𝒰.f i)))

/-- Transition between the chosen local quotient schemes. -/
def map {i j : 𝒰.I₀} (hij : i ⟶ j) : (s i).obj.X.left ⟶ (s j).obj.X.left :=
  D.fppfLocalSolutionMap (pullback.snd p (𝒰.f j)) (pullback.fst p (𝒰.f j))
    (𝒰.f j) pullback.condition (pullback.snd p (𝒰.f i)) (LocalSolutionGluing.coverMap (p := p) 𝒰 hij)
    (𝒰.trans hij) (LocalSolutionGluing.coverMap_snd (p := p) 𝒰 hij) (pullback.fst p (𝒰.f i))
    (𝒰.f i) (LocalSolutionGluing.coverMap_fst (p := p) 𝒰 hij) (𝒰.trans_map hij) pullback.condition (s j) (s i)

@[reassoc] theorem proj_map {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (s i).schemeProj ≫ map D 𝒰 s hij = LocalSolutionGluing.groupMap (p := p) (G := G) 𝒰 hij ≫ (s j).schemeProj := by
  exact D.fppfLocalSolutionMap_proj _ _ _ _ _ _ _ _ _ _ _ _ _ (s j) (s i)

theorem map_square {i j : 𝒰.I₀} (hij : i ⟶ j) :
    IsPullback (s i).obj.X.hom (map D 𝒰 s hij) (𝒰.trans hij) (s j).obj.X.hom :=
  D.fppfLocalSolutionMap_square _ _ _ _ _ _ _ _ _ _ _ _ _ (s j) (s i)

@[simp] theorem map_id (i : 𝒰.I₀) : map D 𝒰 s (𝟙 i) = 𝟙 _ := by
  apply (cancel_epi (s i).schemeSolution.proj).mp
  change (s i).schemeProj ≫ _ = (s i).schemeProj ≫ _
  rw [proj_map, Category.comp_id]
  have h : LocalSolutionGluing.groupMap (p := p) (G := G) 𝒰 (𝟙 i) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [LocalSolutionGluing.coverMap]
  rw [h, Category.id_comp]

@[simp] theorem map_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    map D 𝒰 s (hij ≫ hjk) = map D 𝒰 s hij ≫ map D 𝒰 s hjk := by
  apply (cancel_epi (s i).schemeSolution.proj).mp
  change (s i).schemeProj ≫ _ = (s i).schemeProj ≫ _
  rw [proj_map, ← Category.assoc, proj_map, Category.assoc, proj_map]
  have h : LocalSolutionGluing.groupMap (p := p) (G := G) 𝒰 (hij ≫ hjk) =
      LocalSolutionGluing.groupMap (p := p) (G := G) 𝒰 hij ≫ LocalSolutionGluing.groupMap (p := p) (G := G) 𝒰 hjk := by
    apply pullback.hom_ext <;> simp [LocalSolutionGluing.coverMap, Category.assoc]
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
    (LocalSolutionGluing.groupCover (p := p) (G := G) 𝒰).trans hij ≫
        (s j).schemeProj ≫ colimit.ι (functor D 𝒰 s) j =
      (s i).schemeProj ≫ colimit.ι (functor D 𝒰 s) i := by
  rw [← LocalSolutionGluing.groupMap_eq_trans, ← Category.assoc, ← proj_map, Category.assoc]
  exact congrArg ((s i).schemeProj ≫ ·) (colimit.w (functor D 𝒰 s) hij)

/-- The local quotient maps glue on the induced open cover of the original group. -/
def proj : G.X.left ⟶ (obj D 𝒰 s).left :=
  (LocalSolutionGluing.groupCover (p := p) (G := G) 𝒰).glueMorphismsOfLocallyDirected
    (fun i => (s i).schemeProj ≫ colimit.ι (functor D 𝒰 s) i) (proj_compatible D 𝒰 s)

@[reassoc (attr := simp)] theorem local_proj (i : 𝒰.I₀) :
    pullback.fst G.X.hom (pullback.fst p (𝒰.f i)) ≫ proj D 𝒰 s =
      (s i).schemeProj ≫ colimit.ι (functor D 𝒰 s) i :=
  (LocalSolutionGluing.groupCover (p := p) (G := G) 𝒰).map_glueMorphismsOfLocallyDirected
    _ (proj_compatible D 𝒰 s) i

/-- The glued quotient square is cartesian, as can be checked on the induced cover of `S`. -/
theorem square : IsPullback G.X.hom (proj D 𝒰 s) p (obj D 𝒰 s).hom := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (LocalSolutionGluing.cover (p := p) 𝒰)
  intro i
  have h := ((s i).schemeProj_square.flip.paste_horiz
    ((data D 𝒰 s).isPullback_natTrans_ι_toBase i).flip).flip
  change IsPullback (pullback.snd G.X.hom (pullback.fst p (𝒰.f i)))
    (pullback.fst G.X.hom (pullback.fst p (𝒰.f i)) ≫ proj D 𝒰 s)
    (pullback.fst p (𝒰.f i) ≫ p) (data D 𝒰 s).toBase
  rw [local_proj, pullback.condition]
  exact h

end FppfLocalSolutionGluing
end Langlands.GroupScheme.Descent
