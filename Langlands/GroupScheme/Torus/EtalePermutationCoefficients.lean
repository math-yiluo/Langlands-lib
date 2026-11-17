import Langlands.GroupScheme.Torus.EtalePermutationAtlas
import Langlands.GroupScheme.Torus.LocalCoefficientReindexing

/-! # Coefficient equivalences on permutation-atlas overlaps -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme
namespace EtalePermutationAtlas

variable {S U V : Scheme.{u}} {D : GroupScheme S}
  {I J : Type u} [Finite I] [Finite J]

/-- A split chart evaluates original group points on a test over the chart. -/
def chartPointsEquiv (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    {T : Scheme.{u}} (t : T ⟶ U) :
    (Over.mk (t ≫ f) ⟶ D.X) ≃* (I → (Γ(T, ⊤))ˣ) :=
  (GroupScheme.baseChangePointsEquiv f D (Over.mk t)).symm.trans
    ((isoPointsEquiv e (Over.mk t)).trans (splitTorus.pointsEquiv I (Over.mk t)))

/-- Chart coordinates expressed using an underlying original-group morphism. -/
def coordinates (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    {T : Scheme.{u}} (t : T ⟶ U) (x : T ⟶ D.X.left)
    (hx : x ≫ D.X.hom = t ≫ f) : I → (Γ(T, ⊤))ˣ :=
  chartPointsEquiv f e t (Over.homMk x hx)

theorem coordinates_congr (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    {T : Scheme.{u}} {t t' : T ⟶ U} {x x' : T ⟶ D.X.left}
    (hx : x ≫ D.X.hom = t ≫ f) (hx' : x' ≫ D.X.hom = t' ≫ f)
    (ht : t = t') (hxx : x = x') :
    coordinates f e t x hx = coordinates f e t' x' hx' := by
  subst t'
  subst x'
  rfl

/-- A normalized restriction evaluates the same original chart on the same
original-group morphism. -/
theorem restrictChart_coordinates (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (q : V ⟶ U) (r : V ⟶ S) (h : q ≫ f = r)
    (T : Over V) (x : T ⟶ ((GroupScheme.baseChange r).obj D).X) :
    splitTorus.pointsEquiv I T (x ≫ (restrictChart f e q r h).hom.hom.hom) =
      coordinates f e (T.hom ≫ q) (x.left ≫ pullback.fst D.X.hom r)
        (by
          have hx : x.left ≫ pullback.snd D.X.hom r = T.hom := Over.w x
          rw [Category.assoc, pullback.condition, ← Category.assoc, hx,
            Category.assoc, h]) := by
  let c := Descent.pullbackComparison f q r h D
  let y := x ≫ c.inv.hom.hom
  have hy : GroupScheme.baseChangePointsEquiv f D ((Over.map q).obj T)
      (GroupScheme.baseChangePointsEquiv q ((GroupScheme.baseChange f).obj D) T y) =
      (Over.homMk (x.left ≫ pullback.fst D.X.hom r)
        (by
          change (x.left ≫ pullback.fst D.X.hom r) ≫ D.X.hom = (T.hom ≫ q) ≫ f
          have hx : x.left ≫ pullback.snd D.X.hom r = T.hom := Over.w x
          rw [Category.assoc, pullback.condition, ← Category.assoc, hx,
            Category.assoc, h]) :
          (Over.map f).obj ((Over.map q).obj T) ⟶ D.X) := by
    apply Over.OverMorphism.ext
    change (x.left ≫ c.inv.hom.hom.left) ≫
        pullback.fst ((GroupScheme.baseChange f).obj D).X.hom q ≫
          pullback.fst D.X.hom f = _
    simp only [Category.assoc, c, Descent.pullbackComparison_inv_fst]
    rfl
  have he : splitTorus.pointsEquiv I T
      ((y ≫ ((GroupScheme.baseChange q).map e.hom).hom.hom) ≫
        (splitTorus.baseChangeIso q I).hom.hom.hom) =
      splitTorus.pointsEquiv I ((Over.map q).obj T)
        (GroupScheme.baseChangePointsEquiv q ((GroupScheme.baseChange f).obj D) T y ≫
          e.hom.hom.hom) := by
    rw [show splitTorus.pointsEquiv I T
        ((y ≫ ((GroupScheme.baseChange q).map e.hom).hom.hom) ≫
          (splitTorus.baseChangeIso q I).hom.hom.hom) =
        splitTorus.baseChangePointsEquiv q I T
          (y ≫ ((GroupScheme.baseChange q).map e.hom).hom.hom) from
      isoOfPointModels_hom _ _ _ _ _ _ T _]
    simp only [splitTorus.baseChangePointsEquiv, MulEquiv.trans_apply,
      GroupScheme.baseChangePointsEquiv_comp]
    rfl
  change _ = splitTorus.pointsEquiv I ((Over.map q).obj T)
    ((GroupScheme.baseChangePointsEquiv f D ((Over.map q).obj T)).symm _ ≫ e.hom.hom.hom)
  rw [← hy, MulEquiv.symm_apply_apply]
  exact he

variable {U' : Scheme.{u}}

/-- Agreement of normalized charts can be tested directly on an original-group
morphism over the common base. -/
theorem AgreeBy.coordinates (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (r : V ⟶ S)
    (h : q ≫ f = r) (h' : q' ≫ g = r) (σ : J ≃ I)
    (H : AgreeBy f g e e' q q' r h h' σ)
    (T : Over V) (x : T.left ⟶ D.X.left) (hx : x ≫ D.X.hom = T.hom ≫ r)
    (j : J) :
    coordinates g e' (T.hom ≫ q') x (by rw [Category.assoc, h']; exact hx) j =
      coordinates f e (T.hom ≫ q) x (by rw [Category.assoc, h]; exact hx) (σ j) := by
  let p : (Over.map r).obj T ⟶ D.X := Over.homMk x hx
  let y := (GroupScheme.baseChangePointsEquiv r D T).symm p
  have hy : y.left ≫ pullback.fst D.X.hom r = x := by
    exact congrArg Over.Hom.left
      ((GroupScheme.baseChangePointsEquiv r D T).apply_symm_apply p)
  have Hxy := H T y j
  rw [restrictChart_coordinates, restrictChart_coordinates] at Hxy
  simpa only [hy] using Hxy

/-- The transition on unit families, defined from the two original charts on
every test over their common base. -/
def transitionUnits (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g)
    (T : Over V) (z : I → (Γ(T.left, ⊤))ˣ) : J → (Γ(T.left, ⊤))ˣ :=
  let x := (chartPointsEquiv f e (T.hom ≫ q)).symm z
  coordinates g e' (T.hom ≫ q') x.left (by
    exact (Over.w x).trans (by
      change (T.hom ≫ q) ≫ f = (T.hom ≫ q') ≫ g
      simp only [Category.assoc, h]))

/-- A local normalized permutation gives the formula for the single transition
on every test whose range is contained in the chosen open. -/
theorem transitionUnits_eq_on_open (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g)
    (O : V.Opens) (σ : J ≃ I)
    (H : AgreeBy f g e e' (O.ι ≫ q) (O.ι ≫ q') (O.ι ≫ q ≫ f)
      (by simp only [Category.assoc]) (by simp only [Category.assoc, h]) σ)
    (T : Over V) (hT : Set.range T.hom ⊆ O)
    (z : I → (Γ(T.left, ⊤))ˣ) (j : J) :
    transitionUnits f g e e' q q' h T z j = z (σ j) := by
  let a : T.left ⟶ (O : Scheme.{u}) :=
    IsOpenImmersion.lift O.ι T.hom (by simpa only [Scheme.Opens.range_ι] using hT)
  have ha : a ≫ O.ι = T.hom := IsOpenImmersion.lift_fac _ _ _
  let Z : Over (O : Scheme.{u}) := Over.mk a
  let x := (chartPointsEquiv f e (T.hom ≫ q)).symm z
  have hx : x.left ≫ D.X.hom = Z.hom ≫ (O.ι ≫ q ≫ f) := by
    change x.left ≫ D.X.hom = a ≫ O.ι ≫ q ≫ f
    rw [← Category.assoc a O.ι, ha, ← Category.assoc]
    exact Over.w x
  have Hx := AgreeBy.coordinates f g e e' (O.ι ≫ q) (O.ι ≫ q')
    (O.ι ≫ q ≫ f) _ _ σ H Z x.left hx j
  have hq : Z.hom ≫ (O.ι ≫ q) = T.hom ≫ q := by
    change a ≫ (O.ι ≫ q) = _
    rw [← Category.assoc, ha]
  have hq' : Z.hom ≫ (O.ι ≫ q') = T.hom ≫ q' := by
    change a ≫ (O.ι ≫ q') = _
    rw [← Category.assoc, ha]
  unfold transitionUnits
  change coordinates g e' (T.hom ≫ q') x.left _ j = _
  have Hx' :
      coordinates g e' (T.hom ≫ q') x.left
          ((Over.w x).trans (by
            change (T.hom ≫ q) ≫ f = (T.hom ≫ q') ≫ g
            simp only [Category.assoc, h])) j =
        coordinates f e (T.hom ≫ q) x.left (Over.w x) (σ j) := by
    simpa only [hq, hq'] using Hx
  exact Hx'.trans
    (congrFun ((chartPointsEquiv f e (T.hom ≫ q)).apply_symm_apply z) (σ j))

/-- A locally permuting pair of split charts supplies actual coefficient
gluing data on its scheme-theoretic overlap. -/
def LocallyPermutes.coefficientDatum (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e') :
    LocalCoefficientReindexing.Datum (pullback f g) I J := by
  classical
  choose O hO σ Hσ using H
  refine LocalCoefficientReindexing.ofUnitTransform O ?_ σ
    (transitionUnits f g e e' (pullback.fst f g) (pullback.snd f g)
      (pullback.condition)) ?_
  · apply top_unique
    intro w _
    exact (show O w ≤ ⨆ w, O w from le_iSup O w) (hO w)
  · intro w T hT z j
    exact transitionUnits_eq_on_open f g e e' _ _ _ (O w) (σ w) (Hσ w) T hT z j

/-- The global coefficient algebra equivalence on an atlas overlap. -/
def LocallyPermutes.coefficientEquiv (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e') :
    (I → Γ(pullback f g, ⊤)) ≃ₐ[Γ(pullback f g, ⊤)] (J → Γ(pullback f g, ⊤)) :=
  (H.coefficientDatum f g e e').equiv

end EtalePermutationAtlas
end Langlands.GroupScheme
