import Langlands.GroupScheme.Reductive.AffinePinnedTransitions
import Langlands.GroupScheme.Descent.DisjointPullbackCoherence

/-! # Assembled transitions for an arbitrary pinned affine atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedAtlas

open Descent CoproductComponents

variable {S T W : Scheme.{u}} {G : GroupScheme S}
    (A : AffinePinnedAtlas G)

/-- The actual inclusion of a pinned chart into its atlas. -/
abbrev inclusion (i : S) : (A.chart i).model.base ⟶ A.space :=
  Sigma.ι (fun j : S => (A.chart j).model.base) i

@[reassoc (attr := simp)] theorem inclusion_projection (i : S) :
    A.inclusion i ≫ A.projection = (A.chart i).map := Sigma.ι_comp_desc _ _

/-- Recover the chart's base map from an actual coordinate factorization. -/
theorem coordinate_base (a : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (i : S) (q : W ⟶ T)
    (f : W ⟶ (A.chart i).model.base)
    (hf : f ≫ A.inclusion i = q ≫ a) (l : W ⟶ S) (hl : q ≫ k = l) :
    f ≫ (A.chart i).map = l := by
  rw [← A.inclusion_projection i, ← Category.assoc, hf, Category.assoc, ha, hl]

/-- Assemble the transition from a specified pinned chart to an atlas-valued map. -/
def chartToAtlas (P : RelativePinnedComparison.{u}) (C : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (b : T ⟶ A.space) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hb : b ≫ A.projection = k) :
    (baseChange k).obj G ≅ (baseChange k).obj G :=
  DisjointComponents.pullbackIsoAlong (toBase b) (fun _ => rfl) (fun _ => rfl)
    (fun i => C.transition P (A.chart i) (toBase b i ≫ f) (toComponent b i)
      (toBase b i ≫ k) (by rw [Category.assoc, hf])
      (A.coordinate_base b k hb i (toBase b i) (toComponent b i)
        (component_condition b i) _ rfl))

/-- Evaluate a chart-to-atlas transition on any specified chart coordinate. -/
theorem chartToAtlas_on_chart (P : RelativePinnedComparison.{u})
    (C : AffinePinnedChart G) (f : T ⟶ C.model.base)
    (b : T ⟶ A.space) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hb : b ≫ A.projection = k)
    (i : S) (q : W ⟶ T) (g : W ⟶ (A.chart i).model.base)
    (hg : g ≫ A.inclusion i = q ≫ b) (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hl hl (A.chartToAtlas P C f b k hf hb) =
      C.transition P (A.chart i) (q ≫ f) g l
        (by rw [Category.assoc, hf, hl])
        (A.coordinate_base b k hb i q g hg l hl) := by
  let v := lift b i q g hg
  have hv : v ≫ toBase b i = q := lift_toBase b i q g hg
  have hvl : v ≫ (toBase b i ≫ k) = l := by rw [← Category.assoc, hv, hl]
  unfold chartToAtlas
  rw [DisjointComponents.pullIso_pullbackIsoAlong_factor
    (toBase b) (fun _ => rfl) (fun _ => rfl) _ i v hv hl hl]
  rw [AffinePinnedChart.transition_pull]
  simp only [v, lift_toBase_assoc, lift_toComponent]

/-- Assemble transitions between two arbitrary atlas-valued maps over the base. -/
def transition (P : RelativePinnedComparison.{u})
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    (baseChange k).obj G ≅ (baseChange k).obj G :=
  DisjointComponents.pullbackIsoAlong (toBase a) (fun _ => rfl) (fun _ => rfl)
    (fun i => A.chartToAtlas P (A.chart i) (toComponent a i) (toBase a i ≫ b)
      (toBase a i ≫ k)
      (A.coordinate_base a k ha i (toBase a i) (toComponent a i)
        (component_condition a i) _ rfl)
      (by rw [Category.assoc, hb]))

/-- The assembled transition has the prescribed value on every pair of chart coordinates. -/
theorem transition_on_charts (P : RelativePinnedComparison.{u})
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (i j : S) (q : W ⟶ T)
    (f : W ⟶ (A.chart i).model.base) (g : W ⟶ (A.chart j).model.base)
    (hf : f ≫ A.inclusion i = q ≫ a) (hg : g ≫ A.inclusion j = q ≫ b)
    (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hl hl (A.transition P a b k ha hb) =
      (A.chart i).transition P (A.chart j) f g l
        (A.coordinate_base a k ha i q f hf l hl)
        (A.coordinate_base b k hb j q g hg l hl) := by
  let v := lift a i q f hf
  have hv : v ≫ toBase a i = q := lift_toBase a i q f hf
  have hvg : g ≫ A.inclusion j = v ≫ (toBase a i ≫ b) := by
    rw [← Category.assoc, hv, hg]
  unfold transition
  rw [DisjointComponents.pullIso_pullbackIsoAlong_factor
    (toBase a) (fun _ => rfl) (fun _ => rfl) _ i v hv hl hl]
  rw [A.chartToAtlas_on_chart P _ _ _ _ _ _ j v g hvg l
    (by rw [← Category.assoc, hv, hl])]
  simp only [v, lift_toComponent]

/-- Two actual isomorphisms agree if they agree on all pairs of chart coordinates. -/
theorem iso_ext_on_charts (a b : T ⟶ A.space) (k : T ⟶ S)
    {e d : (baseChange k).obj G ≅ (baseChange k).obj G}
    (h : ∀ (V : Scheme.{u}) (i j : S) (q : V ⟶ T)
      (f : V ⟶ (A.chart i).model.base) (g : V ⟶ (A.chart j).model.base),
      f ≫ A.inclusion i = q ≫ a → g ≫ A.inclusion j = q ≫ b →
      pullIso q rfl rfl e = pullIso q rfl rfl d) : e = d := by
  apply DisjointComponents.pullIso_ext_along (toBase a) (fun _ => rfl) (fun _ => rfl)
  intro i
  apply DisjointComponents.pullIso_ext_along
    (toBase (toBase a i ≫ b)) (fun _ => rfl) (fun _ => rfl)
  intro j
  rw [pullIso_pullIso, pullIso_pullIso]
  apply h _ i j _ (toBase (toBase a i ≫ b) j ≫ toComponent a i)
    (toComponent (toBase a i ≫ b) j)
  · simp only [Category.assoc, component_condition]
  · simpa only [Category.assoc] using component_condition (toBase a i ≫ b) j

/-- Triple chart coordinates detect equality of actual isomorphisms. -/
theorem iso_ext_on_three_charts (a b c : T ⟶ A.space) (k : T ⟶ S)
    {e d : (baseChange k).obj G ≅ (baseChange k).obj G}
    (h : ∀ (V : Scheme.{u}) (i j n : S) (q : V ⟶ T)
      (f : V ⟶ (A.chart i).model.base) (g : V ⟶ (A.chart j).model.base)
      (t : V ⟶ (A.chart n).model.base),
      f ≫ A.inclusion i = q ≫ a → g ≫ A.inclusion j = q ≫ b →
      t ≫ A.inclusion n = q ≫ c →
      pullIso q rfl rfl e = pullIso q rfl rfl d) : e = d := by
  apply A.iso_ext_on_charts a b k
  intro V i j q f g hf hg
  apply DisjointComponents.pullIso_ext_along
    (toBase (q ≫ c)) (fun _ => rfl) (fun _ => rfl)
  intro n
  rw [pullIso_pullIso, pullIso_pullIso]
  apply h _ i j n _ (toBase (q ≫ c) n ≫ f) (toBase (q ≫ c) n ≫ g)
    (toComponent (q ≫ c) n)
  · simp only [Category.assoc, hf]
  · simp only [Category.assoc, hg]
  · simpa only [Category.assoc] using component_condition (q ≫ c) n

@[simp] theorem transition_self (P : RelativePinnedComparison.{u})
    (a : T ⟶ A.space) (k : T ⟶ S) (ha : a ≫ A.projection = k) :
    A.transition P a a k ha ha = Iso.refl _ := by
  apply DisjointComponents.pullIso_ext_along (toBase a) (fun _ => rfl) (fun _ => rfl)
  intro i
  rw [A.transition_on_charts P a a k ha ha i i (toBase a i)
    (toComponent a i) (toComponent a i) (component_condition a i)
    (component_condition a i) _ rfl, AffinePinnedChart.transition_self]
  simp [pullIso]

/-- The assembled transition commutes with every further scheme pullback. -/
theorem transition_pull (P : RelativePinnedComparison.{u})
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (q : W ⟶ T) (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hl hl (A.transition P a b k ha hb) =
      A.transition P (q ≫ a) (q ≫ b) l
        (by rw [Category.assoc, ha, hl]) (by rw [Category.assoc, hb, hl]) := by
  apply A.iso_ext_on_charts (q ≫ a) (q ≫ b) l
  intro V i j r f g hf hg
  rw [pullIso_pullIso]
  rw [A.transition_on_charts P a b k ha hb i j (r ≫ q) f g
    (by simpa only [Category.assoc] using hf)
    (by simpa only [Category.assoc] using hg) _ (by rw [Category.assoc, hl])]
  rw [A.transition_on_charts P (q ≫ a) (q ≫ b) l _ _ i j r f g hf hg _ rfl]

/-- The assembled transitions satisfy the cocycle on every common test scheme. -/
theorem transition_trans (P : RelativePinnedComparison.{u})
    (a b c : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (hc : c ≫ A.projection = k) :
    A.transition P a c k ha hc =
      A.transition P a b k ha hb ≪≫ A.transition P b c k hb hc := by
  apply A.iso_ext_on_three_charts a b c k
  intro V i j n q f g t hf hg ht
  rw [pullIso_trans q rfl rfl rfl]
  rw [A.transition_on_charts P a c k ha hc i n q f t hf ht _ rfl,
    A.transition_on_charts P a b k ha hb i j q f g hf hg _ rfl,
    A.transition_on_charts P b c k hb hc j n q g t hg ht _ rfl]
  exact AffinePinnedChart.transition_trans P _ _ _ _ _ _ _ _ _ _

end Langlands.GroupScheme.AffinePinnedAtlas
