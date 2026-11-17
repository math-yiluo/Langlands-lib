import Langlands.Geometry.Analytic.DirectedAtlasReconstruction
import Langlands.Geometry.Analytic.SaturatedStrongCategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Full pullbacks from bounded pushouts of greatest-chart algebras -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The actual bounded pullback to a greatest target chart, on each source chart. -/
def pullbackAtTop (f : StrongHom A B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))
    (i : A.atlas.Index) :
    BoundedAlgHom K (B.atlas.algebra t) (A.atlas.algebra i) :=
  f.pullback i t (f.image_chart_top t ht i)

/-- Source restriction commutes with the actual greatest-chart pullback. -/
theorem restriction_comp_pullbackAtTop (f : StrongHom A B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))
    (i i' : A.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i')) :
    (A.atlas.restriction i i' hi).comp (f.pullbackAtTop t ht i') =
      f.pullbackAtTop t ht i :=
  f.restriction_comp_pullback i i' t hi
    (f.image_chart_top t ht i) (f.image_chart_top t ht i')

/-- Equality of the bounded maps to the greatest chart determines the complete
strong morphism, including the ambient map and every admissible pullback. -/
theorem ext_atTop {f g : StrongHom A B} (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))
    (hp : ∀ i, f.pullbackAtTop t ht i = g.pullbackAtTop t ht i) :
    f = g := by
  let hd : B.atlas.HasDirectedCharts := fun i j => ⟨t, ht i, ht j⟩
  let d := f.toLocalChartMapData hd (fun _ => t) (f.image_chart_top t ht)
  have hf : d.RealizedBy f := f.toLocalChartMapData_realizedBy hd _ _
  have hg : d.RealizedBy g := by
    intro i
    exact ⟨g.image_chart_top t ht i, (hp i).symm⟩
  exact (hf.eq_toStrongHom hd).trans (hg.eq_toStrongHom hd).symm

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set
open AffinoidAtlasPresentation AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P A B C T : SaturatedAtlasPresentation.{u, v, w} K}

/-- Greatest-chart pullbacks compute composition in the actual saturated category. -/
theorem pullbackAtTop_comp (a : T ⟶ A) (f : A ⟶ C)
    (tA : A.presentation.atlas.Index) (tC : C.presentation.atlas.Index)
    (hA : ∀ j, Set.range (A.presentation.atlas.chart j) ⊆
      Set.range (A.presentation.atlas.chart tA))
    (hC : ∀ j, Set.range (C.presentation.atlas.chart j) ⊆
      Set.range (C.presentation.atlas.chart tC))
    (i : T.presentation.atlas.Index) :
    (a ≫ f).pullbackAtTop tC hC i =
      (a.pullbackAtTop tA hA i).comp (f.pullbackAtTop tC hC tA) :=
  a.saturatedComp_pullback f T.hasAllLocalDomains A.hasAllLocalDomains i tA tC
    (a.image_chart_top tA hA i) (f.image_chart_top tC hC tA)
    ((a ≫ f).image_chart_top tC hC i)

section TopChartPushout

variable (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C)
  (tP : P.presentation.atlas.Index) (tA : A.presentation.atlas.Index)
  (tB : B.presentation.atlas.Index) (tC : C.presentation.atlas.Index)
  (hA : ∀ j, Set.range (A.presentation.atlas.chart j) ⊆
    Set.range (A.presentation.atlas.chart tA))
  (hB : ∀ j, Set.range (B.presentation.atlas.chart j) ⊆
    Set.range (B.presentation.atlas.chart tB))
  (hC : ∀ j, Set.range (C.presentation.atlas.chart j) ⊆
    Set.range (C.presentation.atlas.chart tC))

/-- Bounded-algebra pushout universality at the specified greatest charts.
The test algebra is arbitrary; no ambient analytic map is part of the input. -/
def TopChartPushout : Prop :=
  ∀ (E : PresentedAffinoidAlgebra K)
    (α : BoundedAlgHom K (A.presentation.atlas.algebra tA) E)
    (β : BoundedAlgHom K (B.presentation.atlas.algebra tB) E),
    α.comp (f.pullbackAtTop tC hC tA) = β.comp (g.pullbackAtTop tC hC tB) →
      ∃! ℓ : BoundedAlgHom K (P.presentation.atlas.algebra tP) E,
        ℓ.comp (p.pullbackAtTop tA hA tP) = α ∧
          ℓ.comp (q.pullbackAtTop tB hB tP) = β

variable {p q f g tP tA tB tC hA hB hC}

/-- A commuting strong cone supplies a compatible pair of bounded maps
on every source chart, with no greatest-chart hypothesis on the source. -/
theorem topChartPushout_cone_compatible (a : T ⟶ A) (b : T ⟶ B)
    (hab : a ≫ f = b ≫ g) (i : T.presentation.atlas.Index) :
    (a.pullbackAtTop tA hA i).comp (f.pullbackAtTop tC hC tA) =
      (b.pullbackAtTop tB hB i).comp (g.pullbackAtTop tC hC tB) := by
  rw [← pullbackAtTop_comp, ← pullbackAtTop_comp, hab]

/-- Bounded pushout universality constructs a unique complete strong lift
from every saturated source atlas, without a greatest chart on that source. -/
theorem TopChartPushout.existsUnique_lift
    (h : TopChartPushout p q f g tP tA tB tC hA hB hC)
    (hP : ∀ j, Set.range (P.presentation.atlas.chart j) ⊆
      Set.range (P.presentation.atlas.chart tP))
    (a : T ⟶ A) (b : T ⟶ B) (hab : a ≫ f = b ≫ g) :
    ∃! l : T ⟶ P, l ≫ p = a ∧ l ≫ q = b := by
  classical
  have hex : ∀ i : T.presentation.atlas.Index,
      ∃! ℓ : BoundedAlgHom K (P.presentation.atlas.algebra tP)
          (T.presentation.atlas.algebra i),
        ℓ.comp (p.pullbackAtTop tA hA tP) = a.pullbackAtTop tA hA i ∧
          ℓ.comp (q.pullbackAtTop tB hB tP) = b.pullbackAtTop tB hB i := by
    intro i
    exact h _ _ _ (topChartPushout_cone_compatible a b hab i)
  choose ℓ hℓ huniq using hex
  have hn (i i' : T.presentation.atlas.Index)
      (hi : Set.range (T.presentation.atlas.chart i) ⊆
        Set.range (T.presentation.atlas.chart i')) :
      (T.presentation.atlas.restriction i i' hi).comp (ℓ i') = ℓ i := by
    apply huniq i
    constructor
    · rw [BoundedAlgHom.comp_assoc, (hℓ i').1,
        a.restriction_comp_pullbackAtTop tA hA i i' hi]
    · rw [BoundedAlgHom.comp_assoc, (hℓ i').2,
        b.restriction_comp_pullbackAtTop tB hB i i' hi]
  let d : LocalChartMapData T.presentation P.presentation :=
    { indexMap := fun _ => tP
      pullback := ℓ
      restriction_comm := by
        intro i i' hi
        refine ⟨tP, Subset.rfl, Subset.rfl, ?_⟩
        simp only [P.presentation.atlas.restriction_id, BoundedAlgHom.comp_id]
        exact hn i i' hi }
  let hd : P.presentation.atlas.HasDirectedCharts :=
    fun i j => ⟨tP, hP i, hP j⟩
  let l : T ⟶ P := d.toStrongHom hd
  have hl (i : T.presentation.atlas.Index) :
      l.pullbackAtTop tP hP i = ℓ i :=
    d.toStrongHom_pullback_selected hd i
  have hla : l ≫ p = a := by
    apply ext_atTop tA hA
    intro i
    rw [pullbackAtTop_comp l p tP tA hP hA, hl, (hℓ i).1]
  have hlb : l ≫ q = b := by
    apply ext_atTop tB hB
    intro i
    rw [pullbackAtTop_comp l q tP tB hP hB, hl, (hℓ i).2]
  refine ⟨l, ⟨hla, hlb⟩, ?_⟩
  intro m hm
  apply ext_atTop tP hP
  intro i
  rw [hl]
  apply huniq i
  constructor
  · rw [← pullbackAtTop_comp m p tP tA hP hA, hm.1]
  · rw [← pullbackAtTop_comp m q tP tB hP hB, hm.2]

/-- The two projections jointly detect equality of complete strong morphisms. -/
theorem TopChartPushout.hom_ext
    (h : TopChartPushout p q f g tP tA tB tC hA hB hC)
    (hP : ∀ j, Set.range (P.presentation.atlas.chart j) ⊆
      Set.range (P.presentation.atlas.chart tP))
    (hc : p ≫ f = q ≫ g) (a b : T ⟶ P)
    (hp : a ≫ p = b ≫ p) (hq : a ≫ q = b ≫ q) :
    a = b := by
  have hab : (a ≫ p) ≫ f = (a ≫ q) ≫ g := by
    rw [Category.assoc, Category.assoc, hc]
  exact (h.existsUnique_lift hP (a ≫ p) (a ≫ q) hab).unique
    ⟨rfl, rfl⟩ ⟨hp.symm, hq.symm⟩

/-- Package the chartwise construction as the full limit of strong cones. -/
def TopChartPushout.isLimit
    (h : TopChartPushout p q f g tP tA tB tC hA hB hC)
    (hP : ∀ j, Set.range (P.presentation.atlas.chart j) ⊆
      Set.range (P.presentation.atlas.chart tP))
    (hc : p ≫ f = q ≫ g) : IsLimit (PullbackCone.mk p q hc) := by
  let lift (s : PullbackCone f g) :=
    (h.existsUnique_lift hP s.fst s.snd s.condition).exists.choose
  have fac (s : PullbackCone f g) :
      lift s ≫ p = s.fst ∧ lift s ≫ q = s.snd :=
    (h.existsUnique_lift hP s.fst s.snd s.condition).exists.choose_spec
  exact PullbackCone.IsLimit.mk hc lift
    (fun s => (fac s).1) (fun s => (fac s).2)
    (fun s m hm₁ hm₂ => h.hom_ext hP hc m (lift s)
      (hm₁.trans (fac s).1.symm) (hm₂.trans (fac s).2.symm))

/-- A bounded pushout of greatest-chart algebras gives a genuine pullback
in the category of saturated presentations with complete strong morphisms. -/
theorem TopChartPushout.isPullback
    (h : TopChartPushout p q f g tP tA tB tC hA hB hC)
    (hP : ∀ j, Set.range (P.presentation.atlas.chart j) ⊆
      Set.range (P.presentation.atlas.chart tP))
    (hc : p ≫ f = q ≫ g) : IsPullback p q f g where
  w := hc
  isLimit' := ⟨h.isLimit hP hc⟩

end TopChartPushout

end Langlands.Analytic.SaturatedAtlasPresentation
