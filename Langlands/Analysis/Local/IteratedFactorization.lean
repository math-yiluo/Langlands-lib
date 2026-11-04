import Langlands.Analysis.Local.QuotientFactorization

/-! # Iterated ordered coordinates and their actual quotient measure -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe uA uX uJ uY uG

section Coordinates

variable {A : Type uA} {X : Type uX} {J : Type uJ} {Y : Type uY} {G : Type uG}
  [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace J]
  [TopologicalSpace Y] [TopologicalSpace G]
  (a : A × X ≃ₜ J) (b : J × Y ≃ₜ G)

/-- Compose two ordered coordinate maps, retaining the factor order and
putting the last two factors in the quotient-coordinate position. -/
def iteratedFactorHomeomorph : A × (X × Y) ≃ₜ G :=
  ((Homeomorph.prodAssoc A X Y).symm.trans
    (a.prodCongr (Homeomorph.refl Y))).trans b

@[simp] theorem iteratedFactorHomeomorph_apply (p : A × (X × Y)) :
    iteratedFactorHomeomorph a b p = b (a (p.1, p.2.1), p.2.2) := rfl

@[simp] theorem iteratedFactorHomeomorph_symm_apply (g : G) :
    (iteratedFactorHomeomorph a b).symm g =
      ((a.symm (b.symm g).1).1, ((a.symm (b.symm g).1).2, (b.symm g).2)) := rfl

variable [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace J]
  [MeasurableSpace Y] [MeasurableSpace G]
  (μA : Measure A) (μX : Measure X) (μJ : Measure J) (μY : Measure Y) (μG : Measure G)
  [SFinite μA] [SFinite μX] [SFinite μY]

/-- Exact preservation for the two coordinate maps implies exact preservation
for the composite. The composite product identity is a conclusion. -/
theorem measurePreserving_iteratedFactorHomeomorph
    (ha : MeasurePreserving a (μA.prod μX) μJ)
    (hb : MeasurePreserving b (μJ.prod μY) μG) :
    MeasurePreserving (iteratedFactorHomeomorph a b)
      (μA.prod (μX.prod μY)) μG := by
  have hAssoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μA μX μY)
  exact hb.comp ((ha.prod (MeasurePreserving.id μY)).comp hAssoc)

end Coordinates

section Subgroups

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (H J : Subgroup G) {X : Type uX} {Y : Type uY}
  [TopologicalSpace X] [TopologicalSpace Y]
  (s : X → G) (t : Y → G)
  (a : H × X ≃ₜ J) (b : J × Y ≃ₜ G)
  (ha : ∀ p : H × X, (a p : G) = p.1.val * s p.2)
  (hb : ∀ p : J × Y, b p = p.1.val * t p.2)

include ha hb in
/-- Iterating literal ordered multiplication gives the same literal order
with the last two factors parenthesized together. -/
theorem iteratedFactorHomeomorph_eq (p : H × (X × Y)) :
    iteratedFactorHomeomorph a b p = p.1.val * (s p.2.1 * t p.2.2) := by
  rw [iteratedFactorHomeomorph_apply, hb, ha, mul_assoc]

section ProductMeasures

variable [MeasurableSpace G] [MeasurableSpace H] [MeasurableSpace J]
  [MeasurableSpace X] [MeasurableSpace Y]
  {μG : Measure G} {μH : Measure H} {μJ : Measure J}
  {μX : Measure X} {μY : Measure Y}
  [SFinite μH] [SFinite μX] [SFinite μY]

include ha hb in
/-- A separately supplied literal composite chart has the same derived product
normalization. This permits reuse of existing ordered-coordinate records. -/
theorem measurePreserving_factorProduct_of_iterated
    (m : H × (X × Y) ≃ₜ G)
    (hm : ∀ p : H × (X × Y), m p = p.1.val * (s p.2.1 * t p.2.2))
    (haμ : MeasurePreserving a (μH.prod μX) μJ)
    (hbμ : MeasurePreserving b (μJ.prod μY) μG) :
    MeasurePreserving m (μH.prod (μX.prod μY)) μG := by
  have he : m = iteratedFactorHomeomorph a b := by
    ext p
    exact (hm p).trans (iteratedFactorHomeomorph_eq H J s t a b ha hb p).symm
  rw [he]
  exact measurePreserving_iteratedFactorHomeomorph a b μH μX μJ μY μG haμ hbμ

end ProductMeasures

variable [IsTopologicalGroup G]

/-- The actual quotient chart obtained from the two ordered coordinate maps.
No group structure on either quotient-coordinate space is required. -/
def iteratedFactorQuotientHomeomorph : (X × Y) ≃ₜ LeftQuotient H :=
  factorQuotientHomeomorph H (fun p : X × Y => s p.1 * t p.2)
    (iteratedFactorHomeomorph a b) (iteratedFactorHomeomorph_eq H J s t a b ha hb)

@[simp] theorem iteratedFactorQuotientHomeomorph_apply (p : X × Y) :
    iteratedFactorQuotientHomeomorph H J s t a b ha hb p =
      leftQuotientMap H (s p.1 * t p.2) := rfl

/-- The inverse chart reads the second coordinate of the first factorization
and the second coordinate of the second factorization. -/
@[simp] theorem iteratedFactorQuotientHomeomorph_symm_mk (g : G) :
    (iteratedFactorQuotientHomeomorph H J s t a b ha hb).symm
      (leftQuotientMap H g) =
      ((a.symm (b.symm g).1).2, (b.symm g).2) := by
  exact factorQuotientHomeomorph_symm_mk H _ _ _ g

section Measures

variable [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace J]
  [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace (X × Y)]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  {μG : Measure G} {μH : Measure H} {μJ : Measure J}
  {μX : Measure X} {μY : Measure Y}
  [IsFiniteMeasureOnCompacts μG]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
  [SFinite μH] [SFinite μX] [SFinite μY] [(μX.prod μY).Regular]
  {ν : Measure (LeftQuotient H)}

/-- Two exact intermediate product identities determine the actual composite
quotient normalization, without supplying a third product identity. -/
theorem IsCompatible.measurePreserving_iteratedFactorQuotientHomeomorph
    (hν : IsCompatible H μG μH ν) (hH : IsClosed (H : Set G))
    (haμ : MeasurePreserving a (μH.prod μX) μJ)
    (hbμ : MeasurePreserving b (μJ.prod μY) μG) :
    MeasurePreserving (iteratedFactorQuotientHomeomorph H J s t a b ha hb)
      (μX.prod μY) ν := by
  exact hν.measurePreserving_factorQuotientHomeomorph H _ _
    (iteratedFactorHomeomorph_eq H J s t a b ha hb) hH
    (measurePreserving_iteratedFactorHomeomorph a b μH μX μJ μY μG haμ hbμ)

end Measures

end Subgroups

end Langlands.QuotientIntegration
