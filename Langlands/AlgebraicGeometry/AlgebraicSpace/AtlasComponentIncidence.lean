import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasPointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SameImageToolkit
import Langlands.Topology.QuotientConnectedComponents

/-! # Atlas kernel-pair incidence and connected components -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology IsLocalRing

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F : Presheaf S}

private def fieldPointChart (p : FieldPoint F) :
    (schemeYoneda S).obj (Over.mk p.base) ⟶ F :=
  uliftYonedaEquiv.{u + 1}.symm p.val

private theorem fieldPointChart_map {U : Over S}
    (p : FieldPoint ((schemeYoneda S).obj U)) (a : (schemeYoneda S).obj U ⟶ F) :
    fieldPointChart (p.map a) = (schemeYoneda S).map p.val.down ≫ a := by
  apply uliftYonedaEquiv.{u + 1}.injective
  simp only [fieldPointChart, Equiv.apply_symm_apply]
  rfl

private theorem sameImage₂_of_fieldPoint_rel {p q : FieldPoint F}
    (h : FieldPoint.Rel F p q) :
    SameImage₂ (fieldPointChart p) (fieldPointChart q)
      (closedPoint p.field) (closedPoint q.field) := by
  obtain ⟨Ω, _, i, j, hb, he⟩ := h
  let k : p.extendTest i ⟶ Over.mk q.base := Over.homMk (Spec.map (CommRingCat.ofHom j)) hb
  refine ⟨p.extendTest i, p.extendMap i, k,
    closedPoint Ω, ?_, ?_, ?_⟩
  · ext T t
    change F.map (t.down ≫ p.extendMap i).op p.val =
      F.map (t.down ≫ k).op q.val
    simp only [op_comp, Functor.map_comp_apply]
    exact congrArg (fun z => F.map t.down.op z) he
  · change (Spec.map (CommRingCat.ofHom i)) (closedPoint Ω) = closedPoint p.field
    exact Subsingleton.elim _ _
  · change (Spec.map (CommRingCat.ofHom j)) (closedPoint Ω) = closedPoint q.field
    exact Subsingleton.elim _ _

private theorem sameImage₂_of_fieldPoint_eq {p q : FieldPoint F}
    (h : (Quot.mk _ p : Points F) = Quot.mk _ q) :
    SameImage₂ (fieldPointChart p) (fieldPointChart q)
      (closedPoint p.field) (closedPoint q.field) := by
  have he := Quot.eqvGen_exact h
  clear h
  induction he with
  | rel p q hpq => exact sameImage₂_of_fieldPoint_rel hpq
  | refl p => exact SameImage₂.refl _ _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ hpq hqr => exact hpq.trans hqr

/-- Equality of quotient chart points is precisely the existing common-test-scheme
relation, for any two charts into any presheaf. -/
theorem chartPointMap_eq_iff_sameImage₂ {U V : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj V ⟶ F)
    (x : U.left) (y : V.left) :
    chartPointMap a x = chartPointMap b y ↔ SameImage₂ a b x y := by
  constructor
  · intro h
    let p : FieldPoint ((schemeYoneda S).obj U) :=
      ⟨U.left.residueField x, U.left.fromSpecResidueField x ≫ U.hom,
        ULift.up (Over.homMk (U.left.fromSpecResidueField x) rfl)⟩
    let q : FieldPoint ((schemeYoneda S).obj V) :=
      ⟨V.left.residueField y, V.left.fromSpecResidueField y ≫ V.hom,
        ULift.up (Over.homMk (V.left.fromSpecResidueField y) rfl)⟩
    have he : (Quot.mk _ (p.map a) : Points F) = Quot.mk _ (q.map b) := h
    have hs := sameImage₂_of_fieldPoint_eq he
    rw [fieldPointChart_map, fieldPointChart_map] at hs
    have ht := ((hs.of_comp p.val.down).symm.of_comp q.val.down).symm
    change SameImage₂ a b
      (U.left.fromSpecResidueField x (closedPoint (U.left.residueField x)))
      (V.left.fromSpecResidueField y (closedPoint (V.left.residueField y))) at ht
    simpa only [Scheme.fromSpecResidueField_apply] using ht
  · rintro ⟨T, g, k, t, he, hg, hk⟩
    rw [← hg, ← hk]
    exact chartPointMap_comm he t

/-- A represented pullback realizes every pair of chart points equal in the quotient. -/
theorem chartPointMap_eq_iff_exists_pullback {U V : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj V ⟶ F)
    (hb : IsRepresentableMorphism b) (x : U.left) (y : V.left) :
    chartPointMap a x = chartPointMap b y ↔
      ∃ r : (hb.pullback a).left,
        (hb.snd a).left r = x ∧ (hb.fst' a).left r = y := by
  rw [chartPointMap_eq_iff_sameImage₂]
  exact ⟨fun h => h.exists_pullback hb, fun ⟨r, hx, hy⟩ => by
    rw [← hx, ← hy]
    exact SameImage₂.of_pullback hb r⟩

/-- Two components of a scheme chart are incident when a point of its represented
kernel pair has its two projections in those components. -/
def atlasComponentIncidence {U : Over S} (a : (schemeYoneda S).obj U ⟶ F)
    (ha : IsRepresentableMorphism a) (c d : ConnectedComponents U.left) : Prop :=
  ∃ r : (ha.pullback a).left,
    ConnectedComponents.mk ((ha.snd a).left r) = c ∧
      ConnectedComponents.mk ((ha.fst' a).left r) = d

/-- Kernel-pair incidence is exactly the fibre relation on the chart's components. -/
theorem componentFibreRelation_chartPointMap_iff {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsRepresentableMorphism a)
    (c d : ConnectedComponents U.left) :
    Langlands.Topology.componentFibreRelation (chartPointMap a) c d ↔
      atlasComponentIncidence a ha c d := by
  constructor
  · rintro ⟨x, y, hx, hy, he⟩
    obtain ⟨r, hrx, hry⟩ := (chartPointMap_eq_iff_exists_pullback a a ha x y).mp he
    exact ⟨r, hrx ▸ hx, hry ▸ hy⟩
  · rintro ⟨r, hx, hy⟩
    refine ⟨(ha.snd a).left r, (ha.fst' a).left r, hx, hy, ?_⟩
    exact (chartPointMap_eq_iff_exists_pullback a a ha _ _).mpr ⟨r, rfl, rfl⟩

/-- The connected components of a presheaf with a surjective étale atlas are the
atlas components modulo kernel-pair incidence, when the atlas component space is discrete. -/
def atlasConnectedComponentsEquiv {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a)
    [DiscreteTopology (ConnectedComponents U.left)] :
    Quot (atlasComponentIncidence a ha.representable) ≃
      @ConnectedComponents (Points F) (pointTopology F) := by
  letI := pointTopology F
  exact (Quot.congr (Equiv.refl _) (fun c d =>
    (componentFibreRelation_chartPointMap_iff a ha.representable c d).symm)).trans
      (Langlands.Topology.quotientConnectedComponentsEquiv (chartPointMap a)
        (isQuotientMap_chartPointMap a ha hs))

end Langlands.AlgebraicGeometry.AlgebraicSpace
