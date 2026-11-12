import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemePointsTopology

/-! # The quotient point topology induced by an étale atlas -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology IsLocalRing

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The map from the ordinary points of a scheme chart to presheaf points. -/
def chartPointMap {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) : U.left → Points F :=
  Points.map a ∘ schemePoint U

/-- Chart point maps are natural in maps of the source schemes. -/
@[simp]
theorem chartPointMap_comp {F : Presheaf S} {U V : Over S} (g : V ⟶ U)
    (a : (schemeYoneda S).obj U ⟶ F) (x : V.left) :
    chartPointMap ((schemeYoneda S).map g ≫ a) x = chartPointMap a (g.left x) := by
  dsimp only [chartPointMap, Function.comp_apply]
  rw [Points.map_comp, schemePoint_naturality]

/-- A field-valued section is the image of the unique point of its test spectrum. -/
theorem chartPointMap_fieldPoint {F : Presheaf S} (p : FieldPoint F) :
    chartPointMap (uliftYonedaEquiv.{u + 1}.symm p.val) (closedPoint p.field) = Quot.mk _ p := by
  let T : Over S := Over.mk p.base
  let q : FieldPoint ((schemeYoneda S).obj T) :=
    ⟨p.field, p.base, ULift.up (𝟙 T)⟩
  have hq : schemePoint T (closedPoint p.field) = Quot.mk _ q :=
    schemePoint_schemeValue q
  dsimp only [chartPointMap, Function.comp_apply]
  rw [hq, Points.map_mk]
  change Quot.mk _ ⟨p.field, p.base,
    uliftYonedaEquiv.{u + 1} (uliftYonedaEquiv.{u + 1}.symm p.val)⟩ = Quot.mk _ p
  rw [Equiv.apply_symm_apply]

/-- A commutative square of chart maps gives a commuting square on ordinary points. -/
theorem chartPointMap_comm {F : Presheaf S} {P U V : Over S}
    {a : (schemeYoneda S).obj U ⟶ F} {b : (schemeYoneda S).obj V ⟶ F}
    {f : P ⟶ U} {g : P ⟶ V}
    (h : (schemeYoneda S).map f ≫ a = (schemeYoneda S).map g ≫ b) (x : P.left) :
    chartPointMap a (f.left x) = chartPointMap b (g.left x) := by
  rw [← chartPointMap_comp f a, ← chartPointMap_comp g b, h]

/-- Geometric surjectivity gives surjectivity on the quotient point set. -/
theorem surjective_chartPointMap {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsSurjective a) :
    Function.Surjective (chartPointMap a) := by
  intro x
  induction x using Quot.ind with
  | _ p =>
    let b : (schemeYoneda S).obj (Over.mk p.base) ⟶ F := uliftYonedaEquiv.{u + 1}.symm p.val
    let hr := ha.representable
    have hs : Surjective (hr.snd b).left :=
      ha.projection b (hr.fst b) (hr.snd b) (hr.isPullback b)
    obtain ⟨t, ht⟩ := hs.surj (closedPoint p.field)
    refine ⟨(hr.fst' b).left t, ?_⟩
    calc
      chartPointMap a ((hr.fst' b).left t) = chartPointMap b ((hr.snd b).left t) :=
        chartPointMap_comm (hr.isPullback' b).w t
      _ = Quot.mk _ p := by rw [ht]; exact chartPointMap_fieldPoint p

/-- A surjective étale atlas alone detects the open sets in the point topology. -/
theorem isOpen_pointTopology_iff_atlas {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a)
    (O : Set (Points F)) :
    IsOpen[pointTopology F] O ↔ IsOpen (chartPointMap a ⁻¹' O) := by
  let : TopologicalSpace (Points F) := pointTopology F
  constructor
  · intro hO
    exact hO.preimage (continuous_schemePoint_chart a ha)
  · intro hO
    apply (isOpen_pointTopology_iff F O).mpr
    intro V b hb
    let hr := ha.representable
    have hsq := hr.isPullback' b
    have hleft : Etale (hr.fst' b).left :=
      hb.projection a ((schemeYoneda S).map (hr.snd b)) (hr.fst' b) hsq.flip
    have hright : Etale (hr.snd b).left :=
      ha.projection b ((schemeYoneda S).map (hr.fst' b)) (hr.snd b) hsq
    have hsurj : Surjective (hr.snd b).left :=
      hs.projection b ((schemeYoneda S).map (hr.fst' b)) (hr.snd b) hsq
    let := hright
    have hquot := (hr.snd b).left.isOpenMap.isQuotientMap
      (hr.snd b).left.continuous hsurj.surj
    apply hquot.isOpen_preimage.mp
    have heq : (hr.snd b).left ⁻¹' (chartPointMap b ⁻¹' O) =
        (hr.fst' b).left ⁻¹' (chartPointMap a ⁻¹' O) := by
      ext t
      change chartPointMap b ((hr.snd b).left t) ∈ O ↔
        chartPointMap a ((hr.fst' b).left t) ∈ O
      rw [chartPointMap_comm hsq.w t]
    change IsOpen ((hr.snd b).left ⁻¹' (chartPointMap b ⁻¹' O))
    rw [heq]
    exact hO.preimage (hr.fst' b).left.continuous

/-- Every surjective étale atlas induces a quotient map on ordinary points. -/
theorem isQuotientMap_chartPointMap {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a) :
    @IsQuotientMap U.left (Points F) _ (pointTopology F) (chartPointMap a) := by
  let := pointTopology F
  exact ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen
    (fun O => (isOpen_pointTopology_iff_atlas a ha hs O).symm),
    surjective_chartPointMap a hs⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
