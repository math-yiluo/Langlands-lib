import Langlands.GroupScheme.Lie.SmoothOpenSubgroup

/-! # Smoothness from a nonempty smooth open chart -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Existence of a nonempty smooth scheme openly included in a field group. -/
def HasNonemptySmoothOpenChart {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (j : U ⟶ H.X),
    Smooth U.hom ∧ Nonempty U.left ∧ IsOpenImmersion j.left

/-- A nonempty smooth open chart makes a locally finite-type group over a field smooth. -/
theorem smooth_of_nonempty_smooth_open_chart {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    (U : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom]
    [Smooth U.hom] [Nonempty U.left] (j : U ⟶ H.X) [IsOpenImmersion j.left] :
    Smooth H.X.hom := by
  let Ω : Type u := AlgebraicClosure k
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let H' := (GroupScheme.baseChange b).obj H
  let U' := (Over.pullback b).obj U
  let j' : U' ⟶ H'.X := (Over.pullback b).map j
  have : LocallyOfFiniteType H'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd H.X.hom b))
  have : Smooth U'.hom :=
    inferInstanceAs (Smooth (pullback.snd U.hom b))
  have : IsOpenImmersion j'.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b j inferInstance
  obtain ⟨hb1, hb2, hb3⟩ := fieldExtension_fpqc k Ω
  let : Surjective b := hb1
  obtain ⟨x, _hx⟩ := (inferInstance : Surjective (pullback.fst U.hom b)).surj
    (Classical.choice (inferInstance : Nonempty U.left))
  have : Smooth (j'.left ≫ H'.X.hom) := by
    simpa only [Over.w] using (inferInstance : Smooth U'.hom)
  have hne : (H'.X.hom.smoothLocus : Set H'.X.left).Nonempty := by
    refine ⟨j'.left x, ?_⟩
    change x ∈ j'.left ⁻¹ᵁ H'.X.hom.smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    trivial
  let : GrpObj (Over.mk H'.X.hom) := H'.grp
  have hs : Smooth H'.X.hom := smooth_of_nonempty_smoothLocus H'.X.hom hne
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := H.X.hom) (g := b) ⟨⟨hb1, hb2⟩, hb3⟩ hs

/-- The chart-existence condition implies smoothness for locally finite-type groups. -/
theorem HasNonemptySmoothOpenChart.smooth {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType H.X.hom] (h : HasNonemptySmoothOpenChart H) :
    Smooth H.X.hom := by
  obtain ⟨U, j, hU, hne, hj⟩ := h
  let := hU
  let := hne
  let := hj
  exact smooth_of_nonempty_smooth_open_chart H U j

end Langlands.GroupScheme
