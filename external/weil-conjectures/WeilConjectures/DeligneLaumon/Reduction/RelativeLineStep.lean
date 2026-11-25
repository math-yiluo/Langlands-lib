/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine
public import WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification

/-!
# The relative affine-line step of the Deligne–Laumon reduction

For the projection `p : 𝔸¹_S ⟶ S` of the relative affine line over a separated `k₀`-scheme of
finite type, `Rʳp₀!F` is mixed of weights at most `w + r` whenever the Weil sheaf `F` is mixed of
weights at most `w`, and `Rp₀!` preserves Weil complexes mixed of weights at most `w`. Iterating,
the same holds for the projection of the `r`-fold relative affine line.

The proof stratifies a punctually pure sheaf on `𝔸¹_S`: its pieces are either separated
quasi-finite over `S`, or opens of a relative affine line `𝔸¹_V` over a locally closed `V ⊆ S`
with surjective projection on which the sheaf is lisse, and they are glued by open–closed
decompositions. The direct-image bound holds on each piece — by the quasi-finite lemma, resp. by
the relative affine-line proposition `theorem-pure-lisse-sheaves-over-relative` — and passes through
the gluing by the long exact sequences of the open–closed triangles.

The stratification itself (`AlgebraicGeometry.WeilSheaf.HasRelativeLineStratification` and
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.hasRelativeLineStratification`, blueprint
`proposition-relative-affine-line--1`) is constructed in
`WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.HasRelativeLineStratification.isMixedOfWeightsAtMost`: the weight
  bound on a stratified sheaf.
- `AlgebraicGeometry.hasDirectImageWeightBound_affineLine` and
  `AlgebraicGeometry.hasDirectImageComplexWeightBound_affineLine`: blueprint
  `proposition-relative-affine-line--1`, in its sheaf and its complex form.
- `AlgebraicGeometry.hasDirectImageWeightBound_iteratedAffineLineProj`: the bound for the
  projection of the iterated relative affine line.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §3.3.
-/

@[expose] public section

universe u

open CategoryTheory

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

section Stratification

variable {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]

variable [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (S ↘ Spec (CommRingCat.of k₀))]

variable {w : ℝ} in
/-- If `F` has a relative-line stratification over `S` with pure pieces of weight `w`, then
`Rʳh₀!F` is mixed of weights at most `w + r` for every `r`: on a quasi-finite piece by
`lemma-finite-quasi-finite-direct-images`, on a relative-line piece by
`theorem-pure-lisse-sheaves-over-relative` composed with the quasi-finite immersion `c`, and through
the gluing by the exact sequences of the open–closed triangles (blueprint:
`proposition-relative-affine-line--1`, the reassembly of the strata). -/
theorem WeilSheaf.HasRelativeLineStratification.isMixedOfWeightsAtMost
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {h : X ⟶ S}
    [h.IsOver (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (H : F.HasRelativeLineStratification ι w h) :
    ∀ [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] (r : ℕ),
      ((WeilSheaf.higherLowerShriek k₀ l h r).obj F).IsMixedOfWeightsAtMost ι (w + r) := by
  induction H with
  | quasiFinite h F hF =>
    exact fun r ↦ HasDirectImageWeightBound.of_locallyQuasiFinite h w F hF r
  | affineLine v hv c h hh F hF hpure =>
    subst hh
    exact fun r ↦ WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp
      (isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine ι v hv F hF w hpure)
      (.of_locallyQuasiFinite c) r
  | openClosed j i hij h F _ _ ihU ihZ =>
    intro _ _ _ r
    obtain ⟨S', hS', ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
      WeilSheaf.exists_exact_higherLowerShriek_of_openClosed (f := h) hij F r
    exact (WeilSheaf.IsMixedOfWeightsAtMost.of_exact hS' ((ihU r).of_iso e₁.symm)
      ((ihZ r).of_iso e₃.symm)).of_iso e₂

end Stratification

variable {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (S ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))]

variable (S) in
/-- For the projection `p : 𝔸¹_S ⟶ S` of the relative affine line over a separated `k₀`-scheme
of finite type and a Weil sheaf `F` on `𝔸¹_S` mixed of weights at most `w`, the sheaf `Rʳp₀!F` is
mixed of weights at most `w + r`, for every `r` (blueprint: `proposition-relative-affine-line--1`,
sheaf form).

The weight filtration of `F` and the long exact sequences of `Rp₀!` reduce to a punctually pure
graded piece, which has a relative-line stratification
(`WeilSheaf.IsPunctuallyPureOfWeight.hasRelativeLineStratification`). -/
theorem hasDirectImageWeightBound_affineLine :
    HasDirectImageWeightBound k₀ ι (𝔸(PUnit.{u + 1}; S) ↘ S) := by
  intro w F hF r
  obtain ⟨n, G, φ, h0, hlast, hmono, hpure⟩ := hF
  -- Induction along the filtration, whose successive quotients are punctually pure.
  have key : ∀ (i : ℕ) (hi : i < n + 1) (r : ℕ),
      ((WeilSheaf.higherLowerShriek k₀ l (𝔸(PUnit.{u + 1}; S) ↘ S) r).obj
        (G ⟨i, hi⟩)).IsMixedOfWeightsAtMost ι (w + r) := by
    intro i
    induction i with
    | zero =>
      exact fun _ r ↦ WeilSheaf.isMixedOfWeightsAtMost_of_isZero (Functor.map_isZero _ h0) _
    | succ i ih =>
      intro hi
      have := hmono ⟨i, by omega⟩
      obtain ⟨v, hv, hvpure⟩ := hpure ⟨i, by omega⟩
      exact WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_of_shortExact _
        (.mk' (ShortComplex.cokernelSequence_exact (φ ⟨i, by omega⟩)) this inferInstance)
        (ih (by omega)) fun r ↦
          (hvpure.hasRelativeLineStratification.isMixedOfWeightsAtMost r).mono_weight
            (by linarith)
  exact (key n (by omega) r).of_iso ((WeilSheaf.higherLowerShriek k₀ l _ r).mapIso hlast.some)

variable (S) in
/-- For the projection `p : 𝔸¹_S ⟶ S` of the relative affine line over a separated `k₀`-scheme
of finite type and a Weil complex `K` on `𝔸¹_S` mixed of weights at most `w`, the complex `Rp₀!K`
is mixed of weights at most `w` (blueprint: `proposition-relative-affine-line--1`).

By `lemma-finite-quasi-finite-direct-images--2` this follows from the sheaf form
`AlgebraicGeometry.hasDirectImageWeightBound_affineLine`. -/
theorem hasDirectImageComplexWeightBound_affineLine :
    HasDirectImageComplexWeightBound k₀ ι (𝔸(PUnit.{u + 1}; S) ↘ S) :=
  fun _ _ hK ↦ (hasDirectImageWeightBound_affineLine S).isMixedOfWeightsAtMost_derivedLowerShriek hK

variable (S) in
/-- The direct-image weight assertion holds for the projection of the `r`-fold relative affine line
over a separated `k₀`-scheme of finite type, the composition of `r` affine-line projections
(blueprint: `proposition-relative-affine-line--1` and `theorem-direct-image-mixed-sheaf--1`). -/
theorem hasDirectImageWeightBound_iteratedAffineLineProj :
    ∀ (r : ℕ) [(iteratedAffineLine S r).Over (Spec (CommRingCat.of k₀))]
      [(iteratedAffineLineProj S r).IsOver (Spec (CommRingCat.of k₀))],
      HasDirectImageWeightBound k₀ ι (iteratedAffineLineProj S r)
  | 0, _, _ =>
    have : LocallyQuasiFinite (iteratedAffineLineProj S 0) :=
      inferInstanceAs (LocallyQuasiFinite (𝟙 S))
    have : LocallyOfFiniteType (iteratedAffineLine S 0 ↘ Spec (CommRingCat.of k₀)) := by
      rw [← CategoryTheory.comp_over (iteratedAffineLineProj S 0) (Spec (CommRingCat.of k₀))]
      infer_instance
    .of_locallyQuasiFinite (iteratedAffineLineProj S 0)
  | r + 1, ⟨hom⟩, h => by
    -- `iteratedAffineLine S (r + 1)` is the affine line over `iteratedAffineLine S r`, with the
    -- structure morphism through `iteratedAffineLineProj S r`.
    let : (iteratedAffineLine S r).Over (Spec (CommRingCat.of k₀)) :=
      ⟨iteratedAffineLineProj S r ≫ S ↘ Spec (CommRingCat.of k₀)⟩
    have : (iteratedAffineLineProj S r).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : IsSeparated (iteratedAffineLine S r ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (IsSeparated (iteratedAffineLineProj S r ≫ _))
    have : LocallyOfFiniteType (iteratedAffineLine S r ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (LocallyOfFiniteType (iteratedAffineLineProj S r ≫ _))
    have : QuasiCompact (iteratedAffineLine S r ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (QuasiCompact (iteratedAffineLineProj S r ≫ _))
    have H := (hasDirectImageWeightBound_affineLine (ι := ι) (iteratedAffineLine S r)).comp
      (hasDirectImageWeightBound_iteratedAffineLineProj r)
    obtain rfl : hom = iteratedAffineLineProj S (r + 1) ≫ S ↘ Spec (CommRingCat.of k₀) :=
      h.1.symm
    simpa [iteratedAffineLineProj_succ] using H

end AlgebraicGeometry
