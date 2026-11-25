/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineIrreducible
public import WeilConjectures.DeligneLaumon.AffineLine.DegreeOne
public import WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents
public import WeilConjectures.DeligneLaumon.AffineLine.UpperReduction

/-!
# The Deligne–Laumon estimate on the affine line

Let `j : U₀ ↪ 𝔸¹_{𝔽_q}` be a dense open immersion and `F` a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every `r`.

The endpoint lemmas of `WeilConjectures.WeilSheaf.CurveEndpoints` settle every degree
except one: degree zero vanishes and degree two is pure of weight `w + 2`. For degree one,
choose a finite composition filtration of the Weil representation of `F`; its lisse irreducible
factors are still pure of weight `w`, their stalk spectra being subquotient spectra, and still
unramified at infinity. A geometrically constant factor extends constantly to the whole line
and has `H_c^1 = 0` because `RΓ_c(𝔸¹, ℚ̄_ℓ) = ℚ̄_ℓ(-1)[-2]`; every other factor is covered by
`AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one`. Each filtration step
stays short exact after `j_*` by `AlgebraicGeometry.shortExact_map_directImage`, so the long
exact sequence gives an exact triple in degree one whose middle term inherits the common upper
bound, characteristic polynomials being multiplicative in short exact sequences of Frobenius
modules. Induction through the filtration finishes the proof.

The blueprint proof opens with two further steps: a base change to a finite constant extension
`𝔽_{q^m}` and a reduction to geometrically irreducible graded pieces. They are not needed here,
and no statement of this block corresponds to them: the Fourier route of
`proposition-fourier-transform-middle-extension` only assumes arithmetic irreducibility, so the
composition filtration of the Weil representation over `k₀` is already fine enough, and neither the
filtration nor a semisimplicity theorem for pure sheaves is used.

## Main statements

In the namespace `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`:

- `hasWeightsAtMost_compactlySupportedCohomology_directImage`: the affine-line estimate.
- `subsingleton_compactlySupportedCohomology_directImage_zero` and
  `isPureOfWeightOver_compactlySupportedCohomology_directImage_two`: the two sharper endpoint
  assertions on the line.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The datum `D` with another lisse sheaf `G` on `U₀` is unramified at infinity if and only if
`G` is. -/
theorem isUnramifiedAtInfinity_withSheaf_iff (D : LisseOnDenseOpen k₀ l)
    (G : WeilSheaf k₀ l D.U) (hG : G.IsLisse) :
    (D.withSheaf G hG).IsUnramifiedAtInfinity ↔ G.IsUnramifiedAtInfinity D.j :=
  Iff.rfl

/-- Degree one of the affine-line estimate, for a sheaf `F ≅ j'^* G` restricted from a lisse
sheaf `G` on an open `W ⊆ ℙ¹` containing `∞`, along the open immersion `j' : U₀ ⟶ W`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_of_iso_upperStar
    (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l)
    (W : (ProjectiveLine (Spec (CommRingCat.of k₀))).Opens)
    (hW : ProjectiveLine.affineChart (Spec (CommRingCat.of k₀)) ⁻¹ᵁ W = D.j.opensRange)
    (hWtop : (ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))).opensRange ⊔ W = ⊤)
    (j' : D.U ⟶ W) [j'.IsOver (Spec (CommRingCat.of k₀))]
    (hj' : j' ≫ W.ι = D.j ≫ ProjectiveLine.affineChart (Spec (CommRingCat.of k₀)))
    (G : WeilSheaf k₀ l W) (hG : G.IsLisse) (e : (upperStar j').obj G ≅ D.sheaf) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  obtain ⟨ψ, hψ⟩ := AddChar.exists_ne_one_of_isAlgClosed k₀ (PadicAlgCl l) (by
    rw [ringChar.eq_zero]
    exact (CharP.ringChar_ne_zero_of_finite k₀).symm)
  have : IsOpenImmersion j' := by
    have : IsOpenImmersion (j' ≫ W.ι) := hj' ▸ inferInstance
    exact IsOpenImmersion.of_comp j' W.ι
  have : Nonempty D.U := by
    have : Nonempty (affineLine k₀) := ⟨affineLine.origin k₀⟩
    exact (D.isDominant.denseRange.nonempty_iff).2 inferInstance
  have hWne : (W : Set (ProjectiveLine (Spec (CommRingCat.of k₀)))).Nonempty :=
    ⟨_, (j' (Classical.arbitrary D.U)).2⟩
  have : GeometricallyIrreducible (W.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← Scheme.Opens.ι_comp_over]
    exact ProjectiveLine.geometricallyIrreducible_opens k₀ W hWne
  have : IrreducibleSpace (W.toScheme ↘ Spec (CommRingCat.of k₀)).geometricFiber := by
    rw [← Scheme.Opens.ι_comp_over]
    exact ProjectiveLine.irreducibleSpace_geometricFiber_opens k₀ W hWne
  have : GeometricallyConnected (W.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  have : SmoothOfRelativeDimension 1 (W.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← Scheme.Opens.ι_comp_over, ← zero_add (1 : ℕ)]
    infer_instance
  have := SmoothOfRelativeDimension.smooth 1 (W.toScheme ↘ Spec (CommRingCat.of k₀))
  -- `W` is quasi-compact, as an open of the noetherian scheme `ℙ¹`
  have : IsLocallyNoetherian (ProjectiveLine (Spec (CommRingCat.of k₀))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀))
  have : QuasiCompact (W.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← Scheme.Opens.ι_comp_over]
    infer_instance
  have : IrreducibleSpace W := GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    (f := W.toScheme ↘ Spec (CommRingCat.of k₀))
  have : IsDominant j' := ⟨j'.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : LocallyOfFiniteType (D.U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over D.j]
    infer_instance
  have : QuasiCompact (D.U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over D.j]
    infer_instance
  have : GeometricallyIrreducible (D.U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j']
    infer_instance
  have : GeometricallyConnected (D.U ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  have := connectedSpace_geometricFiber (k₀ := k₀) (Y := D.U)
  refine hasWeightsAtMostOver_compactlySupportedCohomology_one_of_upperStar ι D j' ?_ G hG e hw
  intro M hM hMw
  have hN := hM.upperStar_of_isDominant j'
  by_cases hc : ((upperStar j').obj M).IsGeometricallyConstant
  · obtain ⟨b, ⟨e'⟩⟩ := exists_iso_constantTwist_of_isGeometricallyConstant hN hc
    have : Subsingleton ((D.withSheaf ((upperStar j').obj M) (ProEtale.IsAdicLisseSheaf.upperStar _
        hM.1)).directImage.compactlySupportedCohomology 1).carrier :=
      LisseOnDenseOpen.subsingleton_compactlySupportedCohomology_one_of_iso_constantTwist
        (D.withSheaf ((upperStar j').obj M) (ProEtale.IsAdicLisseSheaf.upperStar _ hM.1)) e'
    exact FrobeniusModule.hasWeightsAtMost_of_subsingleton _ _ _
  · -- state the condition at infinity over `D.U`, where all terms agree syntactically
    have hinfM : ((upperStar j').obj M).IsUnramifiedAtInfinity D.j :=
      ⟨W, hW, hWtop, M, hM.1, ⟨(upperStarCongr (by
        rw [← cancel_mono W.ι, IsOpenImmersion.lift_fac, hj'])).app M⟩⟩
    exact hasWeightsAtMost_compactlySupportedCohomology_one_of_isUnramifiedAtInfinity ψ ι hψ
      (D.withSheaf ((upperStar j').obj M) (ProEtale.IsAdicLisseSheaf.upperStar _ hM.1)) hN
      ((isUnramifiedAtInfinity_withSheaf_iff _ _ _).2 hinfM) hc hMw

/-- **Degree one of the affine-line estimate.** If `F` is lisse on the dense open `U₀ ⊆ 𝔸¹`,
punctually `ι`-pure of weight `w` and unramified at infinity, then `H_c^1(𝔸¹, j_*F)` has weights
at most `w + 1`. Write `F ≅ j'^* G` for a lisse `G` on an open `W ⊆ ℙ¹` containing `∞`; by
`hasWeightsAtMostOver_compactlySupportedCohomology_one_of_upperStar` it suffices to treat
`N = j'^* M` for `M` irreducible lisse on `W`. Such an `N` is irreducible and unramified at
infinity; it is either geometrically constant, hence a constant twist with `H_c^1 = 0`, or it is
covered by `hasWeightsAtMost_compactlySupportedCohomology_one_of_isUnramifiedAtInfinity`.
(blueprint: `theorem-weight-bound-affine-line`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) (hinf : D.IsUnramifiedAtInfinity) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  obtain ⟨W, hW, hWtop, G, hG, ⟨e⟩⟩ := hinf
  -- `upperStarCongr` with a postponed proof makes the kernel compare syntactically equal pullbacks
  exact hasWeightsAtMostOver_compactlySupportedCohomology_one_of_iso_upperStar ι D W hW hWtop _
    (IsOpenImmersion.lift_fac _ _ _) G hG ((upperStarCongr (by rfl)).app G ≪≫ e) hw

/-- Let `j : U₀ ↪ 𝔸¹_{k₀}` be a dense open immersion and let `F` be a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every integer `r`. (blueprint: `theorem-weight-bound-affine-line`) -/
theorem hasWeightsAtMost_compactlySupportedCohomology_directImage (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) (hinf : D.IsUnramifiedAtInfinity) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (D.directImage.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  rcases lt_trichotomy r 1 with hr | rfl | hr
  · rcases (by omega : r < 0 ∨ r = 0) with hr | rfl
    · have : Subsingleton (D.directImage.compactlySupportedCohomology r).carrier :=
        subsingleton_compactlySupportedCohomology_directImage D.j D.sheaf D.lisse
        (Or.inl hr)
      exact FrobeniusModule.hasWeightsAtMost_of_subsingleton _ _ _
    · have : Subsingleton (D.directImage.compactlySupportedCohomology 0).carrier :=
        AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero D.j D.sheaf
          D.lisse
      exact FrobeniusModule.hasWeightsAtMost_of_subsingleton _ _ _
  · exact_mod_cast D.hasWeightsAtMostOver_compactlySupportedCohomology_one ι hinf hw
  · rcases (by omega : 2 < r ∨ r = 2) with hr | rfl
    · have : Subsingleton (D.directImage.compactlySupportedCohomology r).carrier :=
        subsingleton_compactlySupportedCohomology_directImage D.j D.sheaf D.lisse
        (Or.inr hr)
      exact FrobeniusModule.hasWeightsAtMost_of_subsingleton _ _ _
    · exact_mod_cast
        (AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two
          D.j D.sheaf ι D.lisse hw).hasWeightsAtMostOver

/-- In degree zero the compactly supported cohomology of `j_*F` on the line vanishes.
(blueprint: `theorem-weight-bound-affine-line`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero
    (D : LisseOnDenseOpen k₀ l) :
    Subsingleton (D.directImage.compactlySupportedCohomology 0).carrier := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  exact AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero D.j D.sheaf
    D.lisse

/-- In degree two the compactly supported cohomology of `j_*F` on the line is pure of weight
`w + 2`, not merely of weights at most `w + 2`. (blueprint: `theorem-weight-bound-affine-line`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  exact AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two D.j
    D.sheaf ι D.lisse hw

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
