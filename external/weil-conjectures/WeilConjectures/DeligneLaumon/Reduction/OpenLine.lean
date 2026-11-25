/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Curve.AffineCore
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineGeometricallyIrreducible
public import WeilConjectures.DeligneLaumon.AffineLine.Upper
public import WeilConjectures.DeligneLaumon.Reduction.AffineCurve
public import WeilConjectures.WeilSheaf.OpenImmersionRestriction
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The affine-line estimate on an open curve

For a nonempty open `C` of the projective line over `k₀` and a lisse Weil sheaf `F` punctually
pure of weight `w`, the compactly supported cohomology `H_c^r(C, F)` has weights at most `w + r`,
with no ramification condition at infinity (blueprint: `theorem-weight-bound-curve--2`). It is the
case `j = 𝟙` of the compact-support upper bound for a middle extension on a smooth geometrically
connected curve (blueprint: `theorem-weight-bound-curve--1`), the middle extension
`(𝟙)_* F` being `F` itself.

## Main statements

- `AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve`: blueprint
  `theorem-weight-bound-curve--2`.
- `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_of_projectiveLine`:
  blueprint `theorem-weight-bound-curve--2`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §3.
- [Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*][laumon1987], Publ. Math. IHÉS **65** (1987).
-/

@[expose] public section

universe u

open CategoryTheory

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (ι : PadicAlgCl l →+* ℂ)

/-- **Compact-support upper bound for a middle extension on a curve** (blueprint:
`theorem-weight-bound-curve--1`): let `j : U ⟶ C` be a dense open immersion of smooth
geometrically connected curves over `k₀` and let `F` be a lisse Weil sheaf on `U`, punctually
`ι`-pure of weight `w`. Then `H_c^r(C, j_*F)` has weights at most `w + r` for every `r`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_directImage_of_isCurve
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).HasWeightsAtMostOver
      k₀ ι (w + r) := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have := SmoothOfRelativeDimension.smooth 1 (U ↘ Spec (CommRingCat.of k₀))
  rcases lt_or_ge r 0 with hr | hr
  · -- `H_c^r` vanishes in negative degrees
    intro β hβ
    have :
        Subsingleton (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier :=
      WeilSheaf.subsingleton_globalSections_of_isZero
        (WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg
          (f := C ↘ Spec (CommRingCat.of k₀)) _ hr)
    obtain ⟨x, hx⟩ := hβ.exists_hasEigenvector
    exact (hx.2 (Subsingleton.elim _ _)).elim
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
  -- the boundary weights of `j_*F` and the purity of `j^*j_*F = F`
  have hK := WeilSheaf.IsLisse.hasWeightsAtMost_directImage j hj hF hw.hasWeightsAtMost
  obtain ⟨e⟩ := WeilSheaf.nonempty_upperStar_directImage_iso j F
  have hjK := hw.of_mono e.hom
  -- a nonempty affine open `V ⊆ U` of `C`; its complement is finite
  have : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  have : IsRegular C := IsRegular.of_smooth (C ↘ Spec (CommRingCat.of k₀))
  have : ConnectedSpace C :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C ↘ Spec (CommRingCat.of k₀))
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have hdim : topologicalKrullDim C = 1 :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq (C ↘ Spec (CommRingCat.of k₀)) 1).mp
      inferInstance
  have : CompactSpace C := (quasiCompact_iff_compactSpace (C ↘ Spec (CommRingCat.of k₀))).mp
    inferInstance
  have : IsNoetherian C := ⟨⟩
  obtain ⟨_, ⟨x, rfl⟩⟩ := hj.nonempty
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := j x) (U := j.opensRange)
    ⟨x, rfl⟩
  have hVfin : (V : Set C)ᶜ.Finite :=
    V.isOpen.finite_compl_of_topologicalKrullDim_le_one hdim.le ⟨_, hxV⟩
  obtain ⟨Z, _, i, _, _, hrange, _⟩ :=
    Scheme.Opens.exists_isClosedImmersion_isFinite_compl (k₀ := k₀) V hVfin
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i]
    infer_instance
  have : LocallyQuasiFinite (i ≫ C ↘ Spec (CommRingCat.of k₀)) := by
    rw [comp_over i]
    infer_instance
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := WeilSheaf.exists_exact_higherLowerShriek_of_openClosed
    (j := V.ι) (i := i) (f := C ↘ Spec (CommRingCat.of k₀))
    (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl) ((WeilSheaf.directImage j).obj F) n
  -- the open part: the affine-curve estimate on `V`, where `j_*F` restricts to `F|_V`
  have h₁ : S.X₁.HasWeightsAtMost ι (w + n) := by
    have : IsAffine V := hV
    have := V.isSeparated (k₀ := k₀)
    have := V.locallyOfFiniteType (k₀ := k₀)
    have : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over V.ι]
      infer_instance
    have : SmoothOfRelativeDimension 1 (V.toScheme ↘ Spec (CommRingCat.of k₀)) :=
      V.smoothOfRelativeDimension_one (k₀ := k₀)
    have hr : Set.range V.ι ⊆ Set.range j := by
      rw [Scheme.Opens.range_ι]
      exact hVU
    let v : V.toScheme ⟶ U := IsOpenImmersion.lift j V.ι hr
    have hv : v ≫ j = V.ι := IsOpenImmersion.lift_fac _ _ _
    have : v.IsOver (Spec (CommRingCat.of k₀)) := IsOpenImmersion.isOver_lift _ _ hr
    have hVK : ((WeilSheaf.upperStar V.ι).obj
        ((WeilSheaf.directImage j).obj F)).IsPunctuallyPureOfWeight ι w :=
      WeilSheaf.IsPunctuallyPureOfWeight.upperStar_of_comp_eq v j V.ι hv hjK
    have hVe := hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine ι
      (ringKrullDim_le_of_smoothOfRelativeDimension (V.toScheme ↘ Spec (CommRingCat.of k₀)) 1) _
      hVK n
    obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
      (V.ι ≫ C ↘ Spec (CommRingCat.of k₀))
      ((WeilSheaf.upperStar V.ι).obj ((WeilSheaf.directImage j).obj F)) n
    exact (WeilSheaf.hasWeightsAtMost_of_compactlySupportedCohomology_zero
      (FrobeniusModule.HasWeightsAtMost.of_equiv E hVe)).of_epi e₁.inv
  -- the closed part: the finite boundary, of weights at most `w`
  have h₃ : S.X₃.HasWeightsAtMost ι (w + n) := by
    refine WeilSheaf.HasWeightsAtMost.of_epi e₃.inv ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine (WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite _
        (hK.upperStar i)).mono ?_
      simp
    · exact (WeilSheaf.isPunctuallyPureOfWeight_of_isZero
        (isZero_higherLowerShriek_of_quasiFinite _ n hn _) _).hasWeightsAtMost
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
    (C ↘ Spec (CommRingCat.of k₀)) ((WeilSheaf.directImage j).obj F) n
  exact FrobeniusModule.HasWeightsAtMost.of_equiv E.symm
    ((WeilSheaf.HasWeightsAtMost.of_exact hS h₁ h₃).of_epi
      e₂.hom).compactlySupportedCohomology_zero

/-- **Compact-support upper bound on a curve.** Let `C` be a smooth geometrically connected curve
over `k₀` and let `F` be a lisse Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then every
`H_c^r(C, F)` has weights at most `w + r`: this is
`AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_directImage_of_isCurve` for
the identity of `C`, whose middle extension `(𝟙 C)_* F` is `F` itself
(blueprint: `theorem-weight-bound-curve--2`). -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l C) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w)
    (r : ℤ) :
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have h := hasWeightsAtMostOver_compactlySupportedCohomology_directImage_of_isCurve ι (𝟙 C)
    (by simp) F hF hw r
  obtain ⟨e⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_of_iso
    ((WeilSheaf.lowerStarIdIso k₀ l C).app F) r
  exact FrobeniusModule.HasWeightsAtMost.of_equiv e.symm h

/-- Let `C` be a nonempty open subscheme of the projective line `ℙ¹_{k₀}` and let `F` be a lisse
Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then the compactly supported cohomology
`H_c^r(C, F)` of the structure morphism

```
C --- c ---> ℙ¹_{k₀}
  \            |
   \           | ↘
    `--------> Spec k₀
```

has weights at most `w + r`, with no ramification restriction at the point at infinity
(blueprint: `theorem-weight-bound-curve--2`). -/
theorem hasWeightsAtMost_compactlySupportedCohomology_of_projectiveLine {C : Scheme.{u}}
    [Nonempty C] [C.Over (Spec (CommRingCat.of k₀))]
    (c : C ⟶ ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k₀))) [IsOpenImmersion c]
    [c.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l C) (hF : F.IsLisse) (w : ℝ) (hpure : F.IsPunctuallyPureOfWeight ι w)
    (r : ℤ) :
    -- `C ↘ Spec k₀` is separated and locally of finite type, being `c` followed by `ℙ¹ ↘ Spec k₀`
    haveI : IsSeparated (C ↘ Spec (CommRingCat.of k₀)) := by rw [← comp_over c]; infer_instance
    haveI : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over c]; infer_instance
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  -- `C` is a smooth geometrically connected curve over `k₀`, being a nonempty open of `ℙ¹_{k₀}`
  have hc := comp_over c (Spec (CommRingCat.of k₀))
  have : GeometricallyIrreducible (C ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    exact ProjectiveLine.geometricallyIrreducible_of_isOpenImmersion c
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀)) := by
    rw [← hc]
    exact ProjectiveLine.smoothOfRelativeDimension_one_of_isOpenImmersion c
  have : IsSeparated (C ↘ Spec (CommRingCat.of k₀)) := by rw [← hc]; infer_instance
  exact hasWeightsAtMostOver_compactlySupportedCohomology_of_isCurve ι F hF hpure r

end AlgebraicGeometry
