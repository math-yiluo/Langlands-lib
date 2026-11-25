/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.FourierWeight
public import WeilConjectures.WeilSheaf.CohomologyShift
public import WeilConjectures.WeilSheaf.FourierStalk

/-!
# The degree-one estimate for an irreducible factor

Semicontinuity bounds the weights of `j'_*M'` by `v ≤ w + 1` even at the singular points of
the dual line. At the origin the Fourier kernel is trivial, so the stalk formula, taking both
shifts into account, gives

`(FT_ψ(j_*M[1]))_0̄ ≃ RΓ_c(A, j_*M)[2]` and `(j'_*M')_0̄ ≃ H_c^1(A, j_*M)`,

Frobenius-equivariantly. Hence `H_c^1(A, j_*M)` has weights at most `w + 1`. By the
nonexceptionality test `AlgebraicGeometry.isNonexceptional_of_isUnramifiedAtInfinity` the same
bound holds for every irreducible, non-geometrically-constant `M` unramified at infinity.

## Main definitions

- `AlgebraicGeometry.affineLine.origin`: the origin of the affine line, as a closed point.

## Main statements

- `AlgebraicGeometry.nonempty_equiv_stalk_homologySheaf_fourierTransform_origin`: the stalk of
  `FT_ψ(K)` at the origin of the dual line is `RΓ_c(A, K)[1]`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMost_directImage`: boundary
  semicontinuity of weights for the direct image `j_*M` on the affine line.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_equiv_stalk_origin_of_isFourierPartner`:
  the stationary-phase identification `H_c^1(A, j_*M) ≃ (j'_*M')_{0'}` and the vanishing of
  `H_c^2(A, j_*M)`.
- `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one`: the degree-one bound
  for an irreducible nonexceptional sheaf pure of weight `w`, and
  `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one_of_isUnramifiedAtInfinity`
  for an irreducible sheaf unramified at infinity and not geometrically constant.

## Implementation notes

The degree-one bound is derived along the blueprint argument from the boundary semicontinuity
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMost_directImage` and the stationary
phase
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_equiv_stalk_origin_of_isFourierPartner`.
The boundary semicontinuity is the case of the affine line of
`AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The origin `0` of the affine line `𝔸¹_{k₀}`, as a closed point: the image of the
`k₀`-rational point `x = 0`. -/
noncomputable def affineLine.origin (k₀ : Type u) [Field k₀] [Finite k₀] :
    (affineLine k₀).finitePoints :=
  ⟨(AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀))) 0).base
      (IsLocalRing.closedPoint k₀),
    Scheme.Hom.mem_finitePoints_of_comp_eq_id (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) _
      (AffineSpace.homOfVector_over _ _) _⟩

/-- The origin of the affine line is `k₀`-rational: its residue cardinality is `q = #k₀`. -/
theorem affineLine.residueCard_origin :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).residueCard (affineLine.origin k₀).1 =
      Nat.card k₀ := by
  rw [Scheme.Hom.residueCard]
  exact (congrArg (Nat.card k₀ ^ ·) (Scheme.Hom.degreeOver_eq_one_of_comp_eq_id _ _
    (AffineSpace.homOfVector_over (𝟙 _) 0) (IsLocalRing.closedPoint k₀))).trans (pow_one _)

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- **Stalk of the transform at the origin of the dual line.** At the origin `0'` the Fourier
kernel `ℒ_{ψ(x · 0)}` is constant, so the stalk formula identifies the fibre of `FT_ψ(K)` at
`0'` with `RΓ_c(𝔸¹, K)[1]`: in each degree `r`, the stalk of `𝓗^r FT_ψ(K)` at `0'` is
`H_c^{r+1}(𝔸¹ ⊗ k̄, K)`, Frobenius-equivariantly. (blueprint:
`proposition-base-change-fourier-inversion--3`) -/
theorem nonempty_equiv_stalk_homologySheaf_fourierTransform_origin
    (K : WeilComplex k₀ l (affineLine k₀)) (r : ℤ) :
    Nonempty ((((WeilComplex.homologySheaf r).obj ((fourierTransform ψ).obj K)).stalk
      (affineLine.origin k₀)).Equiv (K.compactlySupportedCohomology (r + 1))) := by
  have h0 : affineLine.origin k₀ = affineLine.rationalPoint k₀ 0 := by
    have : (fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom 0 :
        PUnit.{u + 1} → Γ(Spec (CommRingCat.of k₀), ⊤)) = 0 := funext fun _ ↦ map_zero _
    simp only [affineLine.origin, affineLine.rationalPoint, this]
  obtain ⟨E⟩ := nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint ψ K 0 r
  obtain ⟨e⟩ := nonempty_iso_artinSchreier_zero ψ
  rw [h0]
  exact ⟨E.trans (WeilComplex.compactlySupportedCohomologyEquivOfIso
    (WeilComplex.tensorLisseObjIsoOfIso _ _ e K) (r + 1))⟩

/-- **Stalk of the transform at the origin of the dual line**, for a middle extension: the
fibre of `FT_ψ((j_*M)[1])` at the origin has cohomology only in degrees `-1` and `0`, namely
`H_c^1(𝔸¹ ⊗ k̄, j_*M)` and `H_c^2(𝔸¹ ⊗ k̄, j_*M)`; the group `H_c^0` vanishes.
(blueprint: `proposition-base-change-fourier-inversion--3`) -/
theorem WeilSheaf.LisseOnDenseOpen.nonempty_equiv_stalk_fourierTransform_middleExtension_origin
    (D : WeilSheaf.LisseOnDenseOpen k₀ l) :
    Nonempty ((((WeilComplex.homologySheaf (-1)).obj
      ((fourierTransform ψ).obj D.middleExtension)).stalk (affineLine.origin k₀)).Equiv
        (D.directImage.compactlySupportedCohomology 1)) ∧
    Nonempty ((((WeilComplex.homologySheaf 0).obj
      ((fourierTransform ψ).obj D.middleExtension)).stalk (affineLine.origin k₀)).Equiv
        (D.directImage.compactlySupportedCohomology 2)) ∧
    ∀ r : ℤ, r ∉ ({-1, 0} : Set ℤ) → Subsingleton ((((WeilComplex.homologySheaf r).obj
      ((fourierTransform ψ).obj D.middleExtension)).stalk (affineLine.origin k₀)).carrier) := by
  -- `FT_ψ((j_*M)[1])_{0'}` in degree `r` is `H_c^{r+2}(𝔸¹ ⊗ k̄, j_*M)`
  have key (r n : ℤ) (h : r + 2 = n) :
      Nonempty ((((WeilComplex.homologySheaf r).obj
        ((fourierTransform ψ).obj D.middleExtension)).stalk (affineLine.origin k₀)).Equiv
          (D.directImage.compactlySupportedCohomology n)) := by
    obtain ⟨E⟩ := nonempty_equiv_stalk_homologySheaf_fourierTransform_origin ψ
      D.middleExtension r
    exact ⟨E.trans (WeilComplex.compactlySupportedCohomologyShiftEquiv _ 1 (r + 1) n
      (by omega))⟩
  refine ⟨key (-1) 1 (by norm_num), key 0 2 (by norm_num), fun r hr ↦ ?_⟩
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  obtain ⟨E⟩ := key r (r + 2) rfl
  have : Subsingleton (D.directImage.compactlySupportedCohomology (r + 2)).carrier := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
    rcases lt_trichotomy (r + 2) 0 with h | h | h
    · exact subsingleton_compactlySupportedCohomology_directImage D.j D.sheaf D.lisse
        (Or.inl h)
    · rw [h]
      exact subsingleton_compactlySupportedCohomology_directImage_zero D.j D.sheaf D.lisse
    · exact subsingleton_compactlySupportedCohomology_directImage D.j D.sheaf D.lisse
        (Or.inr (by omega))
  exact E.toLinearEquiv.toEquiv.subsingleton

namespace WeilSheaf.LisseOnDenseOpen

/-- *Boundary semicontinuity of weights* on the affine line: if the lisse sheaf `M` on the
dense open `U₀` has punctual weights at most `β`, then so has its direct image `j_*M` at every
closed point of the line, including the finitely many points outside `U₀`, where it may be
singular. This is the case of the affine line of
`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`.
(blueprint: `proposition-weights-j-boundary-points--1`) -/
theorem hasWeightsAtMost_directImage (D : LisseOnDenseOpen k₀ l) {ι : PadicAlgCl l →+* ℂ}
    {β : ℝ} (hβ : D.sheaf.HasWeightsAtMost ι β) : D.directImage.HasWeightsAtMost ι β := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  exact WeilSheaf.hasWeightsAtMost_directImage D.j ι D.lisse hβ

/-- *The origin fibre is the stationary-phase contribution.* If the Fourier transform of the
middle extension `(j_*M)[1]` is the middle extension `(j'_*M')[1]` of `D'`, then the fibre of
the transform at the origin `0'` of the dual line identifies `H_c^1(𝔸¹, j_*M)` with the stalk
`(j'_*M')_{0'}`, Frobenius-equivariantly: the geometric Frobenius of `k₀` on the left
corresponds to the local Frobenius `F_{0'}` at the `k₀`-rational point `0'` on the right.
Moreover `H_c^2(𝔸¹, j_*M) = 0`.

Indeed the fibre of `FT_ψ(K)` at `0'` is `RΓ_c(𝔸¹, K)[1]`, the kernel being trivial there, so
the fibre of `FT_ψ((j_*M)[1])` has `H_c^1` in degree `-1` and `H_c^2` in degree `0`, while the
fibre of `(j'_*M')[1]` is the stalk `(j'_*M')_{0'}` placed in degree `-1`.
(blueprint: `corollary-h-1-c-stalk-fourier`) -/
theorem nonempty_equiv_stalk_origin_of_isFourierPartner (ψ : AddChar k₀ (PadicAlgCl l))
    (D D' : LisseOnDenseOpen k₀ l) (hFT : D.IsFourierPartner ψ D') :
    Nonempty ((D.directImage.compactlySupportedCohomology 1).Equiv
        (D'.directImage.stalk (affineLine.origin k₀))) ∧
      Subsingleton (D.directImage.compactlySupportedCohomology 2).carrier := by
  obtain ⟨e⟩ := hFT
  -- the fibre of the transform at `0'` is `RΓ_c(𝔸¹, j_*M)[2]`
  obtain ⟨⟨e₁⟩, ⟨e₂⟩, -⟩ := D.nonempty_equiv_stalk_fourierTransform_middleExtension_origin ψ
  -- the fibre of `(j'_*M')[1]` is the stalk `(j'_*M')_{0'}` placed in degree `-1`
  obtain ⟨e₃⟩ := WeilSheaf.nonempty_equiv_stalk_of_iso
    ((WeilComplex.homologySheaf (-1)).mapIso e ≪≫
      D'.directImage.homologySheafShiftToComplexIso 1) (affineLine.origin k₀)
  refine ⟨⟨e₁.symm.trans e₃⟩, ?_⟩
  have h₀ : Limits.IsZero ((WeilComplex.homologySheaf 0).obj
      ((fourierTransform ψ).obj D.middleExtension)) :=
    (WeilSheaf.isZero_homologySheaf_shift_toComplex D'.directImage (n := 1) (a := 0)
      (by norm_num)).of_iso ((WeilComplex.homologySheaf 0).mapIso e)
  have := WeilSheaf.subsingleton_stalk_of_isZero h₀ (affineLine.origin k₀)
  exact e₂.symm.toLinearEquiv.toEquiv.subsingleton

end WeilSheaf.LisseOnDenseOpen

/-- If `M` is irreducible, nonexceptional for a nontrivial `ψ` and punctually `ι`-pure of
weight `w` on a dense open `U₀` of the affine line, then `H_c^1(A, j_*M)` has weights at most
`w + 1`. (blueprint: `corollary-h-1-c-stalk-fourier--3`) -/
theorem hasWeightsAtMost_compactlySupportedCohomology_one (ι : PadicAlgCl l →+* ℂ)
    (hψ : ψ ≠ 1) (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  -- Step 1: the transform of `(j_*M)[1]` is a middle extension `(j'_*M')[1]`
  obtain ⟨D', _, hFT⟩ := exists_middleExtension_fourierTransform ψ hψ D hD hne
  -- Step 2: `M'` is pure of a weight `v ≤ w + 1`
  obtain ⟨v, hv⟩ := exists_isPunctuallyPureOfWeight_of_isFourierPartner ψ ι hψ D D' hD hne hw hFT
  have hvw : v ≤ w + 1 := le_add_one_of_isFourierPartner ψ ι hψ D D' hD hne hw hFT hv
  -- Step 3: `j'_*M'` has weights at most `w + 1` on the whole dual line
  have hM' : D'.directImage.HasWeightsAtMost ι (w + 1) :=
    D'.hasWeightsAtMost_directImage (hv.hasWeightsAtMost.mono hvw)
  -- Step 4: the stationary-phase identification at the rational origin `0'`
  obtain ⟨⟨e⟩, -⟩ := D.nonempty_equiv_stalk_origin_of_isFourierPartner ψ D' hFT
  have h0 := hM' (affineLine.origin k₀)
  rw [affineLine.residueCard_origin] at h0
  exact h0.of_equiv e

/-- If `M` is irreducible, unramified at infinity, not geometrically constant and punctually
`ι`-pure of weight `w` on a dense open `U₀` of the affine line, then `H_c^1(A, j_*M)` has weights
at most `w + 1`: such an `M` is nonexceptional for every nontrivial `ψ`
(`AlgebraicGeometry.isNonexceptional_of_isUnramifiedAtInfinity`). (blueprint:
`corollary-h-1-c-stalk-fourier--3`) -/
theorem hasWeightsAtMost_compactlySupportedCohomology_one_of_isUnramifiedAtInfinity
    (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1) (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) (hinf : D.IsUnramifiedAtInfinity)
    (hconst : ¬ D.IsGeometricallyConstant) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) :=
  hasWeightsAtMost_compactlySupportedCohomology_one ψ ι hψ D hD
    (isNonexceptional_of_isUnramifiedAtInfinity ψ hψ D hD hinf hconst) hw

end AlgebraicGeometry
