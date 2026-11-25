/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Etale.Field
public import WeilConjectures.DeligneLaumon.Reduction.TraceReality
public import WeilConjectures.DeligneLaumon.Reduction.AffineCurve
public import WeilConjectures.DeligneLaumon.Reduction.RealSheaves
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology

/-!
# Weight bounds for direct images from an open of the relative affine line

The main statement of this file is the geometric input of the Deligne–Laumon reduction in
general: for the projection `h : U ⟶ Y` of
an open `U` of the relative affine line `𝔸¹_Y` with surjective projection, and `F` lisse and
punctually pure of weight `w`, the sheaf `Rʳh₀!F` is mixed of weights at most `w + r`.

The open-curve estimate (`WeilConjectures.DeligneLaumon.Reduction.OpenLine`) is a *punctual*
upper bound on Frobenius eigenvalues (`FrobeniusModule.HasWeightsAtMostOver`), not mixedness;
this file upgrades it to mixedness, and the reality argument it runs is exactly what that
upgrade costs.

## Conventions

We use the relative affine space `AlgebraicGeometry.AffineSpace` of mathlib and the relative
projective space `AlgebraicGeometry.ProjectiveSpace` of this repository, whose index types record
the coordinates: `𝔸(PUnit; Y)` is the relative affine line — the same spelling as
`AlgebraicGeometry.affineLine` — and `ℙ(ULift (Fin 2); S)` the relative projective line.

## Implementation notes

- For `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine`: the projection
  `h : U ⟶ Y` is smooth of relative dimension one with affine fibres
  (`AlgebraicGeometry.AffineSpace.isAffine_fiber_of_isOpenImmersion`), so the relative-curve step
  `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber` applies. That
  step follows Kiehl–Weissauer I.7: compact-support base change and the curve estimate give the
  punctual bound on every fibre; the direct images of the real envelope `F⁰ ⊕ (F⁰)^∨` have
  reduced local `L`-fractions with real numerator and denominator, so they are `ι`-real and
  `AlgebraicGeometry.WeilSheaf.IsReal.isMixed` applies; the direct image of `F` is a twisted
  direct summand, hence mixed, and the punctual bound cuts its weights down to `w + r`.

## Main statements

- `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine`:
  purity of `H_c^2` of a pure lisse sheaf on a smooth affine curve.
- `AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber`: the punctual
  weight bound `w + i` on the stalks of `Rⁱh₀!F` over a relative affine curve.
- `AlgebraicGeometry.isReal_higherLowerShriek_of_isAffine_fiber`: the direct images of a real
  lisse sheaf over a relative affine curve are real.
- `AlgebraicGeometry.exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber`:
  mixedness of the direct images over a relative affine curve.
- `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber`: the direct
  images over a relative affine curve are mixed of weights at most `w + i`.
- `AlgebraicGeometry.isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine`: the same for an
  open of the relative affine line with surjective projection.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §3.
- [Kiehl, Weissauer, *Weil conjectures, perverse sheaves and l-adic Fourier
  transform*][kiehlWeissauer2001], Springer (2001), I.7.
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

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The constant twist `F ↦ F ⊗ 𝓑_b` by a unit `b ∈ ℚ̄_ℓˣ`, as an endofunctor of Weil sheaves:
the twist of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.constantTwist`), which
keeps the underlying sheaf, restricted to Weil sheaves. -/
noncomputable def constantTwistFunctor (b : (PadicAlgCl l)ˣ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l X :=
  (objectProperty k₀ l X).liftFullSubcategory (objectProperty k₀ l X)
    (ProEtaleWeilSheaf.constantTwist k₀ l X b) fun _ hK ↦ hK

instance (b : (PadicAlgCl l)ˣ) : (constantTwistFunctor k₀ l X b).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

instance (b : (PadicAlgCl l)ˣ) : Limits.PreservesFiniteLimits (constantTwistFunctor k₀ l X b) :=
  preservesFiniteLimits_of_comp_ι _ (ProEtaleWeilSheaf.constantTwist k₀ l X b)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _)

instance (b : (PadicAlgCl l)ˣ) : Limits.PreservesFiniteColimits (constantTwistFunctor k₀ l X b) :=
  preservesFiniteColimits_of_comp_ι _ (ProEtaleWeilSheaf.constantTwist k₀ l X b)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _)

/-- The constant twist `F ⊗ 𝓑_b` of a Weil sheaf is the image of `F` under the constant twist
functor. -/
noncomputable def constantTwistIsoConstantTwistFunctorObj (F : WeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) : F.constantTwist b ≅ (constantTwistFunctor k₀ l X b).obj F :=
  ObjectProperty.isoMk _ (constantTwistObjIso F b)

variable {ι} in
/-- The constant twist `G ⊗ 𝓑_b` of a sheaf mixed of weights at most `v` is mixed of weights at
most `v + c`, where `2 log_q |ι b| = c`: tensoring a mixed filtration with the rank-one sheaf
`𝓑_b` is exact, and it multiplies the eigenvalues at a closed point of degree `m` by `bᵐ`, so it
raises every punctual weight by `c`. -/
theorem IsMixedOfWeightsAtMost.constantTwist {F : WeilSheaf k₀ l X} {w : ℝ}
    (h : F.IsMixedOfWeightsAtMost ι w) {b : (PadicAlgCl l)ˣ} {c : ℝ}
    (hb : 2 * Real.logb (Nat.card k₀) ‖ι b‖ = c) :
    (F.constantTwist b).IsMixedOfWeightsAtMost ι (w + c) :=
  (h.map_add (constantTwistFunctor k₀ l X b) c fun _ G hG ↦
    (hG.constantTwist hb).of_epi (constantTwistIsoConstantTwistFunctorObj G b).hom).of_iso
      (constantTwistIsoConstantTwistFunctorObj F b).symm

end WeilSheaf

/-- The spectrum `Spec κ(y)` of the residue field at a closed point `y` of a `k₀`-scheme is étale
over `k₀`: `κ(y)` is a finite extension of the perfect field `k₀`, hence separable. Thus the fibre
over `y` of a smooth relative curve over `Y` is a smooth curve over `k₀`. -/
theorem Scheme.etale_fromSpecResidueField_comp {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k₀)) (y : Y) (hy : y ∈ Y.finitePoints) :
    Etale (Y.fromSpecResidueField y ≫ p) := by
  have : Finite (Y.residueField y) := hy
  rw [← Scheme.Hom.specMap_residueFieldAlgebraMap, HasRingHomProperty.Spec_iff (P := @Etale)]
  let := (p.residueFieldAlgebraMap y).toAlgebra
  rw [CommRingCat.hom_ofHom, ← RingHom.algebraMap_toAlgebra (p.residueFieldAlgebraMap y),
    RingHom.etale_algebraMap]
  have : Module.Finite k₀ (Y.residueField y) := Module.Finite.of_finite
  have : Algebra.FormallyEtale k₀ (Y.residueField y) := Algebra.FormallyEtale.of_isSeparable _ _
  exact ⟨‹_›, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

section RelativeCurve

/-! ### Relative affine curves

Throughout, `h : U ⟶ Y` is a smooth separated morphism of relative dimension one between
`k₀`-schemes of finite type, `Y` separated, whose fibres `h.fiber y` are affine: every nonempty
geometric fibre of `h` is a smooth affine curve. -/

variable {U Y : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (h : U ⟶ Y)
  [h.IsOver (Spec (CommRingCat.of k₀))] [SmoothOfRelativeDimension 1 h] [IsSeparated h]
  [QuasiCompact h]

/-- **The fibres of a relative affine curve.** For a closed point `y` of `Y`, the fibre
`X' = U ×_Y Spec κ(y)` of `h`, with its map `g : X' ⟶ U`, is a smooth affine curve over `k₀`, and
compact support base change identifies the local polynomials of the stalks of the `Rⁱh₀!F` at `y`
with those of the compactly supported cohomology of the fibre: with `d = [κ(y) : k₀]`,

`det (1 - T^d F_y ∣ (Rⁱh₀!F)_ȳ) = det (1 - T F ∣ H_c^i(X' ⊗ k̄, g^*F))`. -/
theorem exists_fiber_charpolyRev_higherLowerShriek (hfib : ∀ y, IsAffine (h.fiber y))
    (y : Y.finitePoints) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ∃ (X' : Scheme.{u}) (_ : X'.Over (Spec (CommRingCat.of k₀))) (g : X' ⟶ U)
      (_ : g.IsOver (Spec (CommRingCat.of k₀))) (_ : IsAffine X')
      (_ : SmoothOfRelativeDimension 1 (X' ↘ Spec (CommRingCat.of k₀)))
      (_ : IsSeparated (X' ↘ Spec (CommRingCat.of k₀)))
      (_ : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)))
      (_ : QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))),
      ringKrullDim Γ(X', ⊤) ≤ 1 ∧ ∀ (F : WeilSheaf k₀ l U) (i : ℕ),
        Polynomial.expand _ ((Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1)
          (((WeilSheaf.higherLowerShriek k₀ l h i).obj F).stalk y).frobeniusEnd.charpolyRev =
        (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology
          i).frobeniusEnd.charpolyRev := by
  have := SmoothOfRelativeDimension.smooth 1 h
  -- the closed point `y`, as the spectrum of its residue field, a finite extension of `k₀`
  let Z : Scheme.{u} := Spec (Y.residueField y.1)
  let t : Z ⟶ Y := Y.fromSpecResidueField y.1
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨t ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : t.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : Finite (Y.residueField y.1) := y.2
  have hfin : IsFinite (t ≫ Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← Scheme.Hom.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff]
    let := ((Y ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap y.1).toAlgebra
    exact Module.Finite.of_finite
  have : IsFinite (Z ↘ Spec (CommRingCat.of k₀)) := hfin
  have : Etale (Z ↘ Spec (CommRingCat.of k₀)) :=
    Scheme.etale_fromSpecResidueField_comp (Y ↘ Spec (CommRingCat.of k₀)) y.1 y.2
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over h (Spec (CommRingCat.of k₀))]
    infer_instance
  -- the fibre `X' = U ×_Y Spec κ(y)`, a smooth affine curve over `k₀`
  obtain ⟨X', g, f', hH, hX'⟩ : ∃ (X' : Scheme.{u}) (g : X' ⟶ U) (f' : X' ⟶ Z),
      IsPullback g f' h t ∧ IsAffine X' :=
    ⟨_, _, _, IsPullback.of_hasPullback h t, hfib y.1⟩
  -- the instance must be named and passed explicitly below: an `inferInstance` in the
  -- witness makes the kernel unfold the cohomology instead of `inferInstance`
  let instX : X'.Over (Spec (CommRingCat.of k₀)) := ⟨g ≫ U ↘ Spec (CommRingCat.of k₀)⟩
  have : g.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hf' : f' ≫ t ≫ Y ↘ Spec (CommRingCat.of k₀) = g ≫ U ↘ Spec (CommRingCat.of k₀) := by
    rw [← Category.assoc, ← hH.w, Category.assoc, comp_over]
  have : f'.IsOver (Spec (CommRingCat.of k₀)) := ⟨hf'⟩
  have : IsSeparated f' := MorphismProperty.of_isPullback hH ‹_›
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hH inferInstance
  have : QuasiCompact f' := MorphismProperty.of_isPullback hH ‹_›
  have : SmoothOfRelativeDimension 1 f' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hH ‹_›
  have hX : X' ↘ Spec (CommRingCat.of k₀) = f' ≫ Z ↘ Spec (CommRingCat.of k₀) :=
    (comp_over f' _).symm
  have hsm : SmoothOfRelativeDimension 1 (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [hX]
    exact inferInstanceAs (SmoothOfRelativeDimension (1 + 0) _)
  have : IsSeparated (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [hX]
    infer_instance
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [hX]
    infer_instance
  have : QuasiCompact (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [hX]
    infer_instance
  refine ⟨X', instX, g, ‹_›, hX', hsm, ‹_›, ‹_›, ‹_›,
    ringKrullDim_le_of_smoothOfRelativeDimension (X' ↘ Spec (CommRingCat.of k₀)) 1,
    fun F i ↦ ?_⟩
  -- compact support base change
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_fiber hH F i
  -- the degree `d` of `y` and the unique point `z₀` of `Z`
  set d := (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 with hd_def
  have hd : d ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ y.2
  let z₀ : Z := IsLocalRing.closedPoint (Y.residueField y.1)
  have hiz (z : Z) : t.base z = y.1 := Scheme.fromSpecResidueField_apply _ _
  have (z : Z) : IsIso (t.residueFieldMap z) := Scheme.Hom.isIso_residueFieldMap t z
  have hz₀ : z₀ ∈ Z.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso t z₀).1 ((hiz z₀).symm ▸ y.2)
  have hdegZ (z : Z) : (Z ↘ Spec (CommRingCat.of k₀)).degreeOver z = d :=
    (Scheme.Hom.degreeOver_comp_of_isIso t (Y ↘ Spec (CommRingCat.of k₀)) z).trans
      (congrArg _ (hiz z))
  have hy : (⟨t.base z₀, Scheme.Hom.map_mem_finitePoints t hz₀⟩ : Y.finitePoints) = y :=
    Subtype.ext (hiz z₀)
  -- `H_c^0` of the point `Spec κ(y)`
  have hZ : (((WeilSheaf.upperStar t).obj ((WeilSheaf.higherLowerShriek k₀ l h i).obj
      F)).compactlySupportedCohomology 0).frobeniusEnd.charpolyRev = Polynomial.expand _ d
        (((WeilSheaf.higherLowerShriek k₀ l h i).obj F).stalk y).frobeniusEnd.charpolyRev := by
    rw [WeilSheaf.charpolyRev_compactlySupportedCohomology_zero_of_subsingleton _ ⟨z₀, hz₀⟩,
      hdegZ, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def,
      WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar, hy, hdegZ, hiz, ← hd_def,
      Nat.div_self (Nat.pos_of_ne_zero hd), pow_one]
  have hE := E.localPolynomial_eq
  rw [FrobeniusModule.localPolynomial, FrobeniusModule.localPolynomial] at hE
  exact hZ.symm.trans hE

-- the lissity of `F` is not needed: the curve estimate holds for every punctually pure sheaf
set_option linter.unusedVariables false in
/-- **Punctual upper bound in a relative affine curve.** Let `h : U ⟶ Y` be a smooth separated
morphism of relative dimension one with affine fibres, and let `F` be a lisse Weil sheaf on `U`,
punctually `ι`-pure of weight `w`. Then `Rⁱh₀!F` has weights at most `w + i`: by compactly
supported base change its stalk at a closed point `y` is `H_c^i(U_ȳ, F)`, the restriction of
`F` to the fibre is pure of weight `w` relative to `κ(y)`
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.upperStar`), and the curve estimate
applies to each geometric component of the affine fibre. -/
theorem hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber
    (hfib : ∀ y, IsAffine (h.fiber y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ((WeilSheaf.higherLowerShriek k₀ l h i).obj F).HasWeightsAtMost ι (w + i) := by
  have := SmoothOfRelativeDimension.smooth 1 h
  intro y γ hγ
  obtain ⟨X', _, g, _, _, _, _, _, _, hdim, hcp⟩ :=
    exists_fiber_charpolyRev_higherLowerShriek (k₀ := k₀) (l := l) h hfib y
  -- the curve estimate on the fibre
  have hw' := hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine ι hdim
    ((WeilSheaf.upperStar g).obj F) (hw.upperStar g) i
  -- every eigenvalue at `y` is the `d`-th power of one on `H_c^i` of the fibre
  have hd := Scheme.Hom.degreeOver_ne_zero (Y ↘ Spec (CommRingCat.of k₀)) y.2
  obtain ⟨β, hβ, rfl⟩ := LinearMap.exists_hasEigenvalue_pow_eq_of_charpolyRev_eq_expand _ _ hd
    (hcp F i).symm hγ (FrobeniusModule.ne_zero_of_hasEigenvalue hγ)
  rw [Scheme.Hom.residueCard, map_pow, norm_pow, Nat.cast_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
  have := hw' β hβ
  rwa [Int.cast_natCast] at this

/-- **Reality of the relative factors of an envelope.** Let `h : U ⟶ Y` be as in
`AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber` and let `E` be a lisse
`ι`-real Weil sheaf on `U`, punctually `ι`-pure of weight `0`. Then every `Rⁱh₀!E` is `ι`-real.
At a closed point `y` the trace formula writes the `L`-function of the fibre as `P₁ / P₂`, with
real coefficients since `E` is real; the reciprocal roots of `P₁` have modulus at most
`q_y ^ (1 / 2)` and those of `P₂` modulus `q_y`
(`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine`), so the
fraction is reduced (`Polynomial.isCoprime_of_norm_inv_roots`) and both factors are real
(`Polynomial.map_conj_eq_self_of_isCoprime`). -/
theorem isReal_higherLowerShriek_of_isAffine_fiber (hfib : ∀ y, IsAffine (h.fiber y))
    (E : WeilSheaf k₀ l U) (hE : E.IsLisse) (hreal : E.IsReal ι)
    (hpure : E.IsPunctuallyPureOfWeight ι 0) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ((WeilSheaf.higherLowerShriek k₀ l h i).obj E).IsReal ι := by
  have := SmoothOfRelativeDimension.smooth 1 h
  intro y
  obtain ⟨X', _, g, _, _, _, _, _, _, hdim, hcp⟩ :=
    exists_fiber_charpolyRev_higherLowerShriek (k₀ := k₀) (l := l) h hfib y
  set E' := (WeilSheaf.upperStar g).obj E
  have hE' : E'.IsLisse := WeilSheaf.IsLisse.upperStar hE g
  -- the cohomology of the fibre: `H_c^0 = 0`, `H_c^1` of weights at most `1`, `H_c^2` pure of
  -- weight `2`, nothing outside degrees `0, 1, 2`
  have h0 := WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_isAffine E' hE'
  have h1 := hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine ι hdim E'
    (hpure.upperStar g) 1
  have h2 := isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine ι E' hE'
    (hpure.upperStar g)
  -- the traces of the powers of the local Frobenii of `E'` are real, since `E` is real
  have hloc (x : X'.finitePoints) (n : ℕ) :
      (starRingEnd ℂ) (ι (LinearMap.trace _ _ ((E'.stalk x).frobeniusEnd ^ n))) =
        ι (LinearMap.trace _ _ ((E'.stalk x).frobeniusEnd ^ n)) := by
    exact (FrobeniusModule.isReal_iff_forall_trace_pow ι (E'.stalk x)).1
      (hreal.upperStar g x) n
  -- the trace formula: the alternating traces on the cohomology of the fibre are real
  have htr (m : ℕ) (hm : m ≠ 0) : (starRingEnd ℂ) (ι (LinearMap.trace _ _
      ((E'.compactlySupportedCohomology 2).frobeniusEnd ^ m) - LinearMap.trace _ _
      ((E'.compactlySupportedCohomology 1).frobeniusEnd ^ m))) = ι (LinearMap.trace _ _
      ((E'.compactlySupportedCohomology 2).frobeniusEnd ^ m) - LinearMap.trace _ _
      ((E'.compactlySupportedCohomology 1).frobeniusEnd ^ m)) := by
    have hGL := WeilSheaf.sum_trace_compactlySupportedCohomology E' hm
    rw [finsum_eq_sum_of_support_subset (s := {1, 2}) _ ?_, Finset.sum_pair (by decide)] at hGL
    · rw [Int.negOnePow_one, Int.negOnePow_even 2 even_two, Units.val_neg, Units.val_one,
        neg_smul, one_smul, one_smul, ← sub_eq_neg_add] at hGL
      rw [hGL]
      refine RingHom.conj_map_finsum_of_forall ι _ fun x ↦ ?_
      split_ifs
      · rw [map_mul, map_mul, map_natCast, hloc]
        simp
      · simp
    · intro r hr
      rw [Function.mem_support] at hr
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      by_contra hr'
      refine hr ?_
      have : Subsingleton (E'.compactlySupportedCohomology r).carrier := by
        rcases lt_trichotomy r 0 with hr0 | rfl | hr0
        · exact WeilSheaf.subsingleton_compactlySupportedCohomology_of_neg E' hr0
        · exact h0
        · exact WeilSheaf.subsingleton_compactlySupportedCohomology_of_isLisse hE' (by omega)
      rw [Subsingleton.elim ((E'.compactlySupportedCohomology r).frobeniusEnd ^ m) 0, map_zero,
        smul_zero]
  -- the factors `P₁, P₂` of the fibre `L`-function have disjoint root radii, hence are real
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  obtain ⟨hr1, hr2⟩ := LinearMap.map_charpolyRev_conj_eq_self_of_trace ι _ _
    (fun α hα ↦ h1 α hα) (fun α hα ↦ h2 α hα)
    (Real.rpow_lt_rpow_of_exponent_lt hq (by norm_num)) htr
  have hHi : (E'.compactlySupportedCohomology i).IsReal ι := by
    match i with
    | 0 =>
      rw [Nat.cast_zero]
      exact FrobeniusModule.isReal_of_subsingleton ι _
    | 1 =>
      rw [Nat.cast_one]
      exact (Polynomial.forall_coeff_fixed_iff_map_map ι (starRingEnd ℂ) _).2 hr1
    | 2 =>
      rw [Nat.cast_ofNat]
      exact (Polynomial.forall_coeff_fixed_iff_map_map ι (starRingEnd ℂ) _).2 hr2
    | n + 3 =>
      have := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isLisse hE'
        (r := ((n + 3 : ℕ) : ℤ)) (by omega)
      exact FrobeniusModule.isReal_of_subsingleton ι _
  -- back to the stalk at `y`
  have hd := Scheme.Hom.degreeOver_ne_zero (Y ↘ Spec (CommRingCat.of k₀)) y.2
  refine (Polynomial.forall_coeff_expand_fixed_iff ι (starRingEnd ℂ) hd _).1 ?_
  rw [FrobeniusModule.localPolynomial, hcp E i]
  exact hHi

/-- **Mixedness of the direct images over a relative affine curve.** Let `h : U ⟶ Y` be as in
`AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber` and let `F` be a lisse
Weil sheaf on `U`, punctually `ι`-pure of weight `w`. Then each `Rⁱh₀!F` is `ι`-mixed of
weights at most some `v`. The direct images of the real envelope `E = F⁰ ⊕ (F⁰)^∨` of `F` are
real (`AlgebraicGeometry.isReal_higherLowerShriek_of_isAffine_fiber`), hence mixed
(`AlgebraicGeometry.WeilSheaf.IsReal.isMixed`); `Rⁱh₀!F⁰` is a direct summand of `Rⁱh₀!E`, and
`Rⁱh₀!F` is its constant twist back by the projection formula. -/
theorem exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber
    (hfib : ∀ y, IsAffine (h.fiber y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ∃ v : ℝ, ((WeilSheaf.higherLowerShriek k₀ l h i).obj F).IsMixedOfWeightsAtMost ι v := by
  have := SmoothOfRelativeDimension.smooth 1 h
  obtain ⟨w', b, hw', hb⟩ := hw.exists_units_norm_eq ι
  let R := WeilSheaf.higherLowerShriek k₀ l h i
  -- the direct images of the real envelope are real, hence mixed
  obtain ⟨v, hv⟩ := (isReal_higherLowerShriek_of_isAffine_fiber ι h hfib (F.realEnvelope hF b)
    (hF.realEnvelope b) (WeilSheaf.isReal_realEnvelope hF hw' hb) (hw'.realEnvelope hF hb)
    i).isMixed
  -- `Rⁱh₀!(F ⊗ 𝓑_b)` is a direct summand of `Rⁱh₀!E`
  have h₀ : (R.obj (F.constantTwist b)).IsMixedOfWeightsAtMost ι v :=
    hv.of_mono (R.map (Limits.biprod.inl : F.constantTwist b ⟶ F.realEnvelope hF b))
  obtain ⟨e⟩ := WeilSheaf.nonempty_higherLowerShriek_constantTwist_iso h F b i
  exact ⟨_, ((h₀.of_iso e).constantTwist (b := b⁻¹) rfl).of_iso
    ((R.obj F).constantTwistInvIso b)⟩

/-- **Pure lisse relative affine-curve step.** Let `h : U ⟶ Y` be a smooth separated morphism of
relative dimension one between separated `k₀`-schemes of finite type whose fibres are affine,
so that every nonempty geometric fibre is a smooth affine curve, and let `F` be a lisse Weil
sheaf on `U`, punctually `ι`-pure of weight `w`. Then `Rⁱh₀!F` is `ι`-mixed of weights at most
`w + i`: it is mixed
(`AlgebraicGeometry.exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber`), its
local Frobenius eigenvalues have weights at most `w + i`
(`AlgebraicGeometry.hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber`), and the punctual
bound cuts the mixed filtration down
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_hasWeightsAtMost`). -/
theorem isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber
    (hfib : ∀ y, IsAffine (h.fiber y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    haveI := SmoothOfRelativeDimension.smooth 1 h
    ((WeilSheaf.higherLowerShriek k₀ l h i).obj F).IsMixedOfWeightsAtMost ι (w + i) := by
  have := SmoothOfRelativeDimension.smooth 1 h
  obtain ⟨v, hv⟩ :=
    exists_isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber ι h hfib F hF hw i
  exact hv.of_hasWeightsAtMost
    (hasWeightsAtMost_higherLowerShriek_of_isAffine_fiber ι h hfib F hF hw i)

end RelativeCurve

-- the surjectivity of `h` is not needed: an empty fibre contributes nothing
set_option linter.unusedVariables false in
/-- Let `Y` be a separated `k₀`-scheme of finite type, let `U` be an open subscheme of the relative
affine line `𝔸¹_Y` whose projection `h` to `Y` is surjective, and let `F` be a lisse Weil sheaf on
`U`, punctually `ι`-pure of weight `w`. Then `Rʳh₀!F` is mixed of weights at most `w + r`:

```
U --- u ---> 𝔸¹_Y
  \            |
   \ h         | ↘
    `--------> Y
```
-/
theorem isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine {U Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (u : U ⟶ 𝔸(PUnit.{u + 1}; Y))
    [IsOpenImmersion u] [QuasiCompact u] [u.IsOver (Spec (CommRingCat.of k₀))]
    (hu : Surjective (u ≫ 𝔸(PUnit.{u + 1}; Y) ↘ Y)) (F : WeilSheaf k₀ l U) (hF : F.IsLisse)
    (w : ℝ) (hpure : F.IsPunctuallyPureOfWeight ι w) (r : ℕ) :
    ((WeilSheaf.higherLowerShriek k₀ l (u ≫ 𝔸(PUnit.{u + 1}; Y) ↘ Y) r).obj
      F).IsMixedOfWeightsAtMost ι (w + r) := by
  -- `h = u ≫ 𝔸¹_Y ↘ Y` is smooth of relative dimension `0 + 1` with affine fibres
  have : SmoothOfRelativeDimension 1 (u ≫ 𝔸(PUnit.{u + 1}; Y) ↘ Y) := by
    rw [show 1 = 0 + Nat.card PUnit.{u + 1} by simp]
    infer_instance
  exact isMixedOfWeightsAtMost_higherLowerShriek_of_isAffine_fiber ι _
    (AffineSpace.isAffine_fiber_of_isOpenImmersion u) F hF hpure r

end AlgebraicGeometry
