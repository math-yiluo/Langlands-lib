/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# Finite direct images of real and of pure Weil sheaves

For a proper morphism `π` of `k₀`-schemes, the direct image `π₀*F` of a Weil sheaf is the
cohomology sheaf `R⁰π₀!F` of the direct image with compact support
(`AlgebraicGeometry.WeilSheaf.lowerStarIsoHigherLowerShriekZero`). For `π` finite, `π₀!` is a
quasi-finite direct image, so `π₀*` preserves `ι`-reality
(`AlgebraicGeometry.WeilSheaf.IsReal.lowerStar_of_isFinite`) and punctual purity
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.lowerStar_of_isFinite`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Iso

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] {F G : WeilSheaf k₀ l X}

/-- `ι`-reality is invariant under isomorphism. -/
theorem IsReal.of_iso {ι : PadicAlgCl l →+* ℂ} (e : F ≅ G) (h : F.IsReal ι) : G.IsReal ι :=
  fun x ↦ by
    obtain ⟨e'⟩ := nonempty_equiv_stalk_of_iso e x
    exact (h x).of_localPolynomial_eq e'.localPolynomial_eq.symm

end Iso

section Proper

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of k₀))]
  [IsProper π] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- For a proper morphism `π`, the direct image `π₀*F` of a Weil sheaf is `R⁰π₀!F`. -/
noncomputable def lowerStarIsoHigherLowerShriekZero (F : WeilSheaf k₀ l X) :
    (lowerStar π).obj F ≅ (higherLowerShriek k₀ l π 0).obj F :=
  (homologySheafZeroDerivedLowerStarIso π F).symm ≪≫
    (WeilComplex.homologySheaf 0).mapIso
      (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar π (toComplex.obj F)).symm

end Proper

/-- For a finite morphism `π` of `k₀`-schemes, the direct image `π₀*` preserves `ι`-reality: it
is the quasi-finite direct image `R⁰π₀!`, whose local polynomials are products of expansions of
those of `F` (`AlgebraicGeometry.WeilSheaf.IsReal.higherLowerShriek_zero_of_quasiFinite`). -/
theorem IsReal.lowerStar_of_isFinite {ι : PadicAlgCl l →+* ℂ} {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of k₀))]
    [IsFinite π] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} (h : F.IsReal ι) : ((lowerStar π).obj F).IsReal ι :=
  (h.higherLowerShriek_zero_of_quasiFinite π).of_iso
    (lowerStarIsoHigherLowerShriekZero π F).symm

/-- **Purity under a finite direct image.** If `π : X ⟶ Y` is a finite morphism of `k₀`-schemes
and `F` is punctually `ι`-pure of weight `w`, then so is `π₀*F`: it is the quasi-finite direct
image `R⁰π₀!F`, at a closed point `y` every eigenvalue `β` of `F_y` has a power `β ^ e`, with
`e = [κ(x) : κ(y)]`, which is an eigenvalue of `F_x` for a closed point `x` above `y`, and
`q_x = q_y ^ e`
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.higherLowerShriek_zero_of_quasiFinite`).
The blueprint states this for `π` finite étale; étaleness is not needed
(blueprint: `lemma-finite-quasi-finite-direct-images--3`). -/
theorem IsPunctuallyPureOfWeight.lowerStar_of_isFinite {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of k₀))] [IsFinite π]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} (h : F.IsPunctuallyPureOfWeight ι w) :
    ((lowerStar π).obj F).IsPunctuallyPureOfWeight ι w :=
  (h.higherLowerShriek_zero_of_quasiFinite π).of_mono
    (lowerStarIsoHigherLowerShriekZero π F).hom

end AlgebraicGeometry.WeilSheaf
