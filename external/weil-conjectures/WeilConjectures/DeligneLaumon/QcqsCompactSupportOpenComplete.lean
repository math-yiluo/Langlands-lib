/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportConstructible
import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulCompleteness
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenDvrRingedIdentification

/-! Quasi-compact open extension preserves derived completeness.
Source: Bhatt--Scholze, Lemmas 6.7.7 and 6.1.13; Stacks Tags 0E8I and 0F7J.
(blueprint: lem-qcqs-compact-support-image-complete-open).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [Xbase : X.Over (Spec (.of K₀))] [Ybase : Y.Over (Spec (.of K₀))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))]
  [Xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  [fbase : f.IsOver (Spec (.of K₀))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

include K₀ hl Xbase Ybase Xft Xqc Yft Yqc fbase fs fft fqc

set_option linter.unusedSectionVars false in
/-- The completed extension by a quasi-compact open immersion preserves the
completion unit. This is the open factor of the proper/open compact-support
completeness argument.
Source: Bhatt--Scholze, Lemmas 6.7.7 and 6.1.13; Stacks Tags 0E8I and 0F7J.
Proof: transport the completion unit through the normalized quotient tower for
quasi-compact open extension. Exactness and preservation of countable products
identify the target Roos triangle with the image of the source triangle, and the
unit equation then gives the required derived completeness.
(blueprint: lem-qcqs-compact-support-image-complete-open). -/
theorem sfQcqsCompactSupport_open_complete
    (K : sfIntegralConstructibleCategory l E X) :
    IsSfDerivedComplete l E c.Z
      ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj) := by
  classical
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of K₀)).inv ≫ (X ↘ Spec (.of K₀)).appTop
    simpa only [map_natCast] using hl.map ρ.hom
  have hZ : IsUnit (l : Γ(c.Z, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of K₀)).inv ≫
      (c.g ≫ (Y ↘ Spec (.of K₀))).appTop
    simpa only [map_natCast] using hl.map ρ.hom
  obtain ⟨d, hd, hres, hmodels, hopen⟩ := openQuotientKoszulCompleteness l E
  obtain ⟨O, hO⟩ := hopen X c.Z c.i hX hZ
  have hK := (compactSupport_complete_iff l E X K.obj).mp K.property.1
  have hJ := (compactSupport_complete_iff l E c.Z (O.jShriek.obj K.obj)).mpr
    (hO K.obj hK).1
  obtain ⟨e⟩ := IntegralSystemRealization.openDvr_ringed_identification l E c.i O
  exact complete_iso l E c.Z (e.app K.obj) hJ

end WeilConjectures
