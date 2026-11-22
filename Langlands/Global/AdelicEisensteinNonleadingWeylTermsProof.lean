import Langlands.Global.AdelicEisensteinNonleadingWeylTermsStatement
import Langlands.Global.AdelicEisensteinAmbientParametersProof
import Langlands.Global.AdelicEisensteinWeylSeparation
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.GroupScheme.Rational.LanglandsInvariantForm

/-! # Exclusion of competing Weyl exponents from the leading chamber -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Plancherel AdelicGroupPoints RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily Langlands.Automorphic.GroupSchemeFunctions

/-- Weyl separation applied to the actual leading-exponent predicate. -/
theorem eisensteinNonleadingWeylTerms : EisensteinNonleadingWeylTermsStatement.{u} := by
  intro F _ _ G _ _ _ fam P Q _ _ proj n c hproj hc
  let w : relativeWeylGroup fam.i := QuotientGroup.mk n
  change (∀ α ∈ Q.val, schemeWeylCharacterAction fam.i w⁻¹ α ∈ P.val) → _
  intro hinv S hS
  let rQ : ParabolicRootPresentation (fam.p Q) (fam.l Q) (fam.a Q) :=
    ⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩
  let hA := (fam.isCompatible Q).splitComponent.isCentralSplitTorus.1.1
  let hT := fam.maximalSplit.isSplitSubtorus.1
  have hpOver : Mono (fam.p P).hom.hom := by
    let := (fam.isCompatible P).parabolic.isClosedSubgroup.mono
    exact Over.mono_of_mono_left _
  let : Mono (fam.p P) := (Grp.forget _).mono_of_mono_map (f := fam.p P) hpOver
  obtain ⟨R, hR⟩ := rQ.exists_regular_bound_for_ambient_chamber_separation hA hT
    fam.connectedReductive hS
  refine ⟨R, fun lam hreg v hv hpos J exponent shift hshift heq hleading => ?_⟩
  let translated := weylParameter (fam.l P) c proj lam
  let initial := fam.chamberEmbedding P (parameterRealPart F (fam.P P) lam)
  let lifted := weylCharacterRestrictionLift hA hT (fam.f Q) fam.i
    (realParameterRestriction (fam.a Q ≫ fam.l Q) (parameterRealPart F (fam.P Q) translated))
  have hLift : fam.chamberEmbedding Q (parameterRealPart F (fam.P Q) translated) =
      lifted :=
    eisensteinAmbientParameterLift F G (fam.P Q) (fam.M Q) (fam.A Q)
      (fam.p Q) (fam.l Q) (fam.a Q) rQ hA hT (fam.torus Q)
      fam.connectedReductive (fam.torus_comp Q) (parameterRealPart F (fam.P Q) translated)
  have hTransport : fam.chamberEmbedding Q (parameterRealPart F (fam.P Q) translated) =
      relativeWeylRealCharacterAction fam.i w initial :=
    eisensteinAmbientWeylParameter F G (fam.P P) (fam.M P) (fam.P Q) (fam.M Q) fam.T fam.i
      (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) (fam.torus P) (fam.torus Q) proj n c
      (fam.torus_comp P) (fam.torus_comp Q) hproj hc lam
  have hAction :
      relativeWeylRealCharacterAction fam.i (v * w⁻¹) lifted =
        relativeWeylRealCharacterAction fam.i v initial := by
    rw [← hLift, hTransport, ← LinearEquiv.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hne : v * w⁻¹ ≠ 1 := fun h => hv (mul_inv_eq_one.mp h)
  have hpositive : ∀ α ∈ Q.val,
      schemeWeylCharacterAction fam.i (v * w⁻¹) α ∈ positiveRelativeRoots fam.i fam.ν := by
    intro α hα
    rw [map_mul, LinearEquiv.mul_apply]
    exact hpos _ (hinv α hα)
  obtain ⟨β, hβ, hneg⟩ :=
    hR translated hreg (v * w⁻¹) hne hpositive shift hshift
  change relativeWeylInvariantForm fam.i hT
    (relativeWeylRealCharacterAction fam.i (v * w⁻¹) lifted + shift) ((1 : ℝ) ⊗ₜ[ℤ] β) < 0 at hneg
  rw [hAction, ← heq] at hneg
  let B := relativeWeylInvariantForm fam.i hT
  have hB : IsWeylInvariantInnerProduct fam.i B :=
    ⟨relativeWeylInvariantForm_symm fam.i hT,
      fun _ => relativeWeylInvariantForm_pos fam.i hT,
      relativeWeylInvariantForm_invariant fam.i hT⟩
  let root : relativeRoots fam.i := ⟨β, hβ.1.1⟩
  have hNonneg := (fam.coroots.coroot_nonneg_iff fam.i B hB root _).mp (hleading root hβ)
  exact (not_lt_of_ge hNonneg) hneg

section Comparison

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (P Q : StandardIndex F G fam.i fam.ν)
  [Fintype (relativeWeylGroup fam.i)] [Mono (CommGroupScheme.groupHom (fam.f Q)).hom.hom.left]
  {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

local notation "Y" => (AdelicGroupPoints F G → ℂ)
local notation "Parameter" => ComplexCharacterParameter F (fam.P P)
local notation "Automorphic" =>
  IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho

/-- The comparison of global forms from supplied cuspidal expansions and
injectivity of their leading components. The Weyl exponent comparison
gives a single threshold, simultaneously for every standard parabolic. -/
theorem eq_of_weyl_cuspidal_expansions
    (proj : fam.P Q ⟶ fam.M Q) (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M P)
    (hproj : fam.l Q ≫ proj = 𝟙 (fam.M Q))
    (hc : IsWeylConjugation (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) n.val c)
    (hinv : ∀ α ∈ Q.val,
      schemeWeylCharacterAction fam.i ((QuotientGroup.mk n : relativeWeylGroup fam.i)⁻¹) α ∈ P.val)
    (hinjective : ∀ (f g : Y) (L : StandardIndex F G fam.i fam.ν → Y),
      Automorphic f → Automorphic g →
      fam.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho f L →
      fam.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho g L → f = g)
    (EP EQ : Parameter → Y) (D : Set Parameter) (S : Set (Vstar fam.T)) (hS : S.Finite)
    (hAut : ∀ lam ∈ D, Automorphic (EP lam) ∧ Automorphic (EQ lam))
    (hExpansion : ∀ lam ∈ D, ∀ J : StandardIndex F G fam.i fam.ν,
      ∃ left right : Y,
        fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J (EP lam)) left ∧
        fam.IsCuspidalProjection hsmooth Kinf rho J (fam.constantTerm J (EQ lam)) right ∧
        ∃ (s t u : Finset (ComplexCharacterParameter F (fam.P J)))
            (f g b : ComplexCharacterParameter F (fam.P J) → Y),
          fam.IsExponentDecomposition hsmooth Kinf rho J left s f ∧
          fam.IsExponentDecomposition hsmooth Kinf rho J right t g ∧
          left = right + ∑ exponent ∈ u, b exponent ∧
          ∀ exponent ∈ u, fam.HasUnnormalizedExponent J exponent (b exponent) ∧
            ∃ v : relativeWeylGroup fam.i, v ≠ QuotientGroup.mk n ∧
              (∀ α ∈ P.val, schemeWeylCharacterAction fam.i v α ∈ positiveRelativeRoots fam.i fam.ν) ∧
              ∃ shift ∈ S, fam.chamberEmbedding J (parameterRealPart F (fam.P J) exponent) =
                relativeWeylRealCharacterAction fam.i v
                  (fam.chamberEmbedding P (parameterRealPart F (fam.P P) lam)) + shift) :
    let rQ : ParabolicRootPresentation (fam.p Q) (fam.l Q) (fam.a Q) :=
      ⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩
    let hA := (fam.isCompatible Q).splitComponent.isCentralSplitTorus.1.1
    let hT := fam.maximalSplit.isSplitSubtorus.1
    ∃ R : ℝ, ∀ lam ∈ D, rQ.IsRegularParameter hA hT R (weylParameter (fam.l P) c proj lam) →
      EP lam = EQ lam := by
  obtain ⟨R, hR⟩ := eisensteinNonleadingWeylTerms F G fam P Q proj n c hproj hc hinv S hS
  refine ⟨R, fun lam hlam hreg => ?_⟩
  obtain ⟨L, hleft, hright⟩ :=
    fam.exists_common_leadingComponents_of_nonleading_differences hsmooth Kinf rho
      (EP lam) (EQ lam) (by
        intro J
        obtain ⟨left, right, hl, hr, s, t, u, f, g, b, hs, ht, heq, hTerms⟩ :=
          hExpansion lam hlam J
        refine ⟨left, right, hl, hr, s, t, u, f, g, b, hs, ht, ?_, heq⟩
        intro exponent he
        obtain ⟨hExp, v, hne, hv, shift, hshift, hexp⟩ := hTerms exponent he
        exact ⟨hExp, hR lam hreg v hne hv J exponent shift hshift hexp⟩)
  exact hinjective _ _ L (hAut lam hlam).1 (hAut lam hlam).2 hleft hright

end Comparison

end Langlands.Global
