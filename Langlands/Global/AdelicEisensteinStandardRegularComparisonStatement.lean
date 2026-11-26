import Langlands.Global.AdelicEisensteinFunctionalEquationStatement
import Langlands.Global.AdelicConvergentCuspidalTestExpansionStatement

/-! # The Eisenstein comparison on a regular patch for one standard family -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Aubert.General.RationalPointFamily

/-- **Comparison on a regular patch in the standard setting** (Bernstein–Lapid §8.6, the
identity `E(φ, λ) = E(M(w, λ)φ, wλ)` where `⟨w Re λ, α^∨⟩ ≫ 0`). For standard parabolics
`P_I`, `P_Q` of one compatible family, a normalizer point `n` presenting `w ∈ W(P_I, P_Q)`
with `w(I) ⊆ Q` and `w⁻¹(Q) ⊆ I`, and a maximal compact `K` in good position, the data of
`EisensteinFunctionalEquationStatement` give, for every bound `R`, a nonempty open patch in
linear coordinates on which `wλ` is `R`-regular for `P_Q` and the continued `P_I`-series equals
the convergent `P_Q`-series of the continued intertwining datum. -/
def StandardEisensteinRegularComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I Q : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    [IsClosedImmersion (fam.p Q).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f Q)).hom.hom.left]
    (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M I) (proj : fam.P Q ⟶ fam.M Q),
    fam.l Q ≫ proj = 𝟙 (fam.M Q) →
    IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) n.val c →
    (∀ α ∈ I.val, schemeWeylCharacterAction fam.i
      (QuotientGroup.mk n : relativeWeylGroup fam.i) α ∈ Q.val) →
    (∀ α ∈ Q.val, schemeWeylCharacterAction fam.i
      ((QuotientGroup.mk n : relativeWeylGroup fam.i)⁻¹) α ∈ I.val) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hKI : IsIwasawaCompact (fam.p I) K)
      (hKQ : IsIwasawaCompact (fam.p Q) K),
      IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth),
        IsClosedSubgroup rho →
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        let rI : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
          ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
        let rQ : ParabolicRootPresentation (fam.p Q) (fam.l Q) (fam.a Q) :=
          ⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩
        let hAI := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        let hAQ := (fam.isCompatible Q).splitComponent.isCentralSplitTorus.1.1
        let hT := fam.maximalSplit.isSplitSubtorus.1
        ∀ φ : AdelicGroupPoints F G → ℂ,
          IsAutomorphicFunctionOn F G hsmooth hcalc
            (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) Kinf rho φ →
        ∀ (EP : ComplexCharacterParameter F (fam.P I) → AdelicGroupPoints F G → ℂ)
          (DP : Set (ComplexCharacterParameter F (fam.P I))),
          (∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP) →
          (∃ R : ℝ, ∀ lam, rI.IsRegularParameter hAI hT R lam →
            EP lam = hKI.eisensteinSeries φ lam) →
        ∀ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
          (coeff : Fin k → ComplexCharacterParameter F (fam.P I) → ℂ)
          (D : Set (ComplexCharacterParameter F (fam.P I))),
          (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc
            (parabolicQuotientSubgroup F (fam.p Q) (fam.iU Q) (fam.l Q)) Kinf rho (ψ i)) →
          (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
          (∃ R : ℝ, ∀ lam, rI.IsRegularParameter hAI hT R lam → ∀ g,
            hKI.intertwiningOperator hKQ (fam.iU I) (fam.l I) (fam.iU Q) c proj n.val φ lam g =
              ∑ i, coeff i lam * ψ i g) →
        ∀ R : ℝ,
          ∃ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P I))
            (O : Set (Fin m → ℂ)), IsOpen O ∧ O.Nonempty ∧
            ∀ x ∈ O, rQ.IsRegularParameter hAQ hT R (weylParameter (fam.l I) c proj (e x)) ∧
              ∀ g : AdelicGroupPoints F G,
                EP (e x) g = ∑ i, coeff i (e x) *
                  hKQ.eisensteinSeries (ψ i) (weylParameter (fam.l I) c proj (e x)) g

end Langlands.Global
