import Langlands.Global.AdelicConvergentCuspidalTestExpansionStatement

/-! # Uniqueness of convergent Eisenstein series from their cuspidal components

Bernstein–Lapid (6.21) and (6.22): at sufficiently regular parameters, the Eisenstein series is
the only automorphic form whose cuspidal components along every standard parabolic differ from
those of the inducing twist only by terms with competing Weyl exponents. The statement is uniform
over finite linear combinations of fixed inducing functions. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Bernstein–Lapid (6.22), for finite families of inducing data. Fix automorphic functions
`φ i` on `U_I(𝔸) M_I(F) \ G(𝔸)` (`i < n`) and competing Weyl exponent data for the identity element
along every standard `J`. Beyond one threshold, for every `R`-regular `λ` and all coefficients
`a i`, every automorphic form `v` on `G(F) \ G(𝔸)` such that, for every standard `J`, the cuspidal
projection of `C_J v − C_{I,J} (∑ a i φ_{i,λ})` along `J` has an exponent decomposition whose nonzero
components all carry competing labels `(data J).label k λ`, is `∑ a i E(φ i, λ)`. -/
def EisensteinRegularUniquenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
      IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G fam.i fam.ν,
        IsMaximalCompactSubgroup F (fam.M J)
          (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom),
        IsClosedSubgroup rho →
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        let hcalc := adelicDifferentialCommutator_of_smooth F G hsmooth
        let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
          ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
        let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        let hT := fam.maximalSplit.isSplitSubtorus.1
        ∀ (n : ℕ) (phi : Fin n → AdelicGroupPoints F G → ℂ),
          (∀ i, fam.IsAutomorphicOn hsmooth Kinf rho I (phi i)) →
          ∀ data : ∀ J : StandardIndex F G fam.i fam.ν, CompetingWeylExponents fam I J 1,
            ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F (fam.P I),
              r.IsRegularParameter hA hT R lam →
              ∀ (a : Fin n → ℂ) (v : AdelicGroupPoints F G → ℂ),
                IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho v →
                (∀ J : StandardIndex F G fam.i fam.ν,
                  ∃ (vc : AdelicGroupPoints F G → ℂ)
                    (s : Finset (ComplexCharacterParameter F (fam.P J)))
                    (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
                    fam.IsCuspidalProjection hsmooth Kinf rho J
                        (fam.constantTerm J v - fam.parabolicConstantTerm I J
                          (fun g => ∑ i, a i * hK.parameterTwist (phi i) lam g)) vc ∧
                      fam.IsExponentDecomposition hsmooth Kinf rho J vc s c ∧
                      ∀ mu ∈ s, c mu ≠ 0 → ∃ k, mu = (data J).label k lam) →
                v = fun g => ∑ i, a i * hK.eisensteinSeries (phi i) lam g

end Langlands.Global
