import Langlands.Global.AdelicConvergentCuspidalTestExpansionStatement
import Langlands.Global.AdelicExponentPolynomials

/-! # Cuspidal tests of convergent Eisenstein series with a uniform exponent degree

Bernstein–Lapid (6.17), (6.18) and (6.20) for the identity Weyl element, in the norm-one Levi
cusp tests of §6.2, for finite linear combinations of fixed inducing functions, with competing
labels and a bound on the polynomial degree of the competing exponent terms that depend neither
on the parameter nor on the coefficients. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- Fix finitely many automorphic inducing functions `φ i` on `U_I(𝔸) M_I(F) \ G(𝔸)`. For every
standard `J` there are a threshold, competing affine Weyl labels of the identity element and a
degree bound `n` such that, for every sufficiently regular `λ` and all coefficients `a i`, the
tested constant term along `J` of `∑ a i E(φ i, λ)`, minus the tested constant term along `J` of
the twist `∑ a i φ_{i,λ}`, is a finite sum of tested terms with the competing exponents
`data.label k λ`, each of polynomial degree at most `n`. -/
def EisensteinUniformCuspidalExpansionStatement : Prop :=
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
        let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
          ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
        let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        let hT := fam.maximalSplit.isSplitSubtorus.1
        ∀ (m : ℕ) (phi : Fin m → AdelicGroupPoints F G → ℂ),
          (∀ i, fam.IsAutomorphicOn hsmooth Kinf rho I (phi i)) →
          ∀ J : StandardIndex F G fam.i fam.ν,
            ∃ (R : ℝ) (data : CompetingWeylExponents fam I J 1) (n : ℕ),
              ∀ lam : ComplexCharacterParameter F (fam.P I), r.IsRegularParameter hA hT R lam →
                ∀ a : Fin m → ℂ,
                  ∃ terms : Fin data.size → AdelicGroupPoints F G → ℂ,
                    (∀ k, fam.HasPolynomialOrbit J (data.label k lam) n (terms k)) ∧
                    ∀ test : AdelicGroupPoints F (fam.M J) → ℂ,
                      fam.IsLeviCuspForm Kinf rho J test →
                      ∀ g : AdelicGroupPoints F G,
                        (∀ k, Integrable (fam.leviPairingIntegrand J (terms k) g test)
                          (normOneRationalQuotientHaarMeasure F (fam.M J))) ∧
                        fam.leviPairing J (fam.constantTerm J
                            (fun x => ∑ i, a i * hK.eisensteinSeries (phi i) lam x)) g test -
                          fam.leviPairing J (fam.parabolicConstantTerm I J
                            (fun x => ∑ i, a i * hK.parameterTwist (phi i) lam x)) g test =
                        ∑ k, fam.leviPairing J (terms k) g test

end Langlands.Global
