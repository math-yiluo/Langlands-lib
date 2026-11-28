import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionFamily
import Langlands.Global.AdelicIntertwiningIdentity
import Langlands.Global.AdelicSelfWeylParameters

/-! # The identity Weyl element of the uniform convergent cuspidal expansion

`ConvergentCuspidalTestExpansionUniformStatement` is Bernstein–Lapid (6.20) in the norm-one
Levi tests for one inducing function, as in `ConvergentCuspidalTestExpansionStatement`, with a
degree bound of the competing terms that does not depend on the parameter and with the absolute
convergence of the two tested constant terms. Its case of the identity Weyl element is
`EisensteinUniformCuspidalExpansionOneStatement`
(`eisensteinUniformCuspidalExpansionOne_of_uniform`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Aubert.General.RationalPointFamily

/-- Bernstein–Lapid (6.20) in the norm-one Levi tests for one inducing function, with one degree
bound for all regular parameters and the absolute convergence of the tested constant term of the
Eisenstein series and of the selected intertwined term. -/
def ConvergentCuspidalTestExpansionUniformStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I Q : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M I),
    IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) n.val c →
    let w : relativeWeylGroup fam.i := QuotientGroup.mk n
    (∀ alpha ∈ I.val, schemeWeylCharacterAction fam.i w alpha ∈ Q.val) →
    (∀ alpha ∈ Q.val, schemeWeylCharacterAction fam.i w⁻¹ alpha ∈ I.val) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
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
        ∀ phi : AdelicGroupPoints F G → ℂ, fam.IsAutomorphicOn hsmooth Kinf rho I phi →
          ∀ J : StandardIndex F G fam.i fam.ν,
            ∃ (R : ℝ) (data : CompetingWeylExponents fam I J w) (k : ℕ),
              ∀ lam : ComplexCharacterParameter F (fam.P I), r.IsRegularParameter hA hT R lam →
                ∃ terms : Fin data.size → AdelicGroupPoints F G → ℂ,
                  (∀ j, fam.HasPolynomialOrbit J (data.label j lam) k (terms j)) ∧
                  ∀ test : AdelicGroupPoints F (fam.M J) → ℂ, fam.IsLeviCuspForm Kinf rho J test →
                    ∀ g : AdelicGroupPoints F G,
                      Integrable (fam.leviPairingIntegrand J
                          (fam.constantTerm J (hK.eisensteinSeries phi lam)) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
                      Integrable (fam.leviPairingIntegrand J (fam.parabolicConstantTerm Q J
                          (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q)
                            n.val phi lam)) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
                      (∀ j, Integrable (fam.leviPairingIntegrand J (terms j) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J))) ∧
                      fam.leviPairing J (fam.constantTerm J (hK.eisensteinSeries phi lam)) g test -
                          fam.leviPairing J (fam.parabolicConstantTerm Q J
                            (hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q)
                              n.val phi lam)) g test =
                        ∑ j, fam.leviPairing J (terms j) g test

/-- The identity Weyl element: second index `I`, representative `1` and the identity Levi
conjugation. The selected intertwining integral is the twist. -/
theorem eisensteinUniformCuspidalExpansionOne_of_uniform
    (h : ConvergentCuspidalTestExpansionUniformStatement.{u}) :
    EisensteinUniformCuspidalExpansionOneStatement.{u} := by
  intro F _ _ G _ _ _ fam I _ _ _ K hK hKmax hK0 hKJ N d rho hsmooth hrho Kinf r hA hT phi
    hphi J
  have hw : ∀ alpha : characterLattice fam.T,
      schemeWeylCharacterAction fam.i (QuotientGroup.mk (1 : normalizerPoints fam.i)) alpha =
        alpha := fun alpha => by
    rw [QuotientGroup.mk_one, map_one]; rfl
  have hw' : ∀ alpha : characterLattice fam.T,
      schemeWeylCharacterAction fam.i (QuotientGroup.mk (1 : normalizerPoints fam.i))⁻¹ alpha =
        alpha := fun alpha => by
    rw [QuotientGroup.mk_one, inv_one, map_one]; rfl
  obtain ⟨R, data, k, hmain⟩ := h F G fam I I (1 : normalizerPoints fam.i) (𝟙 (fam.M I))
    (isWeylConjugation_one (p := fam.p I) (l := fam.l I))
    (fun alpha halpha => by rw [hw]; exact halpha)
    (fun alpha halpha => by rw [hw']; exact halpha)
    K hK hKmax hK0 hKJ rho hsmooth hrho phi hphi J
  have hsel : ∀ lam : ComplexCharacterParameter F (fam.P I),
      hK.intertwiningIntegral (fam.iU I) (fam.iU I ≫ fam.p I)
        (1 : normalizerPoints fam.i).val phi lam = hK.parameterTwist phi lam := fun lam => by
    funext g
    exact hK.intertwiningIntegral_one_self (fam.iU I) (fam.isUnipotentRadical I) phi
      (fun x hx y => (hphi).1 x (Subgroup.mem_sup_left hx) y) lam g
  refine ⟨R, data, k, fun lam hlam => ?_⟩
  obtain ⟨terms, hpoly, htest⟩ := hmain lam hlam
  refine ⟨terms, hpoly, fun test ht g => ?_⟩
  have h' := htest test ht g
  rw [hsel lam] at h'
  exact ⟨h'.2.2.1, h'.1, h'.2.1, h'.2.2.2⟩

end Langlands.Global
