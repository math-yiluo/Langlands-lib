import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Passage of Eisenstein series to a standard family with a compact in good position

An Eisenstein series for an arbitrary parabolic `P` with a root presentation and an arbitrary
maximal compact Iwasawa subgroup `K` is, after an archimedean right translation, a finite
combination with entire exponential coefficients of Eisenstein series for the corresponding
standard parabolic of a standard family and a maximal compact subgroup in good position. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Standardization of the data of an Eisenstein series. In the setting of
`EisensteinSystemDominationStatement` (without the positivity of the matrix size) there are a
standard parabolic family `fam` with an index `I` such that `fam.p I` has the same image as `p`,
a morphism `j : P_I → P` over `G` whose character restriction is a linear isomorphism `iota` of
parameter spaces, a maximal compact `K'` in good position (Iwasawa coverage for the minimal
standard parabolic and maximal compact intersections with all standard Levis), an archimedean
point `t` of `G(F_∞)`, finitely many automorphic functions `φ' i` on `U_I(𝔸) M_I(F) \ G(𝔸)` and
linear forms `ℓ i` on parameters with:

* right translation by `t` carries automorphic forms for `K_∞` to automorphic forms for `K'_∞`;
* regularity transport: for every `R` there is `R'` such that `iota` maps `R'`-regular parameters
  to `R`-regular parameters of the standard presentation;
* for sufficiently regular `λ` and every `g`,
  `E(φ, λ)(g t) = ∑ i, exp(ℓ i λ) · E'(φ' i, iota λ)(g)`, where `E'` is formed with `K'`.

The instances needed to form `E'` are quantified inside the conclusion (the Weyl group instance is
a subsingleton and the other two are propositions). -/
def EisensteinStandardizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsClosedSubgroup rho → IsMaximalCompactSubgroup F G K →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)
        (K' : Subgroup (AdelicGroupPoints F G)) (hK' : IsIwasawaCompact (fam.p I) K')
        (t : InfiniteAdelicGroupPoints F G)
        (iota : ComplexCharacterParameter F P ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P I))
        (m : ℕ) (φ' : Fin m → AdelicGroupPoints F G → ℂ)
        (ℓ : Fin m → ComplexCharacterParameter F P →ₗ[ℂ] ℂ),
        SubgroupFunctor.range (fam.p I) = SubgroupFunctor.range p ∧
        (∃ j : fam.P I ⟶ P, j ≫ p = fam.p I ∧ ∀ lam, iota lam = parameterRestrict j lam) ∧
        IsMaximalCompactSubgroup F G K' ∧
        IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K' ∧
        (∀ J : StandardIndex F G fam.i fam.ν,
          IsMaximalCompactSubgroup F (fam.M J)
            (K'.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) ∧
        (∀ i, fam.IsAutomorphicOn hsmooth (K'.comap (ofInfinite F G).toMonoidHom) rho I (φ' i)) ∧
        (∀ f : AdelicGroupPoints F G → ℂ,
          IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
              (K.comap (ofInfinite F G).toMonoidHom) rho f →
            IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
              (K'.comap (ofInfinite F G).toMonoidHom) rho (fun g => f (g * ofInfinite F G t))) ∧
        ∀ [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
          [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left],
          let r' : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
            ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
          let hA' := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          let hT' := fam.maximalSplit.isSplitSubtorus.1
          (∀ R : ℝ, ∃ R' : ℝ, ∀ lam : ComplexCharacterParameter F P,
            r.IsRegularParameter hA hT R' lam → r'.IsRegularParameter hA' hT' R (iota lam)) ∧
          ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam →
            ∀ g : AdelicGroupPoints F G,
              hK.eisensteinSeries φ lam (g * ofInfinite F G t) =
                ∑ i, Complex.exp (ℓ i lam) * hK'.eisensteinSeries (φ' i) (iota lam) g

end Langlands.Global
