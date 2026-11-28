import Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction

/-! # Continuation of tested intertwining terms with poles along the inverted roots

Bernstein–Lapid, Theorem 2.3 (3) and §8.6, with the region of convergence of §2.2
(Mœglin–Waldspurger II.1.6). For a standard parabolic family, an element `(n, c)` of
`W(P_{I'}, P_J)` given by a rational point `n` normalizing the maximal split torus, and an
automorphic form `φ'` along `P_{I'}`, the cuspidal tests of the intertwining terms
`[M(n, μ) φ']_{nμ}` continue meromorphically in `μ ∈ X^*(P_{I'}) ⊗ ℂ` with poles only along the
hyperplanes of the roots of `A_{I'}` in `U_{I'}` inverted by `n`, and the continuation agrees with
the integral wherever the real part of `μ` is sufficiently regular for these inverted roots
alone. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Aubert.General.RationalPointFamily

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- The roots of the split component `A_J` in the unipotent radical of `P_J` inverted by the
Weyl element of `n`: the roots `β = χ ∘ f_J` of `A_J` in `U_J` that are restrictions of a
positive relative root `χ` of the maximal split torus whose transport `n · χ`,
`(n · χ)(x) = χ(n⁻¹ x n)`, is not positive. -/
def invertedRoots (J : StandardIndex F G 𝓕.i 𝓕.ν) (n : normalizerPoints 𝓕.i) :
    Set (characterLattice (𝓕.A J)) :=
  {β | β ∈ (𝓕.rootPresentation J).unipotentRoots ∧
    ∃ χ ∈ positiveRelativeRoots 𝓕.i 𝓕.ν, 𝓕.f J ≫ χ = β ∧
      schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) χ ∉ positiveRelativeRoots 𝓕.i 𝓕.ν}

variable [Fintype (relativeWeylGroup 𝓕.i)] [∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left]

/-- A parameter `μ ∈ X^*(P_J) ⊗ ℂ` is `R`-regular for the roots inverted by `n` when
`R < B(Re μ|_{A_J}, β)` for every root `β` of `A_J` in `U_J` inverted by `n`, where `B` is the
Weyl-induced positive form on `X^*(A_J) ⊗ ℝ` (as in `IsRegularParameter`, which asks this for
all roots of `A_J` in `U_J`). -/
def IsInvertedRootRegular (J : StandardIndex F G 𝓕.i 𝓕.ν) (n : normalizerPoints 𝓕.i) (R : ℝ)
    (mu : ComplexCharacterParameter F (𝓕.P J)) : Prop :=
  ∀ β ∈ 𝓕.invertedRoots J n, R < (𝓕.rootPresentation J).realRootFunctional
    (𝓕.isCompatible J).splitComponent.isCentralSplitTorus.1.1 𝓕.maximalSplit.isSplitSubtorus.1
    β (parameterRealPart F (𝓕.P J) mu)

end StandardParabolicFamily

/-- **Continuation of tested intertwining terms with poles along the inverted roots**
(derived from Bernstein–Lapid, Theorem 2.3 (3), §2.2 and §8.6). In the setting of
`EisensteinCuspidalTestStandardExpansionStatement` (standard parabolic family `𝓕`, maximal
compact `K` in good position, closed embedding `rho`), let `I'`, `J` be standard indices, let
`(n, c)` be an element of `W(P_{I'}, P_J)` given by a rational point `n` normalizing the maximal
split torus, let `π` be a retraction of the Levi of `P_J`, and let `φ'` be automorphic on
`U_{I'}(𝔸) M_{I'}(F) \ G(𝔸)`. Then there are finitely many functions `Φ i` on `G(𝔸)` and scalar
functions `coeff i` on `X^*(P_{I'}) ⊗ ℂ`, meromorphic in linear coordinates with one domain `D`
and with poles along the hyperplanes of the root forms of the roots of `A_{I'}` in `U_{I'}`
inverted by `n`, and a bound `R` such that every parameter `μ` that is `R`-regular for the
inverted roots lies in `D` and satisfies, for every cusp form `ψ` on `M_J(F) \ M_J(𝔸)` and
every `g`, `(C_J [M(n, μ) φ']_{nμ}(· g), ψ) = ∑ i, coeff i μ · (C_J [Φ i]_{nμ}(· g), ψ)`. -/
def IntertwiningInvertedRootCuspidalTestContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) [Fintype (relativeWeylGroup 𝓕.i)]
    [∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G))
    (h₀ : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K),
    IsMaximalCompactSubgroup F G K →
    (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom), IsClosedSubgroup rho →
      ∀ (I' J : StandardIndex F G 𝓕.i 𝓕.ν) (n : normalizerPoints 𝓕.i)
        (c : 𝓕.M J ⟶ 𝓕.M I') (π : 𝓕.P J ⟶ 𝓕.M J),
        IsWeylConjugation (𝓕.p I') (𝓕.l I') (𝓕.p J) (𝓕.l J) n.val c →
        𝓕.l J ≫ π = 𝟙 (𝓕.M J) →
        ∀ φ' : AdelicGroupPoints F G → ℂ,
          𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I' φ' →
          ∃ (k : ℕ) (Φ : Fin k → AdelicGroupPoints F G → ℂ)
            (coeff : Fin k → ComplexCharacterParameter F (𝓕.P I') → ℂ)
            (D : Set (ComplexCharacterParameter F (𝓕.P I'))),
            (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
            (∀ i, HasRootHyperplanePoles
              ((𝓕.rootPresentation I').rootFunctional
                (𝓕.isCompatible I').splitComponent.isCentralSplitTorus.1.1
                𝓕.maximalSplit.isSplitSubtorus.1)
              (𝓕.invertedRoots I' n) (coeff i) D) ∧
            ∃ R : ℝ, (∀ mu, 𝓕.IsInvertedRootRegular I' n R mu → mu ∈ D) ∧
              ∀ mu, 𝓕.IsInvertedRootRegular I' n R mu →
              ∀ ψ, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
                𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ I').intertwiningIntegral
                      (𝓕.iU I') (𝓕.iU J ≫ 𝓕.p J) n.val φ' mu)) g ψ =
                  ∑ i, coeff i mu * 𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ J).parameterTwist (Φ i)
                      (weylParameter (𝓕.l I') c π mu))) g ψ

end Langlands.Global
