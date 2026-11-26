import Langlands.Global.AdelicRootHyperplaneStatement
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Root-hyperplane singularities of the cuspidal tests of Eisenstein series

Bernstein–Lapid, §8.6, for the norm-one Levi pairings (§6.2, (6.8)) of the standard constant
terms of `E(φ, λ)` with cusp forms: they continue meromorphically, with singularities along
root hyperplanes, near every point uniformly in the standard Levi, the cusp form and the
adelic point. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Cuspidal tests of Eisenstein series have singularities along root hyperplanes
(Bernstein–Lapid §8.6, in the scalar form of the norm-one Levi pairings of §6.2, (6.8)). In
the setting of `EisensteinRootHyperplaneContinuationStatement`, let `𝓕` be a standard
parabolic family with `K` in good position: `P₀(𝔸)K = G(𝔸)` for the minimal standard
parabolic and `K ∩ M_J(𝔸)` maximal compact for every standard Levi. For every standard `J`,
cusp form `ψ` on `M_J(F) \ M_J(𝔸)` and `g ∈ G(𝔸)`, the scalar function
`λ ↦ (C_J E(φ, λ)(· g), ψ)_{M_J(F) \ M_J(𝔸)^1}` has a meromorphic continuation `Γ J ψ g`
(domain `D J ψ g`, in linear coordinates), equal to it for `Re λ` sufficiently regular.
Near every point `λ₀ = e s₀` one finite set of roots `β` of `A` in the unipotent radical of
`P`, one exponent `m` and one neighborhood serve all `J`, `ψ` and `g`:
`λ ↦ (∏ β, B(λ - λ₀, β))^m · Γ J ψ g λ` agrees with a holomorphic function there. -/
def EisensteinCuspidalTestRootHyperplaneStatement : Prop :=
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
    ∀ (𝓕 : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact p K),
      IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
        (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
        IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
        IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (K.comap (ofInfinite F G).toMonoidHom) rho φ →
        ∃ (Γ : ∀ J : StandardIndex F G 𝓕.i 𝓕.ν, (AdelicGroupPoints F (𝓕.M J) → ℂ) →
            AdelicGroupPoints F G → ComplexCharacterParameter F P → ℂ)
          (D : ∀ J : StandardIndex F G 𝓕.i 𝓕.ν, (AdelicGroupPoints F (𝓕.M J) → ℂ) →
            AdelicGroupPoints F G → Set (ComplexCharacterParameter F P)),
          (∀ J ψ, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
            IsMeromorphicInCoordinatesOn (Γ J ψ g) (D J ψ g) ∧
            ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
              Γ J ψ g lam = 𝓕.leviPairing J (𝓕.constantTerm J (hK.eisensteinSeries φ lam)) g ψ) ∧
          ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
            ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ)),
              (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧ IsOpen W ∧ s₀ ∈ W ∧
              ∀ J ψ, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
                ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
                  ∀ s ∈ W, e s ∈ D J ψ g →
                    h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m *
                      Γ J ψ g (e s)

end Langlands.Global
