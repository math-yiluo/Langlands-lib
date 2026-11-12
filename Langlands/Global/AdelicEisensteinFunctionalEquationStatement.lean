import Langlands.Global.AdelicIntertwiningContinuationStatement

/-! # Functional equation of Eisenstein series

Bernstein–Lapid, Theorem 2.3 (4), number field case:
`E(M(w, λ)φ, wλ) = E(φ, λ)` as meromorphic functions of `λ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Functional equation of Eisenstein series (Bernstein–Lapid, Theorem 2.3 (4), number field
case). Let `P = MU` and `Q = M'V` be standard parabolics with presentations `r` and `r'`,
`(w, c)` an element of `W(P, Q)`, `π'` the Levi projection of `Q`, and `K` a maximal compact
subgroup with `P(𝔸)K = Q(𝔸)K = G(𝔸)`. Let `φ ∈ 𝒜_P`, and take

* `EP`, meromorphic in `λ` at each point `g` with one domain of holomorphy `DP`, equal to
  `E(φ, λ)` for `Re λ` sufficiently regular;
* `ψ i ∈ 𝒜_Q` and meromorphic `coeff i` (domain `D`) with `M(w, λ)φ = ∑ i, coeff i λ • ψ i`
  for `Re λ` sufficiently regular;
* `EQ i`, meromorphic in `μ ∈ X^*(Q) ⊗ ℂ` at each point with one domain `DQ`, equal to
  `E(ψ i, μ)` for `Re μ` sufficiently regular.

Then `EP λ g = ∑ i, coeff i λ * EQ i (wλ) g` whenever `λ ∈ DP ∩ D` and `wλ ∈ DQ`. -/
def EisensteinFunctionalEquationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iV → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∀ (EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (DP : Set (ComplexCharacterParameter F P)),
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          EP lam = hK.eisensteinSeries φ lam) →
      ∀ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
        (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
          (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i)) →
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g) →
      ∀ (EQ : Fin k → ComplexCharacterParameter F Q → AdelicGroupPoints F G → ℂ)
        (DQ : Set (ComplexCharacterParameter F Q)),
        (∀ i g, IsMeromorphicInCoordinatesOn (fun mu => EQ i mu g) DQ) →
        (∀ i, ∃ R : ℝ, ∀ mu, r'.IsRegularParameter hA' hT' R mu →
          EQ i mu = hK'.eisensteinSeries (ψ i) mu) →
      ∀ lam ∈ DP ∩ D, weylParameter l c π' lam ∈ DQ → ∀ g : AdelicGroupPoints F G,
        EP lam g = ∑ i, coeff i lam * EQ i (weylParameter l c π' lam) g

end Langlands.Global
