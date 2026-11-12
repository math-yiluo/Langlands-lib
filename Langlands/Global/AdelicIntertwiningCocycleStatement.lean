import Langlands.Global.AdelicIntertwiningContinuationStatement

/-! # Cocycle relation of intertwining operators

Bernstein–Lapid, Theorem 2.3 (5), number field case:
`M(w'w, λ) = M(w', wλ) ∘ M(w, λ)` as meromorphic functions of `λ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Cocycle relation of intertwining operators (Bernstein–Lapid, Theorem 2.3 (5), number field
case). Let `P = MU` and `Q = M'V` be standard parabolics with presentations `r` and `r'`,
`Q'' = M''V''` a parabolic, `(w, c)` an element of `W(P, Q)` and `(w', c')` an element of
`W(Q, Q'')`, so that `(w'w, c' ≫ c)` is an element of `W(P, Q'')`. Let `K` be a maximal compact
subgroup with `P(𝔸)K = Q(𝔸)K = Q''(𝔸)K = G(𝔸)` and `φ ∈ 𝒜_P`, and take

* `ψ i ∈ 𝒜_Q` and meromorphic `coeff i` (domain `D`) with `M(w, λ)φ = ∑ i, coeff i λ • ψ i`
  for `Re λ` sufficiently regular;
* functions `χ j` and meromorphic `coeff' i j` on `X^*(Q) ⊗ ℂ` (domain `D'`) with
  `M(w', μ)(ψ i) = ∑ j, coeff' i j μ • χ j` for `Re μ` sufficiently regular;
* functions `χ'' j` and meromorphic `coeff'' j` (domain `D''`) with
  `M(w'w, λ)φ = ∑ j, coeff'' j λ • χ'' j` for `Re λ` sufficiently regular.

Then `∑ j, coeff'' j λ * χ'' j g = ∑ i, coeff i λ * ∑ j, coeff' i j (wλ) * χ j g` whenever
`λ ∈ D ∩ D''` and `wλ ∈ D'`. -/
def IntertwiningCocycleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V Q'' M'' V'' : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    [IsAffine Q''.X.left] [IsAffine V''.X.left]
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
    (q'' : Q'' ⟶ G) [IsClosedImmersion q''.hom.hom.left] (iV'' : V'' ⟶ Q'')
    (l'' : M'' ⟶ Q'') [IsClosedImmersion (iV'' ≫ q'').hom.hom.left] (π'' : Q'' ⟶ M'')
    (w w' : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M) (c' : M'' ⟶ M'),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsParabolicSubgroup q'' → LeviSubgroup.IsGeometricUnipotentRadical iV'' →
    IsRationalLeviSubgroup l'' → IsIso (subgroupMultiplication l'' iV'') →
    l' ≫ π' = 𝟙 M' → l'' ≫ π'' = 𝟙 M'' →
    IsWeylConjugation p l q l' w c → IsWeylConjugation q l' q'' l'' w' c' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) (hK'' : IsIwasawaCompact q'' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∀ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
        (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
          (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i)) →
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g) →
      ∀ (k' : ℕ) (χ : Fin k' → AdelicGroupPoints F G → ℂ)
        (coeff' : Fin k → Fin k' → ComplexCharacterParameter F Q → ℂ)
        (D' : Set (ComplexCharacterParameter F Q)),
        (∀ i j, IsMeromorphicInCoordinatesOn (coeff' i j) D') →
        (∀ i, ∃ R : ℝ, ∀ mu, r'.IsRegularParameter hA' hT' R mu → ∀ g,
          hK'.intertwiningOperator hK'' iV l' iV'' c' π'' w' (ψ i) mu g =
            ∑ j, coeff' i j mu * χ j g) →
      ∀ (k'' : ℕ) (χ'' : Fin k'' → AdelicGroupPoints F G → ℂ)
        (coeff'' : Fin k'' → ComplexCharacterParameter F P → ℂ)
        (D'' : Set (ComplexCharacterParameter F P)),
        (∀ j, IsMeromorphicInCoordinatesOn (coeff'' j) D'') →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK'' iU l iV'' (c' ≫ c) π'' (w' * w) φ lam g =
            ∑ j, coeff'' j lam * χ'' j g) →
      ∀ lam ∈ D ∩ D'', weylParameter l c π' lam ∈ D' → ∀ g : AdelicGroupPoints F G,
        ∑ j, coeff'' j lam * χ'' j g =
          ∑ i, coeff i lam * ∑ j, coeff' i j (weylParameter l c π' lam) * χ j g

end Langlands.Global
