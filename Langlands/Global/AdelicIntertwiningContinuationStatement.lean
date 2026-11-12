import Langlands.Global.AdelicIntertwiningConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Meromorphic continuation of intertwining operators

Bernstein–Lapid, Theorem 2.3 (3), number field case: `λ ↦ M(w, λ)φ` takes values in a
finite-dimensional subspace of `𝒜_Q` and continues meromorphically to `X^*(P) ⊗ ℂ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Meromorphic continuation of intertwining operators (Bernstein–Lapid, Theorem 2.3 (3),
number field case). In the setting of `IntertwiningAbsoluteConvergenceStatement`, assume
moreover that `P(𝔸)K = Q(𝔸)K = G(𝔸)` and let `π' : Q → M'` be a retraction of `l'`. Then there
are finitely many automorphic forms `ψ i` on `V(𝔸)M'(F) \ G(𝔸)` and scalar functions `coeff i` on
`X^*(P) ⊗ ℂ`, meromorphic in linear coordinates, with
`M(w, λ)φ = ∑ i, coeff i λ • ψ i` for `Re λ` sufficiently regular. -/
def IntertwiningMeromorphicContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left] (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
        (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
          (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i)) ∧
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
        ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          ∀ g : AdelicGroupPoints F G,
            hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g

end Langlands.Global
