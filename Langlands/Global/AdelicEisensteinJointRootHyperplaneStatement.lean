import Langlands.Global.AdelicRootHyperplaneStatement

/-! # Root-hyperplane form of Eisenstein series, jointly in the parameter and the group variable

Bernstein–Lapid, Theorem 2.3 (1) and (6) with the Fréchet formulation of the Corollary in §8.6,
number field case: near every point `λ₀`, a power of the product of the root forms
`λ ↦ B(λ - λ₀, β)` turns the continued Eisenstein series into one function of `(λ, g)` that is
continuous, holomorphic in `λ` and left `G(F)`-invariant in `g`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Root-hyperplane form of Eisenstein series, jointly in `(λ, g)` (Bernstein–Lapid,
Theorem 2.3 (1) and (6), with the Corollary in §8.6, number field case). The data and hypotheses
are those of `EisensteinRootHyperplaneStatement`: `EP` is meromorphic in `λ` at every point `g`
with one domain `DP` and equals `E(φ, λ)` for `Re λ` sufficiently regular. Then near every point
`λ₀ = e s₀` (in any linear coordinates `e`) there are finitely many roots `β` of `A` in the
unipotent radical, each with a nonzero root form `B(·, β)`, an exponent `m`, an open
neighbourhood `W` of `s₀` and one function `h` of `(s, g)` such that `h` is continuous on
`W × G(𝔸)`, holomorphic in `s ∈ W` for every `g`, left invariant under `G(F)` in `g`, and equal
to `(∏ β, B(e s - λ₀, β))^m · EP (e s) g` whenever `e s ∈ DP`. -/
def EisensteinJointRootHyperplaneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
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
      ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
        ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ))
          (h : (Fin n → ℂ) → AdelicGroupPoints F G → ℂ),
          (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧
          (∀ β ∈ S, r.realRootFunctional hA hT β ≠ 0) ∧
          IsOpen W ∧ s₀ ∈ W ∧
          ContinuousOn (fun q : (Fin n → ℂ) × AdelicGroupPoints F G => h q.1 q.2)
            (W ×ˢ Set.univ) ∧
          (∀ g, DifferentiableOn ℂ (fun s => h s g) W) ∧
          (∀ s ∈ W, ∀ c ∈ rationalSubgroup F G, ∀ g, h s (c * g) = h s g) ∧
          ∀ g, ∀ s ∈ W, e s ∈ DP →
            h s g = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m * EP (e s) g

end Langlands.Global
