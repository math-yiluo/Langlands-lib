import Langlands.Global.AdelicRootHyperplaneStatement

/-! # Continuations of intertwining operators and Eisenstein series with root-hyperplane
singularities

Bernstein–Lapid, Theorem 2.3 (3), (1) and (6), number field case, with the local form of the
Corollary in §8.6: there is one meromorphic continuation of `M(w, λ)φ`, and one of `E(φ, λ)`,
whose singularities near every point `λ₀` are removed by a power of the product of the linear
forms `λ ↦ B(λ - λ₀, β)`, `β` a root of the split component in the unipotent radical. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- A continuation of intertwining operators with singularities along root hyperplanes
(Bernstein–Lapid, Theorem 2.3 (3) and (6), first sentence, number field case). In the setting
of `IntertwiningRootHyperplaneStatement`, there are finitely many functions `ψ i` on `G(𝔸)`
and scalar functions `coeff i`, meromorphic in linear coordinates with one domain `D`, such
that `M(w, λ)φ g = ∑ i, coeff i λ * ψ i g` for `Re λ` sufficiently regular, and near every
point `λ₀ = e s₀` (in any linear coordinates `e`) there are finitely many roots `β` of `A` in
the unipotent radical of `P` and an exponent `m` such that, for every `g`,
`λ ↦ (∏ β, B(λ - λ₀, β))^m · ∑ i, coeff i λ * ψ i g` agrees on `D` with a function
holomorphic on one neighborhood of `λ₀`. -/
def IntertwiningRootHyperplaneContinuationStatement : Prop :=
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
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g) ∧
        ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
          ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ)),
            (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧ IsOpen W ∧ s₀ ∈ W ∧
            ∀ g : AdelicGroupPoints F G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
              ∀ s ∈ W, e s ∈ D →
                h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m *
                  ∑ i, coeff i (e s) * ψ i g

/-- A continuation of Eisenstein series with singularities along root hyperplanes
(Bernstein–Lapid, Theorem 2.3 (1) and (6), second sentence, in the local form of the
Corollary in §8.6, number field case). In the setting of `EisensteinRootHyperplaneStatement`,
there is a function `EP` of `λ` with values in the functions on `G(𝔸)`, meromorphic in `λ` in
linear coordinates at every point `g` with one domain `DP`, equal to `E(φ, λ)` for `Re λ`
sufficiently regular, such that near every point `λ₀ = e s₀` there are finitely many roots `β`
of `A` in the unipotent radical and an exponent `m` such that, for every `g`,
`λ ↦ (∏ β, B(λ - λ₀, β))^m · EP λ g` agrees on `DP` with a function holomorphic on one
neighborhood of `λ₀`. -/
def EisensteinRootHyperplaneContinuationStatement : Prop :=
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
      ∃ (EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (DP : Set (ComplexCharacterParameter F P)),
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP) ∧
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          EP lam = hK.eisensteinSeries φ lam) ∧
        ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
          ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ)),
            (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧ IsOpen W ∧ s₀ ∈ W ∧
            ∀ g : AdelicGroupPoints F G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
              ∀ s ∈ W, e s ∈ DP →
                h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m * EP (e s) g

/-- Both continuation statements of this module: Bernstein–Lapid, Theorem 2.3 (6), for one
continuation of `M(w, λ)φ` and one of `E(φ, λ)`. -/
def RootHyperplaneContinuationStatement : Prop :=
  IntertwiningRootHyperplaneContinuationStatement.{u} ∧
    EisensteinRootHyperplaneContinuationStatement.{u}

end Langlands.Global
