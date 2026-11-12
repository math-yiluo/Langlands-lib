import Langlands.Global.AdelicIntertwiningOperator
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Singularities of Eisenstein series and intertwining operators along root hyperplanes

Bernstein–Lapid, Theorem 2.3 (6), number field case, in the local form of the Corollary in
§8.6: near every point `λ₀`, a product of powers of the linear forms `λ ↦ ⟨λ - λ₀, β^∨⟩`,
`β` a root of the split component in the unipotent radical, removes the singularities. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The real linear form `x ↦ B(x|_A, β)` on `X^*(P) ⊗ ℝ`, for a character `β` of the split
component `A`, where `B` is the Weyl-induced positive form of the presentation. -/
def _root_.Langlands.GroupScheme.ParabolicRootPresentation.realRootFunctional
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (β : characterLattice A) :
    RealCharacterParameter F P →ₗ[ℝ] ℝ :=
  ((Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i).flip
    ((1 : ℝ) ⊗ₜ[ℤ] β)) ∘ₗ realParameterRestriction (a ≫ l)

/-- The complex linear form `λ ↦ B(λ|_A, β)` on `X^*(P) ⊗ ℂ`: the complex-linear extension of
`realRootFunctional`, so `s ⊗ χ ↦ s · B((1 ⊗ χ)|_A, β)`. Its zero set is the root hyperplane
`⟨λ, β^∨⟩ = 0`. -/
def _root_.Langlands.GroupScheme.ParabolicRootPresentation.rootFunctional
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (β : characterLattice A) :
    ComplexCharacterParameter F P →ₗ[ℂ] ℂ :=
  AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ (GroupScheme.rationalCharacters P →ₗ[ℤ] ℂ)
      ((Complex.ofRealHom.toAddMonoidHom.comp
        ((r.realRootFunctional hA hT β).toAddMonoidHom.comp
          (TensorProduct.mk ℤ ℝ (GroupScheme.rationalCharacters P) 1).toAddMonoidHom)).toIntLinearMap))

omit [NumberField F] in
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.rootFunctional_tmul
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (β : characterLattice A)
    (s : ℂ) (χ : GroupScheme.rationalCharacters P) :
    r.rootFunctional hA hT β (s ⊗ₜ[ℤ] χ) =
      s * (r.realRootFunctional hA hT β ((1 : ℝ) ⊗ₜ[ℤ] χ) : ℂ) :=
  rfl

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Singularities of intertwining operators lie along root hyperplanes (Bernstein–Lapid,
Theorem 2.3 (6), first sentence, number field case). In the setting of the intertwining
continuation statement, let `ψ i` and meromorphic `coeff i` (domain `D`) satisfy
`M(w, λ)φ = ∑ i, coeff i λ • ψ i` for `Re λ` sufficiently regular. Then near every point
`λ₀ = e s₀` (in any linear coordinates `e`) there are finitely many roots `β` of `A` in the
unipotent radical of `P` and an exponent `m` such that, for every `g`,
`λ ↦ (∏ β, B(λ - λ₀, β))^m · ∑ i, coeff i λ * ψ i g` agrees on `D` with a function holomorphic
on one neighborhood of `λ₀`. -/
def IntertwiningRootHyperplaneStatement : Prop :=
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
      ∀ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
        (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g) →
      ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
        ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ)),
          (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧ IsOpen W ∧ s₀ ∈ W ∧
          ∀ g : AdelicGroupPoints F G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
            ∀ s ∈ W, e s ∈ D →
              h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m *
                ∑ i, coeff i (e s) * ψ i g

/-- Singularities of Eisenstein series lie along root hyperplanes (Bernstein–Lapid,
Theorem 2.3 (6), second sentence, in the local form of the Corollary in §8.6, number field
case). In the setting of the Eisenstein convergence statement, let `EP` be meromorphic in `λ`
at every point `g` with one domain `DP` and equal to `E(φ, λ)` for `Re λ` sufficiently regular.
Then near every point `λ₀ = e s₀` there are finitely many roots `β` of `A` in the unipotent
radical and an exponent `m` such that, for every `g`, `λ ↦ (∏ β, B(λ - λ₀, β))^m · EP λ g`
agrees on `DP` with a function holomorphic on one neighborhood of `λ₀`. -/
def EisensteinRootHyperplaneStatement : Prop :=
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
        ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ)),
          (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧ IsOpen W ∧ s₀ ∈ W ∧
          ∀ g : AdelicGroupPoints F G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
            ∀ s ∈ W, e s ∈ DP →
              h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m * EP (e s) g

/-- Bernstein–Lapid, Theorem 2.3 (6): the singularities of `M(w, λ)φ` and of `E(φ, λ)` lie
along root hyperplanes. -/
def RootHyperplaneSingularitiesStatement : Prop :=
  IntertwiningRootHyperplaneStatement.{u} ∧ EisensteinRootHyperplaneStatement.{u}

end Langlands.Global
