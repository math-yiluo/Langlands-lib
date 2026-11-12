import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Completeness of wave packets of Eisenstein series

Delorme 2023, Theorem 7.9 (the surjectivity half of Langlands' spectral decomposition): the
wave packets `Θ_{P,φ}`, for all parabolics `P` and all `φ ∈ W_P`, span a dense subspace of
`L²(G(F) \ G(𝔸))`. Equivalently, a square-integrable function orthogonal to all of them is
zero. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Completeness of wave packets (Delorme 2023, Theorem 7.9, with Lapid 2011, Theorem 2). Let
`G` be connected reductive over a number field and `K` a maximal compact subgroup of `G(𝔸)`
with `P₀(𝔸)K = G(𝔸)` for some minimal parabolic `P₀`. Let `f ∈ L²(G(F) \ G(𝔸))` be orthogonal
to every wave packet `Θ = ∫ ∑ j, c j x • E(v j, i e(x)) dx`, where `P = MU` is a parabolic with a
presentation `r`, `e` are coordinates on `X^*(P) ⊗ ℝ`, `v j ∈ A^2_P`, `c j` are smooth and
compactly supported, and `E j` are meromorphic continuations of the Eisenstein series `E(v j, λ)`
holomorphic near `i𝔞_P^*`. Then `f = 0` almost everywhere. -/
def WavePacketCompletenessStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ f : RationalQuotient F G → ℂ, MemLp f 2 μG →
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
        (A : CommGroupScheme (Spec (CommRingCat.of F)))
        [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
        [IsAffine U.X.left]
        (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
        [IsClosedImmersion (iU ≫ p).hom.hom.left]
        (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
        [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
        [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
        (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
        haveI : LocallyOfFiniteType P.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
        LeviSubgroup.IsGeometricUnipotentRadical iU →
        ∀ (hK : IsIwasawaCompact p K) {n : ℕ}
          (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
          (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
          (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
          (D : Set (ComplexCharacterParameter F P)),
          (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
          (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ HasCompactSupport (c j)) →
          Set.range (imaginaryParameter F P) ⊆ D →
          (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
          (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
            E j lam = hK.eisensteinSeries (v j) lam) →
          ∫ y, f y * (starRingEnd ℂ)
              (∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) y.out
                ∂(spectralMeasure n)) ∂μG = 0) →
      f =ᵐ[μG] 0

end Langlands.Global
