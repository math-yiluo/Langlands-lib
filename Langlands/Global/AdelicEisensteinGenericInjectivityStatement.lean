import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Generic injectivity of Eisenstein series

Bernstein–Lapid, formula (8.4) (Remark at the end of §8.5), number field case: on the span of
finitely many automorphic forms, `φ ↦ E(φ, λ)` is injective for generic `λ`, stated for any
pointwise meromorphic continuations of the Eisenstein series. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Generic injectivity of Eisenstein series on finite-dimensional spaces (Bernstein–Lapid,
formula (8.4) in the Remark at the end of §8.5, number field case). Let `P = MU` be a
parabolic with presentation `r`, `K` a maximal compact subgroup with `P(𝔸)K = G(𝔸)`, and
`φ i ∈ 𝒜_P` for `i` in a finite index type `Idx`. Take any functions `E i` and set `D` such
that, for every `i` and `g`, `λ ↦ E i λ g` is meromorphic in linear coordinates with domain
of holomorphy `D`, and `E i λ = E(φ i, λ)` for `Re λ` sufficiently regular (a bound for each
`i`). Then in every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` there is an open dense
set `O` of parameters such that, for `s ∈ O` with `e s ∈ D`, every relation
`∑ i, c i • E i (e s) = 0` among the continued series forces `∑ i, c i • φ i = 0`. -/
def EisensteinGenericInjectivityStatement : Prop :=
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
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      ∀ (Idx : Type) [Fintype Idx] (φ : Idx → AdelicGroupPoints F G → ℂ),
        (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (K.comap (ofInfinite F G).toMonoidHom) rho (φ i)) →
        ∀ (E : Idx → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
          (D : Set (ComplexCharacterParameter F P)),
          (∀ i g, IsMeromorphicInCoordinatesOn (fun lam => E i lam g) D) →
          (∀ i, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
            E i lam = hK.eisensteinSeries (φ i) lam) →
          ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
            ∃ O : Set (Fin n → ℂ), IsOpen O ∧ Dense O ∧ ∀ s ∈ O, e s ∈ D →
              ∀ c : Idx → ℂ, (∀ g, ∑ i, c i * E i (e s) g = 0) → ∀ g, ∑ i, c i * φ i g = 0

end Langlands.Global
