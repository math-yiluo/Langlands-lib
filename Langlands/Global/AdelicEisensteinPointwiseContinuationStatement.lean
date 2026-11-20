import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Pointwise meromorphic continuation of Eisenstein series

Bernstein–Lapid, Theorem 2.3 (1), number field case, for finite families of automorphic forms
and for scalar values at single points of `G(𝔸)`: the Eisenstein series of finitely many
automorphic forms have pointwise meromorphic continuations with one common domain of
holomorphy. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Pointwise meromorphic continuation of Eisenstein series for a finite family
(Bernstein–Lapid, Theorem 2.3 (1), number field case, evaluated at points of `G(𝔸)`). Let
`P = MU` be a parabolic with presentation `r`, `K` a maximal compact subgroup with
`P(𝔸)K = G(𝔸)`, and `φ i ∈ 𝒜_P` for `i` in a finite index type `Idx`. There are functions
`E i` on `X^*(P) ⊗ ℂ` with values in the functions on `G(𝔸)` and one set `D` such that, for
every `i` and every `g`, `λ ↦ E i λ g` is meromorphic in linear coordinates with domain of
holomorphy `D`, and `E i λ = E(φ i, λ)` for `Re λ` sufficiently regular. -/
def EisensteinPointwiseContinuationStatement : Prop :=
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
        ∃ (E : Idx → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
          (D : Set (ComplexCharacterParameter F P)),
          (∀ i g, IsMeromorphicInCoordinatesOn (fun lam => E i lam g) D) ∧
          ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ i,
            E i lam = hK.eisensteinSeries (φ i) lam

end Langlands.Global
