import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Automorphy of pointwise Eisenstein continuations -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- The published local Fréchet-valued continuation implies that every
pointwise meromorphic Eisenstein continuation has automorphic values on
a common open dense subset of its holomorphy domain in each chart. -/
def EisensteinPointwiseContinuationAutomorphyReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{u} →
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
        ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
          ∃ S : Set (Fin n → ℂ), IsOpen S ∧ Dense S ∧ S ⊆ e ⁻¹' DP ∧
            ∀ s ∈ S, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
              (K.comap (ofInfinite F G).toMonoidHom) rho (EP (e s))

end Langlands.Global
