import Langlands.Global.AdelicComplexParameters
import Langlands.Global.AdelicParabolicQuotient
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicParabolicModulus
import Langlands.GroupScheme.Lie.AdjointDeterminantCharacter
import Langlands.Automorphic.GroupSchemeInvariantForms

/-! # Square-integrable automorphic forms on `A_M U(𝔸) M(F) \ G(𝔸)`

Lapid 2011, §2 (p.311): the spaces `A^n_P` and `A^2_P`, the parameter `ρ_P`, and the imaginary
parameters `i𝔞_P^*`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

section Parameters

variable (F : Type u) [Field F] [NumberField F] (P : GroupScheme (Spec (CommRingCat.of F)))

/-- The real-linear map `μ ↦ iμ` from `X^*(P) ⊗ ℝ` to `X^*(P) ⊗ ℂ`; its image is the space of
imaginary parameters `i𝔞_P^*`. -/
def imaginaryParameter : RealCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
  AlgebraTensorModule.map (LinearMap.toSpanSingleton ℝ ℂ Complex.I) LinearMap.id

variable [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]

/-- The parameter `2ρ_P = 1 ⊗ det(Ad | Lie P)` of the rational character `det(Ad | Lie P)`, so
that `m^{2ρ_P}` is the normalized idele norm of `det(Ad(m) | Lie P)`. -/
def modulusParameter : ComplexCharacterParameter F P :=
  (1 : ℂ) ⊗ₜ[ℤ] Lie.adjointDeterminantCharacter P

/-- The parameter `ρ_P = ½ ⊗ det(Ad | Lie P)`. -/
def halfModulusParameter : ComplexCharacterParameter F P :=
  (1 / 2 : ℂ) ⊗ₜ[ℤ] Lie.adjointDeterminantCharacter P

end Parameters

section Forms

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

/-- Lapid's condition defining `A^n_P` inside `A_P`: `φ(a g) = δ_P(a)^{1/2} φ(g)` for every
`a` in the split component `A_M` of `M(𝔸)` and every `g ∈ G(𝔸)`, with
`δ_P(a)^{1/2} = a^{ρ_P}`. -/
def IsSplitComponentEquivariant (p : P ⟶ G) (l : M ⟶ P) (φ : AdelicGroupPoints F G → ℂ) :
    Prop :=
  ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F M, ∀ g : AdelicGroupPoints F G,
    φ (map F P G p (map F M P l a) * g) =
      parameterPower F P (halfModulusParameter F P) (map F M P l a) * φ g

/-- Lapid's space `A^2_P`: `φ` is an automorphic form on `U(𝔸) M(F) \ G(𝔸)` (for the
archimedean part of `K` and the matrix embedding `rho`), it satisfies the `A^n_P` condition,
and `∫_{A_M U(𝔸) M(F) \ G(𝔸)} |φ|² < ∞`, written in Iwasawa coordinates as the integrability
of `(k, m) ↦ δ_P(m)⁻¹ |φ(m k)|²` on `K × [M]`, `[M] = A_M M(F) \ M(𝔸)`. -/
def IsSquareIntegrableInducedForm (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ ∧
    IsSplitComponentEquivariant p l φ ∧
    Integrable (fun x : K × RestrictionSplitCentre.CanonicalQuotient F M =>
        ‖parameterPower F P (-modulusParameter F P) (map F M P l x.2.out)‖ *
          ‖φ (map F P G p (map F M P l x.2.out) * (x.1 : AdelicGroupPoints F G))‖ ^ 2)
      ((compactHaarProbability F G K hKc).prod (RestrictionSplitCentre.canonicalMeasure F M))

end Forms

end Langlands.Global.AdelicGroupPoints
