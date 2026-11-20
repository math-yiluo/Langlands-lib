import Langlands.Global.AdelicInducedInnerProduct

/-! # Positivity of the inner product `(·,·)_P` on finite families in `A^2_P`

Lapid 2011, §2 (p.311): `(φ, ψ)_P = ∫_{A_M U(𝔸) M(F) \ G(𝔸)} φ ψ̄` is an inner product on
`A^2_P`. For a finite family `φ i` in `A^2_P` and coefficients `x i` this says that the Gram
form `∑ i, ∑ i', x i · conj (x i') · (φ i, φ i')_P` is a nonnegative real number, which vanishes
exactly when `∑ i, x i • φ i = 0`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ComplexOrder

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Positive definiteness of the inner product of Lapid 2011, §2 (p.311), on `A^2_P`, in Gram
form. Let `P = MU` be a parabolic of a connected reductive `G` over a number field with rational
Levi `l` and unipotent radical `iU` (`M ⋉ U ≅ P`), `K` a compact subgroup with `P(𝔸)K = G(𝔸)`,
`μ_M` a Haar measure on `M(𝔸)`, `e` coordinates on `X^*(P) ⊗ ℝ` and `β` a continuous compactly
supported weight with `∫ β = 1`, which define `(·,·)_P = inducedInnerProduct K hK.isCompact p l
μM e β`. Then for `φ i ∈ A^2_P` (`IsSquareIntegrableInducedForm`) and `x i ∈ ℂ`,
`∑ i, ∑ i', x i · conj (x i') · (φ i, φ i')_P` is a nonnegative real number (`0 ≤` in the order
of `ℂ`), and it is `0` exactly when `∑ i, x i • φ i = 0`. -/
def InducedInnerProductGramStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left],
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsRationalLeviSubgroup l → IsIso (subgroupMultiplication l iU) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure] {n : ℕ}
      (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
    ∀ (m : ℕ) (φ : Fin m → AdelicGroupPoints F G → ℂ),
      (∀ i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (φ i)) →
    ∀ x : Fin m → ℂ,
      0 ≤ ∑ i, ∑ i', x i * (starRingEnd ℂ) (x i') *
          inducedInnerProduct K hK.isCompact p l μM e β (φ i) (φ i') ∧
        (∑ i, ∑ i', x i * (starRingEnd ℂ) (x i') *
            inducedInnerProduct K hK.isCompact p l μM e β (φ i) (φ i') = 0 ↔
          ∑ i, x i • φ i = 0)

end Langlands.Global
