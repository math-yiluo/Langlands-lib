import Langlands.Global.AdelicSpectralTransformSpaces

/-! # Square integrability of restrictions of elements of `A^2_P`

For `φ ∈ A^2_P` (Lapid 2011, §2), the restriction `(k, m) ↦ φ(m k)` to
`K × M(F) \ M(𝔸)` is square integrable for the measure `β(y(m)) δ_P(m)⁻¹ dk dm` of
`inducedL2Measure`, when `β` is continuous, nonnegative and compactly supported: this is the
statement that `φ` defines an element of Arthur's Hilbert space `H_P` (Arthur 2005, §7, p.32). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Elements of `A^2_P` have square-integrable restrictions (Lapid 2011, §2, p.311; Arthur 2005,
§7, p.32). For a presented parabolic `P = MU` of a connected reductive `G` over a number field
with Levi projection `π`, a maximal compact subgroup `K` with `P(𝔸)K = G(𝔸)`, a Haar measure
`μ_M` compatible with the Iwasawa decomposition, coordinates `e` on `X^*(P) ⊗ ℝ` and a continuous,
nonnegative, compactly supported weight `β`, every `φ ∈ A^2_P` restricts to an element
`(k, m) ↦ φ(m k)` of `L²(K × M(F) \ M(𝔸), β(y(m)) δ_P(m)⁻¹ dk dm)`. -/
def InducedRestrictionMemLpStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsIso (subgroupMultiplication l iU) → l ≫ π = 𝟙 M →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → (∀ y, 0 ≤ β y) →
    ∀ φ : AdelicGroupPoints F G → ℂ,
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      MemLp (inducedRestriction K p l φ) 2 (inducedL2Measure K hK.isCompact l μM e β)

end Langlands.Global
