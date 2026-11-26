import Langlands.Global.Factors.CuspidalPairLineRegularity
import Langlands.Global.AdelicEisensteinConvergenceProof

/-! # Normal convergence of the cuspidal-pair Eisenstein series for large `Re s`

The Library's convergence theorem `eisensteinAbsoluteConvergence` for group-scheme Eisenstein
series applies to the cuspidal-pair Eisenstein series through the comparison of
`CuspidalPairSchemeComparisonStatement` and the regularity of `CuspidalPairLineRegularityStatement`.
See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions PrimitiveAdelicHeight

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : Automorphic.CuspidalOperatorRealization F r}
  {T' : Automorphic.CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}

/-- The terms of the matrix Eisenstein sum, at the representatives of the matrix cosets matched
with the scheme cosets, are the scheme Eisenstein terms. -/
theorem matrixTerm_parabolicCosetsEquiv (hφ : IsSection T T' φ) (s : ℂ)
    (g : AdelicGroupPoints F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)))
    (c : ParabolicRationalCosets F (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t)))) :
    φ (AdelicGL.rational F (r + t + 2) (Quotient.out (parabolicCosetsEquiv F r t c)) *
        adelicHomeomorph F (r + t + 2) g) *
      heightPower F r t s (AdelicGL.rational F (r + t + 2)
        (Quotient.out (parabolicCosetsEquiv F r t c)) * adelicHomeomorph F (r + t + 2) g) =
      (isIwasawaCompact_blockParabolic F (blockShape r t)).eisensteinTerm
        (φ ∘ adelicHomeomorph F (r + t + 2)) (s • lineParameter F r t) g c := by
  let f : RationalGL F (r + t + 2) → ℂ := fun y =>
    φ (AdelicGL.rational F (r + t + 2) y * adelicHomeomorph F (r + t + 2) g) *
      heightPower F r t s (AdelicGL.rational F (r + t + 2) y * adelicHomeomorph F (r + t + 2) g)
  have hf : ∀ c0 ∈ (blockShape r t).parabolic F, ∀ y, f (c0 * y) = f y := by
    intro c0 hc0 y
    simp only [f, map_mul, mul_assoc]
    rw [isSection_rational_mul hφ c0 hc0, heightPower_rational_mul s c0 hc0]
  have hq : (Quotient.mk _ (Quotient.out (parabolicCosetsEquiv F r t c)) :
      Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F))) =
      Quotient.mk _ (rationalPointsEquiv F r t (Quotient.out c)) := by
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  have hsplit : rationalPointsEquiv F r t (Quotient.out c) =
      (rationalPointsEquiv F r t (Quotient.out c) *
        (Quotient.out (parabolicCosetsEquiv F r t c))⁻¹) *
        Quotient.out (parabolicCosetsEquiv F r t c) := by group
  change f _ = _
  rw [← hf _ hrel, ← hsplit]
  simp only [f, rational_rationalPointsEquiv, ← map_mul]
  rw [heightPower_eq_schemeHeightPower]
  rfl

section Convergence

local instance convGLAffine (n : ℕ) : IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance convGLAffineHom (n : ℕ) :
    IsAffineHom (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  isAffineHom_groupScheme (n := Fin n) (R := CommRingCat.of F)

local instance convParabolicAffine :
    IsAffine (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  blockParabolic_isAffine F (blockShape r t)

local instance convParabolicClosed :
    IsClosedImmersion (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))

local instance convTorusMono :
    Mono (blockRootData F (blockShape r t)).root.data.i.hom.hom.left :=
  (blockRootData F (blockShape r t)).torus_mono

local instance convFactorMono :
    Mono (CommGroupScheme.groupHom (blockRootData F (blockShape r t)).root.data.f).hom.hom.left :=
  (blockRootData F (blockShape r t)).factor_mono

local instance convWeylFinite :
    Fintype (relativeWeylGroup (blockRootData F (blockShape r t)).root.data.i) :=
  @Fintype.ofFinite _ (blockRootData F (blockShape r t)).finite_weylGroup

/-- **Absolute convergence.** For a section of the cuspidal pair there is `σ` such that the terms
of the Eisenstein sum are dominated by one summable function on `P(F) \ GL_N(F)`, uniformly for
`g` in a compact set and `s` in a compact set in the half-plane `Re s > σ`. -/
theorem exists_summable_eisensteinTerm_bound (hφ : IsSection T T' φ) :
    ∃ σ : ℝ, ∀ C : Set (AdelicGL F (r + t + 2)), IsCompact C → ∀ Λ : Set ℂ, IsCompact Λ →
      (∀ s ∈ Λ, σ < s.re) →
      ∃ b : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)) → ℝ,
        Summable b ∧ ∀ c, ∀ g ∈ C, ∀ s ∈ Λ,
          ‖φ (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g) *
            heightPower F r t s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g)‖ ≤ b c := by
  have hG := isConnectedReductive_generalLinear F (Fin (r + t + 2))
  have hs := hG.smoothDimension_spec
  have hc := adelicDifferentialCommutator_of_smooth F
    (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hs
  have hrho : IsClosedSubgroup (MatrixRepresentation.standard (Fin (r + t + 2))
      (CommRingCat.of F)) := by
    change IsClosedImmersion (𝟙 (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)).X.left)
    infer_instance
  obtain ⟨R, hR⟩ := eisensteinAbsoluteConvergence F (groupScheme (Fin (r + t + 2))
    (CommRingCat.of F)) _ _ _ (blockRootData F (blockShape r t)).A
    (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F) (blockShapeWeight (blockShape r t)))
    (blockUnipotentInclusion F (blockShape r t)) (blockLeviInclusion F (blockShape r t))
    (blockRootData F (blockShape r t)).a (blockRootData F (blockShape r t)).root
    (blockRootData F (blockShape r t)).splitComponent (blockRootData F (blockShape r t)).splitTorus
    hG (blockUnipotentInclusion_isLeviGeometricUnipotentRadical F (blockShape r t))
    (standardCompactPoints F (r + t + 2)) (isIwasawaCompact_blockParabolic F (blockShape r t))
    (MatrixRepresentation.standard (Fin (r + t + 2)) (CommRingCat.of F)) hs hc
    (φ ∘ adelicHomeomorph F (r + t + 2)) (standardCompactPoints_isMaximalCompact F (r + t + 2))
    hrho (isAutomorphicFunctionOn_of_isSection hφ hs hc)
  obtain ⟨σ, hσ⟩ := exists_isRegularParameter_lineParameter F r t R
  refine ⟨σ, fun C hC Λ hΛ hΛσ => ?_⟩
  let e := (blockRootData F (blockShape r t)).parameterCoordinates
  let v := e.symm (lineParameter F r t)
  have hev : ∀ s : ℂ, e (s • v) = s • lineParameter F r t := fun s => by
    rw [map_smul, LinearEquiv.apply_symm_apply]
  have hC' : IsCompact ((adelicHomeomorph F (r + t + 2)).symm '' C) :=
    hC.image (adelicHomeomorph F (r + t + 2)).symm.continuous
  have hΛ' : IsCompact ((fun s : ℂ => s • v) '' Λ) :=
    hΛ.image (continuous_id.smul continuous_const)
  obtain ⟨b, hb, hbound⟩ := hR _ hC' _ e _ hΛ' (by
    rintro _ ⟨s, hsΛ, rfl⟩
    rw [hev]
    exact hσ s (hΛσ s hsΛ))
  refine ⟨fun c => b ((parabolicCosetsEquiv F r t).symm c),
    (parabolicCosetsEquiv F r t).symm.summable_iff.mpr hb, fun c g hg s hsΛ => ?_⟩
  have key := matrixTerm_parabolicCosetsEquiv hφ s ((adelicHomeomorph F (r + t + 2)).symm g)
    ((parabolicCosetsEquiv F r t).symm c)
  rw [Equiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply] at key
  rw [key, ← hev]
  exact hbound _ _ ⟨g, hg, rfl⟩ _ ⟨s, hsΛ, rfl⟩

end Convergence

/-- **Normal convergence of the cuspidal-pair Eisenstein series** (Mœglin–Waldspurger II.1.5
on Shahidi's line). For a number field `F : Type u` with compact adele quotient, actual cuspidal
realizations `T`, `T'` and a section `φ` of the cuspidal pair, there is `σ` such that for every
compact set `C` of `GL_N(𝔸)` and every compact set `Λ` of `s` with `Re s > σ`, one summable
function on `P(F) \ GL_N(F)` dominates the terms `φ(γ g) H(γ g)^s` of `eisensteinSeries` (at the
chosen representatives `γ` of the cosets) for all `g ∈ C` and `s ∈ Λ`. -/
def CuspidalPairEisensteinNormalConvergenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r t : ℕ)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (φ : AdelicGL F (r + t + 2) → ℂ),
    IsSection T T' φ →
      ∃ σ : ℝ, ∀ C : Set (AdelicGL F (r + t + 2)), IsCompact C → ∀ Λ : Set ℂ, IsCompact Λ →
        (∀ s ∈ Λ, σ < s.re) →
        ∃ b : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)) → ℝ,
          Summable b ∧ ∀ c, ∀ g ∈ C, ∀ s ∈ Λ,
            ‖φ (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g) *
              heightPower F r t s (AdelicGL.rational F (r + t + 2) (Quotient.out c) * g)‖ ≤ b c

theorem cuspidalPairEisensteinNormalConvergence :
    CuspidalPairEisensteinNormalConvergenceStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ hφ => exists_summable_eisensteinTerm_bound hφ

end Langlands.Global.CuspidalPairEisenstein
