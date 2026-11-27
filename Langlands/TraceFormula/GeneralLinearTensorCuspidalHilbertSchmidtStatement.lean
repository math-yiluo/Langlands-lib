import Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaStatement

/-!
# Hilbert–Schmidt cuspidal operators of tensor test functions on `GL_n`

This module states, without proof, that for `GL_n` over a number field the cuspidal operator
`R_cusp(f)` of a tensor test function `f = a ⊗ b` is Hilbert–Schmidt. Here `a` is a smooth
compactly supported function on the archimedean group `GL_n(F_∞)` and `b` is a locally
constant compactly supported function on the finite adelic group. The cuspidal operator is the
integrated right action on the closed cuspidal subspace of `L²` of the positive rational
quotient. The proposition is the hypothesis on tensor test functions of
`GeneralLinearTensorSimpleTraceFormulaStatement`.

Source: Getz–Hahn 2024, Theorem 9.1.2 and its proof (printed p. 241 and §9.5). See
`GeneralLinearTensorCuspidalHilbertSchmidtStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

local instance generalLinearTensorHSIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearTensorHSSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The `GL_n` group scheme over `F`, for the bound variables `F` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- **Hilbert–Schmidt cuspidal operators of tensor test functions** (Getz–Hahn, Theorem 9.1.2
and its proof). Let `F` be a number field and `n : ℕ`, with the Library's data for the
positive rational quotient of `GL_n` over `F`: the parabolic classification `hPD`, connected
reductivity `hG`, a central split torus `T` with morphism `i` satisfying the character
conditions `hi`, an isomorphism `e` with a split torus and centrality `hc`, and right
invariance of Haar measure on the norm-one adelic subgroup. Let `μG` be Haar measure on
`GL_n(𝔸_F)`. For every smooth compactly supported archimedean kernel `a` and every compactly
supported locally constant finite adelic test `b`, read on the group-scheme points through
`GeneralLinearGroupPoints.adelicHomeomorph`, and every integrability proof `h`, the integrated
action of `a ⊗ b` on the full cuspidal subspace is Hilbert–Schmidt. -/
def GeneralLinearTensorCuspidalHilbertSchmidtStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F GLₙ)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F GLₙ) := Measure.haar
    ∀ (a : ArchimedeanGL.SmoothCompactKernel F n) (b : CompactFiniteGLTest F n)
      (h : Integrable (fun g => adelicTestTensor F n a b
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)) μG),
      IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction F GLₙ hPD hG T i hi I e hc μG
        (fun g => adelicTestTensor F n a b (GeneralLinearGroupPoints.adelicHomeomorph F n g))
        h)

end Langlands.TraceFormula
