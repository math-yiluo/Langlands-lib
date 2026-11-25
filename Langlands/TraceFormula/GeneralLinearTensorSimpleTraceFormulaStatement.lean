import Langlands.Analysis.OperatorTrace
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.TraceFormula.CompactSmoothAdelicGLTest
import Langlands.TraceFormula.TwistedOrbital

/-!
# The simple trace formula for `GL_n` on sums of tensor test functions

* `GeneralLinearSimpleTraceExpansion`: the conclusion of `GeneralLinearSimpleTraceFormulaStatement`
  for one integrable function (trace class of `R(f)` and the expansion of its trace into volumes
  times elliptic orbital integrals).
* `GeneralLinearTensorSimpleTraceFormulaStatement`: for a finite sum `f = ∑ⱼ aⱼ ⊗ bⱼ` of tensor test
  functions on `GL_n(𝔸_F)`, under the Hilbert–Schmidt assumption for tensor tests, a local
  vanishing condition on each finite component `bⱼ` and regular ellipticity of the supports at a
  finite place `v`, `f` satisfies the simple trace formula at `v` with one family of
  representatives (`GeneralLinearSimpleTraceExpansion`).
* `GeneralLinearTensorSimpleTracePiecesStatement`: under the same hypotheses, `R(f)` is trace class
  and its trace is the sum of the traces of finitely many convolution pieces, each of which
  satisfies the simple trace formula with its own family of representatives.

Both are proved in `GeneralLinearTensorSimpleTraceFormulaReduction`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

open Langlands.GeneralLinear

local instance generalLinearTensorTraceIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearTensorTraceSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The `GL_n` group scheme over `F`, for the bound variables `F` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- The conclusion of `GeneralLinearSimpleTraceFormulaStatement` for an integrable function `f`
on `GL_n(𝔸_F)` at the finite place `v`: `R(f)` is trace class on `L²([G])`, and its trace is the sum,
over finitely many pairwise non-conjugate rational norm-one points `r j` regular elliptic at `v`
(and containing every conjugacy class that meets the support of `f¹`), of volumes times orbital
integrals of `f¹(x) = ∫ f(a x) da`, for all compatible measures. -/
def GeneralLinearSimpleTraceExpansion (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F GLₙ)).IsMulRightInvariant]
    (v : Langlands.Global.FinitePlace F) (f : AdelicGroupPoints F GLₙ → ℂ)
    (h : Integrable f (Measure.haar : Measure (AdelicGroupPoints F GLₙ))) : Prop :=
  let μG : Measure (AdelicGroupPoints F GLₙ) := Measure.haar
  let fOne : normOneSubgroup F GLₙ → ℂ := fun x =>
    ∫ a, f (positivePointMap F GLₙ T i a * x)
      ∂normalizedPositiveHaarMeasure F GLₙ T i hi I e hc
  IsTraceClass (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG f h) ∧
    ∃ (m : ℕ) (r : Fin m → rationalNormOneSubgroup F GLₙ),
      (∀ j k, IsTwistedConjugate (rationalNormOneSubgroup F GLₙ)
        (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ)
        (r k : normOneSubgroup F GLₙ) → j = k) ∧
      (∀ j, IsRegularElliptic (FiniteAdelicGL.localProjection F n v
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
          ((r j : normOneSubgroup F GLₙ) : AdelicGroupPoints F GLₙ))))) ∧
      (∀ q ∈ rationalNormOneSubgroup F GLₙ,
        (∃ x : normOneSubgroup F GLₙ, fOne (x⁻¹ * q * x) ≠ 0) →
        ∃ j, IsTwistedConjugate (rationalNormOneSubgroup F GLₙ)
          (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ) q) ∧
      ∀ [∀ j, MeasurableSpace (LeftQuotient (twistedCentralizer
            (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ)))]
        [∀ j, BorelSpace (LeftQuotient (twistedCentralizer
            (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ)))]
        [∀ j, MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
              (r j : normOneSubgroup F GLₙ))))]
        [∀ j, BorelSpace (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
              (r j : normOneSubgroup F GLₙ))))]
        (μC : ∀ j, Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
            (r j : normOneSubgroup F GLₙ)))
        [∀ j, (μC j).IsMulRightInvariant] [∀ j, IsFiniteMeasureOnCompacts (μC j)]
        [∀ j, (μC j).IsOpenPosMeasure]
        (νC : ∀ j, Measure (LeftQuotient (twistedCentralizer
            (MonoidHom.id (normOneSubgroup F GLₙ)) (r j : normOneSubgroup F GLₙ))))
        (νΓC : ∀ j, Measure (LeftQuotient ((rationalNormOneSubgroup F GLₙ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
              (r j : normOneSubgroup F GLₙ))))),
        (∀ j, Langlands.QuotientIntegration.IsCompatible
          (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
            (r j : normOneSubgroup F GLₙ))
          (Measure.haar : Measure (normOneSubgroup F GLₙ)) (μC j) (νC j)) →
        (∀ j, Langlands.QuotientIntegration.IsCompatible
          ((rationalNormOneSubgroup F GLₙ).subgroupOf
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F GLₙ))
              (r j : normOneSubgroup F GLₙ)))
          (μC j) Measure.count (νΓC j)) →
        (∀ j, νΓC j Set.univ ≠ ⊤) ∧
        (∀ j, Integrable (twistedOrbitFunction (MonoidHom.id (normOneSubgroup F GLₙ))
          (r j : normOneSubgroup F GLₙ) fOne) (νC j)) ∧
        operatorTrace (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG f h) =
          ∑ j, ((νΓC j Set.univ).toReal : ℂ) *
            orbitalIntegral (r j : normOneSubgroup F GLₙ) (νC j) fOne

/-- The simple trace formula for `GL_n` over a number field `F` on a finite sum
`f = ∑ⱼ aⱼ ⊗ bⱼ` of tensor test functions (`adelicTestTensor`, read on the group-scheme points
through `GeneralLinearGroupPoints.adelicHomeomorph`). Assume that every tensor test function has a
Hilbert–Schmidt cuspidal operator, that every finite component `bⱼ` has vanishing integrals over
the two-block unipotent subgroups of `GL_n(F_{wⱼ})` at some finite place `wⱼ` for every two-sided
translate, and that the support of every `aⱼ ⊗ bⱼ` is regular elliptic at the finite place `v`.
Then `f` is integrable and satisfies the simple trace formula at `v`
(`GeneralLinearSimpleTraceExpansion`): `R(f)` is trace class, and there are finitely many pairwise
non-conjugate rational norm-one points `r j`, regular elliptic at `v` and meeting every class on
which the orbit function of `f¹` does not vanish, with
`tr R(f) = ∑ j, vol((Γ ∩ C j) \ C j) · O_{r j}(f¹)` for all compatible measures. -/
def GeneralLinearTensorSimpleTraceFormulaStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F GLₙ)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F GLₙ) := Measure.haar
    (∀ (a : ArchimedeanGL.SmoothCompactKernel F n) (b : CompactFiniteGLTest F n)
      (h : Integrable (fun g => adelicTestTensor F n a b
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)) μG),
      IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction F GLₙ hPD hG T i hi I e hc μG
        (fun g => adelicTestTensor F n a b (GeneralLinearGroupPoints.adelicHomeomorph F n g))
        h)) →
    ∀ (m : ℕ) (a : Fin m → ArchimedeanGL.SmoothCompactKernel F n)
      (b : Fin m → CompactFiniteGLTest F n) (w : Fin m → Langlands.Global.FinitePlace F),
      (∀ j (p q : ℕ) (hpq : p + q = n), 0 < p → 0 < q →
        letI : MeasurableSpace (Matrix (Fin p) (Fin q) (FiniteCompletion F (w j))) := borel _
        ∀ ν : Measure (Matrix (Fin p) (Fin q) (FiniteCompletion F (w j))), ν.IsAddHaarMeasure →
          ∀ x y : FiniteAdelicGL F n,
            ∫ Z, (b j).val (x * FiniteAdelicGL.localInclusion F n (w j) (blockUnipotent hpq Z) * y)
              ∂ν = 0) →
    ∀ v : Langlands.Global.FinitePlace F,
      (∀ j, ∀ g ∈ tsupport (adelicTestTensor F n (a j) (b j)),
        IsRegularElliptic (FiniteAdelicGL.localProjection F n v (AdelicGL.finite F n g))) →
    let f : AdelicGroupPoints F GLₙ → ℂ := fun g =>
      ∑ j, adelicTestTensor F n (a j) (b j) (GeneralLinearGroupPoints.adelicHomeomorph F n g)
    ∃ h : Integrable f μG, GeneralLinearSimpleTraceExpansion F n T i hi I e hc v f h

/-- The simple trace formula for `GL_n` on a finite sum `f = ∑ⱼ aⱼ ⊗ bⱼ` of tensor test functions,
piece by piece. Under the hypotheses of `GeneralLinearTensorSimpleTraceFormulaStatement`, `f` is
integrable, `R(f)` is trace class, and `f` is a finite sum of Haar convolutions `f₁ₖ ⋆ f₂ₖ`, each
satisfying the simple trace formula at `v` (`GeneralLinearSimpleTraceExpansion`) with its own
family of representatives, with `tr R(f) = ∑ₖ tr R(f₁ₖ ⋆ f₂ₖ)`. -/
def GeneralLinearTensorSimpleTracePiecesStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F GLₙ)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F GLₙ) := Measure.haar
    (∀ (a : ArchimedeanGL.SmoothCompactKernel F n) (b : CompactFiniteGLTest F n)
      (h : Integrable (fun g => adelicTestTensor F n a b
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)) μG),
      IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction F GLₙ hPD hG T i hi I e hc μG
        (fun g => adelicTestTensor F n a b (GeneralLinearGroupPoints.adelicHomeomorph F n g))
        h)) →
    ∀ (m : ℕ) (a : Fin m → ArchimedeanGL.SmoothCompactKernel F n)
      (b : Fin m → CompactFiniteGLTest F n) (w : Fin m → Langlands.Global.FinitePlace F),
      (∀ j (p q : ℕ) (hpq : p + q = n), 0 < p → 0 < q →
        letI : MeasurableSpace (Matrix (Fin p) (Fin q) (FiniteCompletion F (w j))) := borel _
        ∀ ν : Measure (Matrix (Fin p) (Fin q) (FiniteCompletion F (w j))), ν.IsAddHaarMeasure →
          ∀ x y : FiniteAdelicGL F n,
            ∫ Z, (b j).val (x * FiniteAdelicGL.localInclusion F n (w j) (blockUnipotent hpq Z) * y)
              ∂ν = 0) →
    ∀ v : Langlands.Global.FinitePlace F,
      (∀ j, ∀ g ∈ tsupport (adelicTestTensor F n (a j) (b j)),
        IsRegularElliptic (FiniteAdelicGL.localProjection F n v (AdelicGL.finite F n g))) →
    let f : AdelicGroupPoints F GLₙ → ℂ := fun g =>
      ∑ j, adelicTestTensor F n (a j) (b j) (GeneralLinearGroupPoints.adelicHomeomorph F n g)
    ∃ h : Integrable f μG,
      IsTraceClass (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG f h) ∧
      ∃ (N : ℕ) (f₁ f₂ : Fin N → C_c(AdelicGroupPoints F GLₙ, ℂ))
        (hk : ∀ k, Integrable (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG) μG),
        (∀ g, f g = ∑ k, ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG) ∧
        (∀ k, GeneralLinearSimpleTraceExpansion F n T i hi I e hc v
          (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG) (hk k)) ∧
        operatorTrace (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG f h) =
          ∑ k, operatorTrace (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc μG
            (fun g => ∫ x, f₁ k x * f₂ k (x⁻¹ * g) ∂μG) (hk k))

end Langlands.TraceFormula
