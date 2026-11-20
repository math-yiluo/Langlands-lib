import Langlands.Automorphic.GroupSchemeFullAEL2Integrated

/-!
# Convolution operators with vanishing radical integrals have cuspidal image

Let `G` be a connected reductive group over a number field `F`, presented as in the Library's
full almost-everywhere cuspidal `L²` space: `T → G` is a central split torus with
finite-index character restriction, `[G]` is the quotient of `G(𝔸_F)` by `G(F)` and the
positive real points of `T`, and `L²([G])` uses its Haar quotient measure. Let `dg` be the
Haar measure of `G(𝔸_F)` and `f` a continuous compactly supported function on `G(𝔸_F)`.
Suppose that for every proper rational parabolic `P` with unipotent radical `N_P`,

`∫_{N_P(𝔸_F)} f(x n y) dn = 0` for all `x, y ∈ G(𝔸_F)`.

Then the operator `R(f) = ∫ f(g) R(g) dg` on `L²([G])` maps every `φ` into the Library's
`fullAEL2CuspidalSubmodule`: for every proper rational parabolic, almost every constant term
of `R(f)φ` converges and vanishes.

This is the unfolding step of Getz–Hahn 2024, Lemma 16.4.2 (printed p. 430), for the
right regular representation on `L²([G])`, with "supercuspidal at one place" replaced by the
vanishing condition its proof uses. See `GroupSchemeCuspidalImageStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.TraceFormula

/-- If a compactly supported continuous `f` on `G(𝔸_F)` has vanishing integrals over every
two-sided translate of the adelic points of the unipotent radical of every proper rational
parabolic subgroup (with the Library's normalized radical Haar measure), then the Haar
integrated right action `R(f)` maps all of `L²` of the positive rational quotient into the
full almost-everywhere cuspidal submodule. -/
def GroupSchemeCuspidalImageStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    ∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG),
      (∀ (P : ProperRationalParabolic G) (x y : AdelicGroupPoints F G),
        ∫ n, f (x * (n : AdelicGroupPoints F G) * y)
          ∂properParabolicHaarMeasure F G hPD hG P = 0) →
      ∀ φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i),
        haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf φ ∈
          fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc

end Langlands.TraceFormula
