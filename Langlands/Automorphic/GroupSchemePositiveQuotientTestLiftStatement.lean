import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicSplitCenterQuotient
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! # Lifting smooth tests from the quotient by the positive split centre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

/-- A compactly supported test on the quotient by the positive central image, identified
with the norm-one group. Smoothness is tested on its pullback to the full adelic group,
with both finite open translation levels. -/
def IsPositiveQuotientTestFunction (f : C_c(normOneSubgroup F G, ℂ)) : Prop :=
  let pullback := (f : normOneSubgroup F G → ℂ) ∘ normOneProjection F G T i hi I e hc
  IsAdelicSmoothFunction F G pullback ∧
    ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∀ l ∈ L, ∀ g : AdelicGroupPoints F G, pullback (ofFinite F G l * g) = pullback g

/-- Every such quotient test is the positive-factor average of a smooth compactly
supported adelic test, for the Haar measure that makes the product with norm-one Haar
equal to ambient Haar. -/
def GroupSchemePositiveQuotientTestLiftStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (hi : Function.Injective (characterRestrict i))
      [(characterRestrict i).range.FiniteIndex]
      (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
      (hc : IsCentral i) (f : C_c(normOneSubgroup F G, ℂ)),
      IsPositiveQuotientTestFunction F G T i hi I e hc f →
        ∃ h : C_c(AdelicGroupPoints F G, ℂ), IsAdelicTestFunction F G h ∧
          ∀ x : normOneSubgroup F G,
            (∫ a, h (positivePointMap F G T i a * x)
              ∂normalizedPositiveHaarMeasure F G T i hi I e hc) = f x

end Langlands.Automorphic.GroupSchemeFunctions
