import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.IntegralModel.LocalField

/-! # Opposite factors in smooth connected integral models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Theorem 8.2.9 over a nonarchimedean local field.** In a supplied smooth
connected integral model containing a closed integral split maximal generic torus,
the opposite factors of a nontrivial integral root point are integral exactly when
its reduction is outside the unipotent radical. The radical preimage is the
actual subgroup `Q.positivePoints`. -/
def IntegralOppositeFactorsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (_hiS : IsMaximalSplitTorus iS)
    (D : RelativeComponentModelData ↥𝒪[F] F G)
    (T : IntegralTorusData D S iS) (Q : SpecialFibreQuotientData D),
    T.IsClosedSplit → Q.IsReductiveQuotient →
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a, g ≠ 1 →
        g ∈ D.neutral.integralPoints →
          ∀ g' ∈ rootGroupPoints iS (-a), ∀ g'' ∈ rootGroupPoints iS (-a),
            g' * g * g'' ∈ normalizerPoints iS →
              ((g' ∈ D.neutral.integralPoints ∧ g'' ∈ D.neutral.integralPoints) ↔
                g ∉ Q.positivePoints)

end Langlands.BruhatTits.IntegralModels
