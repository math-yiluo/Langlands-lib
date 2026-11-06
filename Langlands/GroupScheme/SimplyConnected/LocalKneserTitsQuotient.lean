import Langlands.GroupScheme.SimplyConnected.LocalKneserTitsStatement
import Langlands.GroupScheme.Rational.ParabolicWhiteheadQuotient

/-! # Exact elementary-subgroup and quotient formulations of local Kneser–Tits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The published local target is equivalent to equality of the actual
parabolic elementary subgroup with all rational points. -/
theorem localKneserTitsStatement_iff_elementarySubgroup_eq_top :
    LocalKneserTitsStatement.{u} ↔
      ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F]
        (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
        IsSimplyConnected G → IsAlmostSimple G → ¬ IsAnisotropic G →
          parabolicElementarySubgroup G = ⊤ := by
  constructor
  · intro h F _ _ _ _ G _ hsc has hiso
    exact (parabolicElementarySubgroup_eq_top_iff G).mpr (h F G hsc has hiso)
  · intro h F _ _ _ _ G _ hsc has hiso
    exact (parabolicElementarySubgroup_eq_top_iff G).mp (h F G hsc has hiso)

/-- The exact published target is equivalent to triviality of the actual
parabolic Whitehead quotient, with the same field and group hypotheses. -/
theorem localKneserTitsStatement_iff_quotient_subsingleton :
    LocalKneserTitsStatement.{u} ↔
      ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F]
        (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
        IsSimplyConnected G → IsAlmostSimple G → ¬ IsAnisotropic G →
          Subsingleton (parabolicWhiteheadQuotient G) := by
  rw [localKneserTitsStatement_iff_elementarySubgroup_eq_top]
  constructor
  · intro h F _ _ _ _ G _ hsc has hiso
    exact (parabolicWhiteheadQuotient_subsingleton_iff G).mpr (h F G hsc has hiso)
  · intro h F _ _ _ _ G _ hsc has hiso
    exact (parabolicWhiteheadQuotient_subsingleton_iff G).mp (h F G hsc has hiso)

end Langlands.GroupScheme
