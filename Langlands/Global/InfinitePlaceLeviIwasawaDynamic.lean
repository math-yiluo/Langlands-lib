import Langlands.Global.InfinitePlaceLeviIwasawaAssembly
import Langlands.GroupScheme.Dynamic.ReductiveLeviIwasawa

/-! # Archimedean Levi-compatible Iwasawa from dynamic structure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

/-- The published ambient realization theorem removes the realization
premise from the completion assembly. The two dynamic premises remain. -/
theorem completion_realization_of_dynamic
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F) :
    HasCompletionDiagonalStarLeviRealization F G P p M l v :=
  completion_realization_of_selfAdjoint_of_dynamic
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement
    hPD hGUR F G hG P p hp M l hl v

/-- Construct the actual compatible compact under the two retained
dynamic structure propositions. -/
theorem exists_leviCompatibleIwasawaCompact_of_dynamic
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F) :
    ∃ K, IsLeviCompatibleIwasawaCompact F G P p M l v K :=
  exists_leviCompatibleIwasawaCompact_of_completion_realization F G hG P p M l hl v
    (completion_realization_of_dynamic hPD hGUR F G hG P p hp M l hl v)

/-- Reduction of the exact published target to the two remaining dynamic
structure propositions. Neither proposition is proved by this wrapper. -/
theorem leviCompatibleIwasawaStatement_of_dynamic
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u}) :
    LeviCompatibleIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp M l hl v
  exact exists_leviCompatibleIwasawaCompact_of_dynamic
    hPD hGUR F G hG P p hp M l hl v

end Langlands.Global.InfinitePlaceGroupPoints
