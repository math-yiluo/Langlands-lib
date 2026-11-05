import Langlands.GroupScheme.Dynamic.RCLikeLeviIwasawa
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationStatement
import Langlands.Global.InfinitePlaceLeviIwasawaRealization

/-! # Archimedean Levi-compatible Iwasawa from the remaining structural inputs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

/-- The three remaining structural inputs yield compatible diagonal data on
the actual completion pullback. The common cocharacter is chosen over the
original number field and then base changed. -/
theorem completion_realization_of_selfAdjoint_of_dynamic
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F) :
    HasCompletionDiagonalStarLeviRealization F G P p M l v := by
  let : IsRCLikeNormedField v.Completion := v.completion_isRCLikeNormedField
  let := IsRCLikeNormedField.rclike v.Completion
  obtain ⟨χ, hχp, hχm⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD hGUR hG hp hl
  have hpc := hp.isClosedSubgroup
  have hmc := hl.isClosedSubgroup.comp hpc
  let : IsClosedImmersion p.hom.hom.left := hpc
  let : IsClosedImmersion (l ≫ p).hom.hom.left := hmc
  have hpχ : (Dynamic.parabolic χ).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, hχp⟩
  have hmχ : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, hχm⟩
  let b := Spec.algebraMap F v.Completion
  let B := GroupScheme.baseChange b
  let ψ := Dynamic.baseChangeCocharacter b χ
  have hpψ : (Dynamic.parabolic ψ).IsRepresentedBy (B.map p) := by
    rw [Dynamic.parabolic_baseChange]
    exact hpχ.baseChange b
  have hmψ : (Dynamic.centralizer ψ).IsRepresentedBy (B.map l ≫ B.map p) := by
    rw [Dynamic.centralizer_baseChange, ← B.map_comp]
    exact hmχ.baseChange b
  have hGv := isConnectedReductive_completionBaseChange F G hG v
  have hs : MatrixRepresentation.HasClosedStarRealization (B.obj G) :=
    hR v.Completion (B.obj G) hGv
  exact hs.hasRCLikeDiagonalStarLeviRealization ψ hpψ hmψ

/-- Construct the actual compatible compact subgroup from the three
remaining structural propositions, retaining them as explicit premises. -/
theorem exists_leviCompatibleIwasawaCompact_of_selfAdjoint_of_dynamic
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
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
    (completion_realization_of_selfAdjoint_of_dynamic hR hPD hGUR F G hG P p hp M l hl v)

/-- The chosen compatible compact subgroup of the unchanged actual
completion-point group under the three retained structural inputs. -/
def leviCompatibleIwasawaCompact
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F) :
    Subgroup (InfinitePlaceGroupPoints F G v) :=
  Classical.choose (exists_leviCompatibleIwasawaCompact_of_selfAdjoint_of_dynamic
    hR hPD hGUR F G hG P p hp M l hl v)

/-- The selected subgroup satisfies all four original conclusions. -/
theorem leviCompatibleIwasawaCompact_spec
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F) :
    IsLeviCompatibleIwasawaCompact F G P p M l v
      (leviCompatibleIwasawaCompact hR hPD hGUR F G hG P p hp M l hl v) :=
  Classical.choose_spec (exists_leviCompatibleIwasawaCompact_of_selfAdjoint_of_dynamic
    hR hPD hGUR F G hG P p hp M l hl v)

/-- Conditional assembly of the exact existing proposition. None of the
three structural propositions is proved by this theorem. -/
theorem leviCompatibleIwasawaStatement_of_selfAdjoint_of_dynamic
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u}) :
    LeviCompatibleIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp M l hl v
  exact exists_leviCompatibleIwasawaCompact_of_selfAdjoint_of_dynamic
    hR hPD hGUR F G hG P p hp M l hl v

end Langlands.Global.InfinitePlaceGroupPoints
