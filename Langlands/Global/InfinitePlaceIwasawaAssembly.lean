import Langlands.Global.InfinitePlaceIwasawaBaseChange
import Langlands.Global.InfiniteCompletionRCLike
import Langlands.GroupScheme.AffinePolarIwasawa
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationStatement
import Langlands.GroupScheme.Absolute.BorelStatement

/-! # Conditional assembly of archimedean local parabolic Iwasawa existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Conditional existence at one place: from the two remaining structural
propositions, the actual completion-point group has a compact subgroup, maximal
among compact subgroups, whose product with the literal point range of the
parabolic subgroup is the whole group. -/
theorem exists_iwasawa_of_realization_of_dynamic
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hD : ParabolicDynamicStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (hG : Langlands.GroupScheme.IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : Langlands.GroupScheme.IsParabolicSubgroup p)
    (v : NumberField.InfinitePlace F) :
    ∃ K : Subgroup (InfinitePlaceGroupPoints F G v),
      IsCompact (K : Set (InfinitePlaceGroupPoints F G v)) ∧
      (∀ L : Subgroup (InfinitePlaceGroupPoints F G v),
        IsCompact (L : Set (InfinitePlaceGroupPoints F G v)) → K ≤ L → L = K) ∧
      Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) *
        (K : Set (InfinitePlaceGroupPoints F G v)) = Set.univ := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  suffices h : CompactIwasawa.HasDecomposition
      (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) from h
  rw [hasDecomposition_completionBaseChange_iff F G P p v]
  have : IsRCLikeNormedField v.Completion := v.completion_isRCLikeNormedField
  let : RCLike v.Completion := IsRCLikeNormedField.rclike v.Completion
  have hGv := isConnectedReductive_completionBaseChange F G hG v
  have hpv := isParabolicSubgroup_completionBaseChange F G hG P p hp v
  let : IsAffineHom (completionBaseChange F G v).X.hom := hGv.isAffineHom
  let : IsAffine (completionBaseChange F G v).X.left :=
    isAffine_of_isAffineHom (completionBaseChange F G v).X.hom
  obtain ⟨d, ρ, hρ, hstar⟩ := hR v.Completion (completionBaseChange F G v) hGv
  have hpc := hpv.isClosedSubgroup
  let : IsClosedImmersion
      ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p).hom.hom.left := hpc
  have : Mono ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p).hom.hom :=
    Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (hD v.Completion (completionBaseChange F G v) hGv _ _ hpc).1 hpv
  obtain ⟨K, hK, hmax, hcover⟩ := ρ.affineDynamicIwasawa (S := v.Completion) hρ hstar
  exact ⟨K, hK, hmax, hcover χ _ _ ⟨inferInstance, hχ⟩⟩

/-- The compact subgroup produced by the conditional assembly: a chosen
compact subgroup of the actual completion-point group, maximal among compact
subgroups, whose product with the literal point range of `p` is everything. -/
noncomputable def iwasawaCompact
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hD : ParabolicDynamicStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (hG : Langlands.GroupScheme.IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : Langlands.GroupScheme.IsParabolicSubgroup p)
    (v : NumberField.InfinitePlace F) :
    Subgroup (InfinitePlaceGroupPoints F G v) :=
  Classical.choose (exists_iwasawa_of_realization_of_dynamic hR hD F G hG P p hp v)

/-- The chosen compact subgroup has the three required Iwasawa properties. -/
theorem iwasawaCompact_spec
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hD : ParabolicDynamicStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (hG : Langlands.GroupScheme.IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : Langlands.GroupScheme.IsParabolicSubgroup p)
    (v : NumberField.InfinitePlace F) :
    IsCompact (iwasawaCompact hR hD F G hG P p hp v :
        Set (InfinitePlaceGroupPoints F G v)) ∧
      (∀ L : Subgroup (InfinitePlaceGroupPoints F G v),
        IsCompact (L : Set (InfinitePlaceGroupPoints F G v)) →
          iwasawaCompact hR hD F G hG P p hp v ≤ L →
            L = iwasawaCompact hR hD F G hG P p hp v) ∧
      Set.range (P.affinePointsTarget p (CommAlgCat.of F v.Completion)) *
        (iwasawaCompact hR hD F G hG P p hp v :
          Set (InfinitePlaceGroupPoints F G v)) = Set.univ :=
  Classical.choose_spec (exists_iwasawa_of_realization_of_dynamic hR hD F G hG P p hp v)

/-- Conditional assembly of the exact archimedean local target from the two
remaining structural propositions: existence of an adjoint-stable closed
realization and the identification of rational parabolics with dynamic
parabolics. Both propositions remain explicit hypotheses. -/
theorem parabolicIwasawaStatement_of_realization_of_dynamic
    (hR : ConnectedReductiveSelfAdjointRealizationStatement.{u})
    (hD : ParabolicDynamicStatement.{u}) :
    ParabolicIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp v
  exact ⟨iwasawaCompact hR hD F G hG P p hp v,
    iwasawaCompact_spec hR hD F G hG P p hp v⟩

end Langlands.Global.InfinitePlaceGroupPoints
