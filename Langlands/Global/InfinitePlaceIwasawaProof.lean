import Langlands.Global.InfinitePlaceIwasawaStatement
import Langlands.Global.InfinitePlaceIwasawaBaseChange
import Langlands.Global.InfiniteCompletionRCLike
import Langlands.GroupScheme.AffinePolarIwasawa
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicForward

/-! # Actual archimedean local parabolic Iwasawa existence: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Existence at one place: the actual completion-point group has a compact
subgroup, maximal among compact subgroups, whose product with the literal point
range of the parabolic subgroup is the whole group. -/
theorem exists_parabolicIwasawaCompact
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
  have hGv := isConnectedReductive_completionBaseChange F G hG v
  have hpv := isParabolicSubgroup_completionBaseChange F G hG P p hp v
  obtain ⟨χ, hχ⟩ := exists_cocharacter_range_eq_parabolic_of_isParabolicSubgroup
    v.Completion (completionBaseChange F G v) hGv _ _ hpv
  have : IsRCLikeNormedField v.Completion := v.completion_isRCLikeNormedField
  let : RCLike v.Completion := IsRCLikeNormedField.rclike v.Completion
  let : IsAffineHom (completionBaseChange F G v).X.hom := hGv.isAffineHom
  let : IsAffine (completionBaseChange F G v).X.left :=
    isAffine_of_isAffineHom (completionBaseChange F G v).X.hom
  obtain ⟨d, ρ, hρ, hstar⟩ :=
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement
      v.Completion (completionBaseChange F G v) hGv
  have hpc := hpv.isClosedSubgroup
  let : IsClosedImmersion
      ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p).hom.hom.left := hpc
  have : Mono ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p).hom.hom :=
    Over.mono_of_mono_left _
  obtain ⟨K, hK, hmax, hcover⟩ := ρ.affineDynamicIwasawa (S := v.Completion) hρ hstar
  exact ⟨K, hK, hmax, hcover χ _ _ ⟨inferInstance, hχ⟩⟩

/-- **Actual archimedean local parabolic Iwasawa existence.** For every number
field, connected reductive group, parabolic subgroup and infinite place, the
actual completion-point group has a compact subgroup, maximal among compact
subgroups, whose product with the parabolic point range is the whole group. -/
theorem parabolicIwasawaStatement : ParabolicIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp v
  exact exists_parabolicIwasawaCompact F G hG P p hp v

end Langlands.Global.InfinitePlaceGroupPoints
