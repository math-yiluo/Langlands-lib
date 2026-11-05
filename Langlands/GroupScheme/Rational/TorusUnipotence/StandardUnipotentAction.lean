import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.DynamicPositiveSemigroup
import Langlands.GroupScheme.Rational.ActionWeightSupport
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.CoordinateSemigroupProof
import Langlands.GroupScheme.RepresentedAction

/-! # The torus action on the standard unipotent subgroup

For a smooth affine group `G` over a field, a split torus `i : T ⟶ G` and a cocharacter `ν`,
the standard unipotent subgroup for the empty set of simple roots is the dynamic unipotent
subgroup `U_G(ν)`. Its closed representative `N = Standard.unipotentScheme i ν ∅` is smooth and
connected, `T` acts on it by conjugation, the Lie weights of this action are the positive
relative roots with the multiplicities of `Lie(G)`, and its augmentation weights pair positively
with `ν`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Standard

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

instance (J : Set (characterLattice T)) : IsAffineHom (unipotentScheme i ν J).X.hom :=
  (isClosedSubgroup_unipotentHom i ν J).isAffineHom

instance (J : Set (characterLattice T)) : Mono (unipotentHom i ν J).hom.hom :=
  (isRepresentedBy_unipotentHom i ν J).1

variable [Smooth G.X.hom] (hT : IsSplitTorus T.toGrp)

include hT

/-- For the empty set of simple roots, the standard unipotent subgroup is the dynamic
unipotent subgroup of `ν`. -/
theorem standardUnipotent_empty_eq :
    standardUnipotent i ν ∅ = Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  refine le_antisymm
    (standardUnipotent_le_dynamicUnipotent i ν (isStandardCocharacter_empty_self i ν)) ?_
  intro U g hg
  rw [mem_standardUnipotent]
  intro ζ hζ
  refine (rootSignUnipotentInclusions k G T hT i ν ζ).2 ?_ U hg
  intro χ hχ hpos
  rw [hζ.pairing_pos_iff_not_mem_closure i ν ⟨hχ, hpos⟩, AddSubmonoid.closure_empty,
    AddSubmonoid.mem_bot]
  exact (mem_relativeRoots.1 hχ).1

/-- The standard unipotent representative represents the dynamic unipotent subgroup. -/
theorem isRepresentedBy_unipotentHom_empty :
    (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (unipotentHom i ν ∅) := by
  rw [← standardUnipotent_empty_eq i ν hT]
  exact isRepresentedBy_unipotentHom i ν ∅

theorem smooth_unipotentScheme_empty : Smooth (unipotentScheme i ν ∅).X.hom :=
  (dynamicSmooth k G (CommGroupScheme.groupHom ν ≫ i) _ _).2.2
    (isRepresentedBy_unipotentHom_empty i ν hT)

theorem connectedSpace_unipotentScheme_empty : ConnectedSpace (unipotentScheme i ν ∅).X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G _
    (isRepresentedBy_unipotentHom_empty i ν hT)

/-- The conjugation action of `T` on the standard unipotent representative. -/
def unipotentAction : AutomorphicAction T.toGrp (unipotentScheme i ν ∅) :=
  (AutomorphicAction.conjugation i).onRepresentedSubgroup (unipotentHom i ν ∅)
    (isRepresentedBy_unipotentHom_empty i ν hT) (Dynamic.unipotent_isStable_conjugation i _)

/-- The inclusion intertwines the action with conjugation in `G`. -/
theorem unipotentAction_act_comp {U : Over (Spec (CommRingCat.of k))} (s : U ⟶ T.X)
    (x : U ⟶ (unipotentScheme i ν ∅).X) :
    (unipotentAction i ν hT).act s x ≫ (unipotentHom i ν ∅).hom.hom =
      (s ≫ i.hom.hom) * (x ≫ (unipotentHom i ν ∅).hom.hom) * (s ≫ i.hom.hom)⁻¹ := by
  rw [unipotentAction, AutomorphicAction.onRepresentedSubgroup_act_comp,
    AutomorphicAction.conjugation_act]

/-- The weights of the conjugation action on the Lie algebra of the dynamic unipotent
subgroup are the positive relative roots. -/
theorem actionWeightSupport_dynamicUnipotent :
    RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation i)
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) = positiveRelativeRoots i ν := by
  obtain ⟨-, -, hLie⟩ := RelativeRoot.dynamicUnipotent_semigroupData G T hT i ν
  rw [RelativeRoot.actionWeightSupport_eq_inter_of_hasLieImage _ _ _ hLie
      (RelativeRoot.actionWeightSupport_subset_of_tangentSubmodule_le
        (AutomorphicAction.conjugation i) hT (RelativeRoot.positiveSemigroup ν) _
        (le_of_eq ((RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mp hLie))),
    RelativeRoot.actionWeightSupport_top_inter_positiveSemigroup]

/-- A character is a Lie weight of the action on `N` exactly when it is a positive relative
root. -/
theorem actionWeightSpace_unipotentAction_ne_bot_iff (χ : characterLattice T) :
    RelativeRoot.actionWeightSpace (unipotentAction i ν hT) χ ≠ ⊥ ↔
      χ ∈ positiveRelativeRoots i ν := by
  rw [unipotentAction, ← RelativeRoot.mem_actionWeightSupport_iff_onRepresentedSubgroup,
    actionWeightSupport_dynamicUnipotent i ν hT]

/-- For a positive relative root `β`, the `β`-weight space of `T` on `Lie(N)` has the same
dimension as the `β`-weight space of `T` on `Lie(G)`. -/
theorem finrank_actionWeightSpace_unipotentAction {β : characterLattice T}
    (hβ : β ∈ positiveRelativeRoots i ν) :
    Module.finrank k (RelativeRoot.actionWeightSpace (unipotentAction i ν hT) β) =
      Module.finrank k (weightSpace i β) := by
  obtain ⟨-, -, hLie⟩ := RelativeRoot.dynamicUnipotent_semigroupData G T hT i ν
  have hN := isRepresentedBy_unipotentHom_empty i ν hT
  have hmap := RelativeRoot.map_actionWeightSpace_eq_inf_tangentSubmodule
    (AutomorphicAction.conjugation i) (unipotentAction i ν hT) (unipotentHom i ν ∅)
    (fun _ s x => AutomorphicAction.onRepresentedSubgroup_act_comp _ _ hN _ s x) β
  have hle : RelativeRoot.actionWeightSpace (AutomorphicAction.conjugation i) β ≤
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range (unipotentHom i ν ∅)) := by
    intro X hX
    change X.toMul.val ∈ (SubgroupFunctor.range (unipotentHom i ν ∅)).carrier _
    rw [hN.2]
    exact (hLie X).mpr ((le_iSup_of_le (⟨β, hβ.2⟩ : RelativeRoot.positiveSemigroup ν) le_rfl :
      RelativeRoot.actionWeightSpace (AutomorphicAction.conjugation i) β ≤
        RelativeRoot.semigroupWeightSpan (AutomorphicAction.conjugation i)
          (RelativeRoot.positiveSemigroup ν)) hX)
  rw [← RelativeRoot.actionWeightSpace_conjugation,
    (Submodule.equivMapOfInjective _ (Lie.targetMapLinear_injective (unipotentHom i ν ∅) k)
      _).finrank_eq, hmap, inf_eq_left.mpr hle]

/-- The augmentation weights of the action on `N` pair positively with `ν`. -/
theorem pairing_pos_of_mem_support {χ : characterLattice T}
    (hχ : χ ∈ CoordinateWeights.support (unipotentAction i ν hT)) :
    0 < latticePairing T χ ν := by
  have hcmp := CoordinateWeights.coordinateSemigroupComparison.2 k (unipotentScheme i ν ∅)
    (smooth_unipotentScheme_empty i ν hT) inferInstance
    (connectedSpace_unipotentScheme_empty i ν hT) T hT (unipotentAction i ν hT)
    (RelativeRoot.positiveSemigroup ν)
  refine (hcmp.mpr ?_) hχ
  intro ψ hψ
  rw [RelativeRoot.actionWeightSupport_top] at hψ
  exact ((actionWeightSpace_unipotentAction_ne_bot_iff i ν hT ψ).mp hψ).2

end Langlands.GroupScheme.Standard
