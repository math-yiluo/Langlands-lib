import Langlands.GroupScheme.Dynamic.CommonTorusDeterminantBalance
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.ActionWeightFunctoriality

/-! # Actual intersection determinants on a common split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Tangent

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)

include hT

/-- The tangent submodule of a cocharacter centralizer is its zero-pairing region. -/
theorem tangentSubmodule_centralizer_eq_weightRegion (zeta : cocharacterLattice T) :
    RelativeRoot.tangentSubmodule
        (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)) =
      ⨆ α : characterLattice T, ⨆ (_ : latticePairing T α zeta = 0), weightSpace i α := by
  rw [← weightSpace_cocharacter_eq_iSup hT i zeta 0]
  ext X
  exact (dynamicLie k G (CommGroupScheme.groupHom zeta ≫ i) X.toMul).1

/-- The tangent submodule of an identity-limit subgroup is its positive-pairing region. -/
theorem tangentSubmodule_unipotent_eq_weightRegion (zeta : cocharacterLattice T) :
    RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)) =
      ⨆ α : characterLattice T, ⨆ (_ : 0 < latticePairing T α zeta), weightSpace i α := by
  rw [RelativeRoot.tangentSubmodule_unipotent_eq_semigroupWeightSpan hT i zeta,
    RelativeRoot.semigroupWeightSpan_conjugation,
    RelativeRoot.adjointSemigroupWeightSpan]
  exact iSup_subtype

/-- A single actual weight space meets a weight region in itself or zero. -/
theorem weightSpace_inf_weightRegion (p : characterLattice T → Prop)
    (α : characterLattice T) :
    weightSpace i α ⊓ (⨆ β : characterLattice T, ⨆ (_ : p β), weightSpace i β) =
      if p α then weightSpace i α else ⊥ := by
  split_ifs with hα
  · exact inf_eq_left.mpr (le_iSup₂_of_le α hα le_rfl)
  · rw [← disjoint_iff]
    exact weightSpace_disjoint_iSup hT i hα

/-- Centralizer intersection cuts an actual weight space by the zero pairing. -/
theorem weightSpace_inf_tangentSubmodule_centralizer (zeta : cocharacterLattice T)
    (α : characterLattice T) :
    weightSpace i α ⊓ RelativeRoot.tangentSubmodule
        (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)) =
      if latticePairing T α zeta = 0 then weightSpace i α else ⊥ := by
  rw [tangentSubmodule_centralizer_eq_weightRegion hT i,
    weightSpace_inf_weightRegion hT i]
  split_ifs <;> rfl

/-- Unipotent intersection cuts an actual weight space by the positive pairing. -/
theorem weightSpace_inf_tangentSubmodule_unipotent (zeta : cocharacterLattice T)
    (α : characterLattice T) :
    weightSpace i α ⊓ RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)) =
      if 0 < latticePairing T α zeta then weightSpace i α else ⊥ := by
  rw [tangentSubmodule_unipotent_eq_weightRegion hT i,
    weightSpace_inf_weightRegion hT i]
  split_ifs <;> rfl

/-- The unipotent/centralizer intersection has exactly the positive/zero weight region. -/
theorem weightSpace_inf_tangentSubmodule_unipotent_inf_centralizer
    (zeta eta : cocharacterLattice T) (α : characterLattice T) :
    weightSpace i α ⊓ RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
          Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)) =
      if 0 < latticePairing T α zeta ∧ latticePairing T α eta = 0
      then weightSpace i α else ⊥ := by
  rw [RelativeRoot.tangentSubmodule_inf, inf_inf_distrib_left,
    weightSpace_inf_tangentSubmodule_unipotent hT i,
    weightSpace_inf_tangentSubmodule_centralizer hT i]
  by_cases hz : 0 < latticePairing T α zeta <;>
    by_cases he : latticePairing T α eta = 0 <;>
    simp only [hz, he, and_self, and_false, false_and, ite_true, ite_false,
      inf_idem, inf_bot_eq, bot_inf_eq]

/-- The two-unipotent intersection has exactly the common positive weight region. -/
theorem weightSpace_inf_tangentSubmodule_unipotent_inf_unipotent
    (zeta eta : cocharacterLattice T) (α : characterLattice T) :
    weightSpace i α ⊓ RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
          Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) =
      if 0 < latticePairing T α zeta ∧ 0 < latticePairing T α eta
      then weightSpace i α else ⊥ := by
  rw [RelativeRoot.tangentSubmodule_inf, inf_inf_distrib_left,
    weightSpace_inf_tangentSubmodule_unipotent hT i,
    weightSpace_inf_tangentSubmodule_unipotent hT i]
  by_cases hz : 0 < latticePairing T α zeta <;>
    by_cases he : 0 < latticePairing T α eta <;>
    simp only [hz, he, and_self, and_false, false_and, ite_true, ite_false,
      inf_idem, inf_bot_eq, bot_inf_eq]

end Tangent

section Determinant

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom U.X.hom] [IsAffine H.X.left]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
  (a : AutomorphicAction H U) (j : T.toGrp ⟶ H)
  {F : SubgroupFunctor G} {iU : U ⟶ G}
  (hU : F.IsRepresentedBy iU)
  (ha : (a.restrict j).IsEquivariant (AutomorphicAction.conjugation i) iU)
  (p : characterLattice T → Prop)
  (hp : ∀ α, weightSpace i α ⊓ RelativeRoot.tangentSubmodule F =
    if p α then weightSpace i α else ⊥)

include hU ha hp

omit [IsAffine H.X.left] in
/-- The differential of the actual inclusion identifies each intersection weight space. -/
theorem map_lieWeightSpace_of_tangentRegion (α : characterLattice T) :
    (a.lieWeightSpace j α).map (Lie.targetMapLinear iU k) =
      if p α then weightSpace i α else ⊥ := by
  have : Mono iU.hom.hom := hU.1
  have he : a.lieWeightSpace j α =
      RelativeRoot.actionWeightSpace (a.restrict j) α := by
    rw [RelativeRoot.actionWeightSpace_eq_lieWeightSpace,
      AutomorphicAction.lieWeightSpace_restrict, Category.id_comp]
  rw [he, ha.map_actionWeightSpace_eq_inf_range,
    RelativeRoot.actionWeightSpace_conjugation,
    ← RelativeRoot.tangentSubmodule_range iU, hU.2, hp]

omit [IsAffine H.X.left] in
/-- Actual intersection weight multiplicities, without a characteristic restriction. -/
theorem finrank_lieWeightSpace_of_tangentRegion (α : characterLattice T) :
    Module.finrank k (a.lieWeightSpace j α) =
      if p α then Module.finrank k (weightSpace i α) else 0 := by
  have : Mono iU.hom.hom := hU.1
  rw [(Submodule.equivMapOfInjective _ (Lie.targetMapLinear_injective iU k) _).finrank_eq,
    map_lieWeightSpace_of_tangentRegion i a j hU ha p hp α]
  by_cases h : p α
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, finrank_bot]

include hT in
/-- The determinant of the represented action restricts to its actual weighted region. -/
theorem characterRestrict_determinant_of_tangentRegion {d : ℕ}
    (c : Lie.FiniteCoordinates U d) :
    characterRestrict j (a.determinantCharacter c) = regionWeightCharacter i p := by
  rw [a.determinantCharacter_restrict_eq_rootSum c hT j,
    finsum_mem_def, regionWeightCharacter]
  apply finsum_congr
  intro α
  rw [← finrank_lieWeightSpace_of_tangentRegion i a j hU ha p hp α]
  by_cases hmem : α ∈ a.lieRoots j
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem]
    rw [AutomorphicAction.mem_lieRoots, not_and_or, not_not, not_not] at hmem
    rcases hmem with h0 | hb
    · rw [h0, map_zero, smul_zero]
    · rw [hb, finrank_bot, zero_smul]

end Determinant

section IntersectionDeterminant

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom U.X.hom] [IsAffine H.X.left]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
  (a : AutomorphicAction H U) (j : T.toGrp ⟶ H)
  (zeta eta : cocharacterLattice T) {iU : U ⟶ G}

include hT

/-- Any actual action on the positive/zero intersection with the displayed
equivariance has the actual positive/zero determinant after torus restriction. -/
theorem characterRestrict_determinant_unipotent_inf_centralizer
    (hU : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU)
    (ha : (a.restrict j).IsEquivariant (AutomorphicAction.conjugation i) iU)
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    characterRestrict j (a.determinantCharacter c) =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α zeta ∧ latticePairing T α eta = 0) :=
  characterRestrict_determinant_of_tangentRegion hT i a j hU ha _
    (by
      intro α
      rw [weightSpace_inf_tangentSubmodule_unipotent_inf_centralizer hT i zeta eta]
      split_ifs <;> rfl) c

/-- Any actual action on the common positive intersection with the displayed
equivariance has the actual common positive determinant after torus restriction. -/
theorem characterRestrict_determinant_unipotent_inf_unipotent
    (hU : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU)
    (ha : (a.restrict j).IsEquivariant (AutomorphicAction.conjugation i) iU)
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    characterRestrict j (a.determinantCharacter c) =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α zeta ∧ 0 < latticePairing T α eta) :=
  characterRestrict_determinant_of_tangentRegion hT i a j hU ha _
    (by
      intro α
      rw [weightSpace_inf_tangentSubmodule_unipotent_inf_unipotent hT i zeta eta]
      split_ifs <;> rfl) c

end IntersectionDeterminant

namespace Dynamic

section Actions

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G U : GroupScheme S}
  (i : T.toGrp ⟶ G) (zeta eta : cocharacterLattice T) {iU : U ⟶ G}

private theorem isStable_inf {H : GroupScheme S} {a : AutomorphicAction H G}
    {F F' : SubgroupFunctor G} (hF : a.IsStable F) (hF' : a.IsStable F') :
    a.IsStable (F ⊓ F') :=
  fun V h g hg => ⟨hF V h g hg.1, hF' V h g hg.2⟩

/-- The actual common torus conjugates the intersection of two identity-limit subgroups. -/
def unipotentIntersectionTorusAction
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU) :
    AutomorphicAction T.toGrp U :=
  (AutomorphicAction.conjugation i).onRepresentedSubgroup iU hU
    (isStable_inf (unipotent_isStable_conjugation i (CommGroupScheme.groupHom zeta))
      (unipotent_isStable_conjugation i (CommGroupScheme.groupHom eta)))

/-- The actual common torus conjugates the positive/zero intersection subgroup. -/
def unipotentCentralizerIntersectionTorusAction
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU) :
    AutomorphicAction T.toGrp U :=
  (AutomorphicAction.conjugation i).onRepresentedSubgroup iU hU
    (isStable_inf (unipotent_isStable_conjugation i (CommGroupScheme.groupHom zeta))
      (centralizer_isStable_conjugation i (CommGroupScheme.groupHom eta)))

/-- The actual inclusion intertwines the canonical common positive torus action. -/
theorem unipotentIntersectionTorusAction_isEquivariant
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU) :
    (unipotentIntersectionTorusAction i zeta eta hU).IsEquivariant
      (AutomorphicAction.conjugation i) iU := by
  intro V t g
  exact AutomorphicAction.onRepresentedSubgroup_act_comp ..

/-- The actual inclusion intertwines the canonical positive/zero torus action. -/
theorem unipotentCentralizerIntersectionTorusAction_isEquivariant
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU) :
    (unipotentCentralizerIntersectionTorusAction i zeta eta hU).IsEquivariant
      (AutomorphicAction.conjugation i) iU := by
  intro V t g
  exact AutomorphicAction.onRepresentedSubgroup_act_comp ..

end Actions

section TorusDeterminants

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom U.X.hom]
  [IsAffine T.X.left]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
  (zeta eta : cocharacterLattice T) {iU : U ⟶ G}

include hT

/-- The determinant of the constructed torus action is the actual common
positive weighted character. -/
theorem unipotentIntersectionTorusAction_determinantCharacter
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU)
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    (unipotentIntersectionTorusAction i zeta eta hU).determinantCharacter c =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α zeta ∧ 0 < latticePairing T α eta) := by
  have ha :
      ((unipotentIntersectionTorusAction i zeta eta hU).restrict (𝟙 T.toGrp)).IsEquivariant
        (AutomorphicAction.conjugation i) iU := by
    intro V t g
    simpa only [AutomorphicAction.restrict_act, Grp.id_hom_hom, Category.id_comp,
      Category.comp_id] using
      unipotentIntersectionTorusAction_isEquivariant i zeta eta hU t g
  simpa only [characterRestrict_id, AddMonoidHom.id_apply] using
    characterRestrict_determinant_unipotent_inf_unipotent hT i
      (unipotentIntersectionTorusAction i zeta eta hU) (𝟙 T.toGrp) zeta eta hU ha c

/-- The determinant of the constructed torus action is the actual
positive/zero weighted character. -/
theorem unipotentCentralizerIntersectionTorusAction_determinantCharacter
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU)
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    (unipotentCentralizerIntersectionTorusAction i zeta eta hU).determinantCharacter c =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α zeta ∧ latticePairing T α eta = 0) := by
  have ha :
      ((unipotentCentralizerIntersectionTorusAction i zeta eta hU).restrict
        (𝟙 T.toGrp)).IsEquivariant (AutomorphicAction.conjugation i) iU := by
    intro V t g
    simpa only [AutomorphicAction.restrict_act, Grp.id_hom_hom, Category.id_comp,
      Category.comp_id] using
      unipotentCentralizerIntersectionTorusAction_isEquivariant i zeta eta hU t g
  simpa only [characterRestrict_id, AddMonoidHom.id_apply] using
    characterRestrict_determinant_unipotent_inf_centralizer hT i
      (unipotentCentralizerIntersectionTorusAction i zeta eta hU) (𝟙 T.toGrp)
      zeta eta hU ha c

end TorusDeterminants

end Dynamic

end Langlands.GroupScheme
