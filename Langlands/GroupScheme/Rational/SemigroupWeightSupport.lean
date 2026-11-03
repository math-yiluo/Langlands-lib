import Langlands.GroupScheme.Rational.TangentWeightTransport
import Langlands.GroupScheme.Torus.ActionWeightDecomposition
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Intrinsic split-torus decomposition and semigroup support bounds -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)

include hS

open Classical in
/-- The intrinsic action weight spaces form an internal direct sum for any split torus. -/
theorem isInternal_actionWeightSpace : DirectSum.IsInternal (actionWeightSpace b) := by
  have heq : actionWeightSpace b = b.lieWeightSpace (𝟙 S.toGrp) :=
    funext (actionWeightSpace_eq_lieWeightSpace b)
  rw [heq]
  exact AutomorphicAction.isInternal_lieWeightSpace_of_isSplitTorus k G S hS b (𝟙 _)

open Classical in
/-- The canonical decomposition attached to the intrinsic split-torus action weight spaces. -/
@[instance_reducible]
def actionWeightDecomposition :
    DirectSum.Decomposition (actionWeightSpace b) :=
  (isInternal_actionWeightSpace b hS).chooseDecomposition

/-- Distinct intrinsic character weight spaces are independent. -/
theorem iSupIndep_actionWeightSpace : iSupIndep (actionWeightSpace b) := by
  classical
  exact (isInternal_actionWeightSpace b hS).submodule_iSupIndep

/-- The intrinsic action weight spaces span the actual Lie algebra. -/
theorem iSup_actionWeightSpace_eq_top : (⨆ χ, actionWeightSpace b χ) = ⊤ := by
  classical
  exact (isInternal_actionWeightSpace b hS).submodule_iSup_eq_top

/-- An excluded character weight space is disjoint from a semigroup's full weight span. -/
theorem disjoint_actionWeightSpace_semigroupWeightSpan
    (A : AddSubsemigroup (characterLattice S)) (χ : characterLattice S) (hχ : χ ∉ A) :
    Disjoint (actionWeightSpace b χ) (semigroupWeightSpan b A) := by
  have h := (iSupIndep_actionWeightSpace b hS).disjoint_biSup hχ
  apply disjoint_iff.mpr
  simpa only [semigroupWeightSpan, iSup_subtype] using! h.eq_bot

/-- A support bound follows from tangent containment in the semigroup weight span,
without requiring the subgroup to be represented. -/
theorem actionWeightSupport_subset_of_tangentSubmodule_le
    (A : AddSubsemigroup (characterLattice S)) (F : SubgroupFunctor G)
    (hF : tangentSubmodule F ≤ semigroupWeightSpan b A) :
    actionWeightSupport b F ⊆ A := by
  rintro χ ⟨X, hX0, hXχ, hXF⟩
  by_contra hχ
  exact hX0 ((Submodule.disjoint_def.mp
    (disjoint_actionWeightSpace_semigroupWeightSpan b hS A χ hχ)) X hXχ (hF hXF))

/-- The exact semigroup Lie image has precisely the nonzero ambient weight
spaces indexed by the semigroup as its intrinsic support. -/
theorem HasLieImage.mem_actionWeightSupport_iff
    {F : SubgroupFunctor G} (A : AddSubsemigroup (characterLattice S))
    (hF : HasLieImage F (semigroupWeightSpan b A)) (χ : characterLattice S) :
    χ ∈ actionWeightSupport b F ↔ χ ∈ A ∧ actionWeightSpace b χ ≠ ⊥ := by
  rw [_root_.Langlands.GroupScheme.RelativeRoot.mem_actionWeightSupport_iff,
    (hasLieImage_iff_tangentSubmodule_eq F _).mp hF]
  by_cases hχ : χ ∈ A
  · have hle : actionWeightSpace b χ ≤ semigroupWeightSpan b A :=
      le_iSup (fun ψ : A => actionWeightSpace b ψ.val) ⟨χ, hχ⟩
    rw [inf_eq_left.mpr hle]
    simp only [hχ, true_and]
  · rw [(disjoint_actionWeightSpace_semigroupWeightSpan b hS A χ hχ).eq_bot]
    simp only [ne_eq, not_true_eq_false, hχ, false_and]

section Represented

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (j : H ⟶ G) {F : SubgroupFunctor G}
    (hj : F.IsRepresentedBy j) (hF : b.IsStable F)

include j hj hF

omit [LocallyOfFiniteType G.X.hom] in
/-- A represented stable subgroup's tangent image is the sum of its intersections
with all ambient character weight spaces. -/
theorem tangentSubmodule_eq_iSup_weight_inf :
    tangentSubmodule F = ⨆ χ, actionWeightSpace b χ ⊓ tangentSubmodule F := by
  have : Mono j.hom.hom := hj.1
  let d := b.onRepresentedSubgroup j hj hF
  have hd : (⨆ χ, actionWeightSpace d χ) = ⊤ := iSup_actionWeightSpace_eq_top d hS
  have hmap (χ : characterLattice S) :
      (actionWeightSpace d χ).map (Lie.targetMapLinear j k) =
        actionWeightSpace b χ ⊓ tangentSubmodule F := by
    have h := map_actionWeightSpace_eq_inf_tangentSubmodule b d j
      (fun _ s x => b.onRepresentedSubgroup_act_comp j hj hF s x) χ
    simpa only [hj.2] using h
  calc
    tangentSubmodule F = LinearMap.range (Lie.targetMapLinear j k) :=
      (hasLieImage_iff_tangentSubmodule_eq _ _).mp (hasLieImage_of_isRepresentedBy j hj)
    _ = (⨆ χ, actionWeightSpace d χ).map (Lie.targetMapLinear j k) := by
      rw [hd, Submodule.map_top]
    _ = ⨆ χ, (actionWeightSpace d χ).map (Lie.targetMapLinear j k) :=
      Submodule.map_iSup _ _
    _ = ⨆ χ, actionWeightSpace b χ ⊓ tangentSubmodule F := iSup_congr hmap

/-- For a represented stable subgroup, support containment and tangent containment
in the semigroup weight span are equivalent. -/
theorem actionWeightSupport_subset_iff_tangentSubmodule_le
    (A : AddSubsemigroup (characterLattice S)) :
    actionWeightSupport b F ⊆ A ↔ tangentSubmodule F ≤ semigroupWeightSpan b A := by
  constructor
  · intro hA
    rw [tangentSubmodule_eq_iSup_weight_inf b hS j hj hF]
    refine iSup_le fun χ => ?_
    by_cases hχ : χ ∈ A
    · exact inf_le_left.trans
        (le_iSup (fun ψ : A => actionWeightSpace b ψ.val) ⟨χ, hχ⟩)
    · have hz : actionWeightSpace b χ ⊓ tangentSubmodule F = ⊥ := by
        by_contra hz
        exact hχ (hA ((mem_actionWeightSupport_iff b F χ).mpr hz))
      rw [hz]
      exact bot_le
  · exact actionWeightSupport_subset_of_tangentSubmodule_le b hS A F

end Represented

/-- The support/tangent-span equivalence applies in particular to every smooth
connected invariant closed subgroup in the semigroup realization target. -/
theorem IsSmoothConnectedClosed.actionWeightSupport_subset_iff_tangentSubmodule_le
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F) (hstable : b.IsStable F)
    (A : AddSubsemigroup (characterLattice S)) :
    actionWeightSupport b F ⊆ A ↔ tangentSubmodule F ≤ semigroupWeightSpan b A := by
  obtain ⟨H, j, hj, hclosed, hsmooth, _⟩ := hF
  have : IsAffineHom H.X.hom := hclosed.isAffineHom
  have : Smooth H.X.hom := hsmooth
  exact _root_.Langlands.GroupScheme.RelativeRoot.actionWeightSupport_subset_iff_tangentSubmodule_le
    b hS j hj hstable A

end Langlands.GroupScheme.RelativeRoot
