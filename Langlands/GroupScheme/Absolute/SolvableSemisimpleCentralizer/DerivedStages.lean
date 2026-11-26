import Langlands.GroupScheme.Derived.Action
import Langlands.GroupScheme.Derived.ConnectedSmoothness
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationFieldPoints
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # Smooth connected stages of the derived series -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.SemisimpleCentralizer

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

omit [IsAlgClosed k] in
/-- The point map of a composite is the composite of the point maps. -/
theorem pointMap_comp {H Q : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) (q : G ⟶ Q) :
    rationalPoints.map (i ≫ q) = (rationalPoints.map q).comp (rationalPoints.map i) := by
  apply MonoidHom.ext
  intro x
  exact (Category.assoc x i.hom.hom q.hom.hom).symm

/-- Commutation of rational points of a smooth affine group is scheme-theoretic. -/
theorem isCommMonObj_of_commuting_points [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (h : ∀ x y : rationalPoints G, x * y = y * x) : IsCommMonObj G.X := by
  have : Smooth (G.X ⊗ G.X).hom := smooth_tensor _ _ inferInstance inferInstance
  have : IsReduced (G.X ⊗ G.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (G.X ⊗ G.X).hom
  refine ⟨hom_ext_rationalPoints fun z => ?_⟩
  let x := z ≫ fst G.X G.X
  let y := z ≫ snd G.X G.X
  have hz : lift x y = z := by simp [x, y]
  rw [← hz, ← Category.assoc, lift_braiding_hom, ← Hom.mul_def, ← Hom.mul_def]
  exact h y x

private theorem rational_range_derived_image [Smooth G.X.hom]
    [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (E : GeneratedImage (commutatorMap (𝟙 G) (𝟙 G)))
    (hE : E.HasSmoothConnectedGeneration) :
    (rationalPoints.map E.inclusion).range = commutator (rationalPoints G) := by
  obtain ⟨hA, hft, _, hI⟩ := smoothConnectedAffineGeometry.2 k G G
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
  apply le_antisymm
  · apply ConnectedGenerationField.generatedImage_range_le E hE
    intro a
    rw [commutatorMap_points, Grp.id_hom_hom, Category.comp_id, Category.comp_id,
      ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · show ⁅(⊤ : Subgroup (rationalPoints G)), ⊤⁆ ≤ (rationalPoints.map E.inclusion).range
    rw [Subgroup.commutator_le]
    intro x _ y _
    exact E.isDerivedSubgroup.containsCommutators _ x y

/-- The abstract derived series of rational points is represented at every stage by a smooth
connected normal closed subgroup, computed using the actual scheme-theoretic derived subgroup. -/
theorem exists_derived_stage [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (n : ℕ) : ∃ (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
      IsClosedSubgroup i ∧ Smooth N.X.hom ∧ ConnectedSpace N.X.left ∧
        (SubgroupFunctor.range i).IsNormal ∧
          (rationalPoints.map i).range = derivedSeries (rationalPoints G) n := by
  induction n with
  | zero =>
      have hc : IsClosedSubgroup (𝟙 G) := (derivedSubgroup_total_admissible G).1
      refine ⟨G, 𝟙 G, hc, inferInstance, inferInstance, ?_, ?_⟩
      · rw [SubgroupFunctor.range_id]
        exact fun _ _ _ _ _ => Subgroup.mem_top _
      · change (SubgroupFunctor.range (𝟙 G)).carrier _ = _
        rw [SubgroupFunctor.range_id, derivedSeries_zero]
        rfl
  | succ n ih =>
      obtain ⟨H, j, hj, hHs, hHc, hHn, hHr⟩ := ih
      have : IsAffineHom H.X.hom := hj.isAffineHom
      let e := smoothConnectedCommutatorImage k H hHs inferInstance hHc
      let E := e.val
      have hE : E.HasSmoothConnectedGeneration := e.property
      have heconn : ConnectedSpace E.group.X.left := by
        have : GeometricallyConnected E.group.X.hom := hE.2.2.1
        exact GeometricallyConnected.connectedSpace_of_subsingleton E.group.X.hom
      refine ⟨E.group, E.inclusion ≫ j, E.closed.comp hj, hE.1, heconn,
        E.isDerivedSubgroup.isNormal_comp j hj hHn, ?_⟩
      rw [pointMap_comp, MonoidHom.range_comp, rational_range_derived_image E hE]
      change Subgroup.map (rationalPoints.map j)
        ⁅(⊤ : Subgroup (rationalPoints H)), ⊤⁆ = _
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hHr, derivedSeries_succ]

omit [IsAlgClosed k] in
/-- In a commutative target the point map kills the first derived subgroup. -/
theorem derived_one_le_ker {D : GroupScheme (Spec (CommRingCat.of k))} [IsCommMonObj D.X]
    (q : G ⟶ D) : derivedSeries (rationalPoints G) 1 ≤ (rationalPoints.map q).ker := by
  have h := map_derivedSeries_le_derivedSeries (rationalPoints.map q) 1
  rw [derivedSeries_one (rationalPoints D), commutator_eq_bot, Subgroup.map_le_iff_le_comap] at h
  exact h

/-- Any smooth closed subgroup with rational points in the first derived subgroup of a
connected smooth affine solvable group is unipotent. -/
theorem isUnipotent_of_range_le_derived [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hG : IsSolvableGroupScheme G)
    {N : GroupScheme (Spec (CommRingCat.of k))} [Smooth N.X.hom]
    (i : N ⟶ G) (hi : IsClosedSubgroup i)
    (h : (rationalPoints.map i).range ≤ derivedSeries (rationalPoints G) 1) : IsUnipotent N := by
  obtain ⟨U, D, u, q, hu, hUs, _, hU, _, hq, hD⟩ := solvableTorusQuotient k G hG
  have : IsCommMonObj D.X := IsSplitTorus.isCommMonObj hD
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion u.hom.hom.left := hu
  have : IsReduced N.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ N.X.hom
  have : Mono u.hom.hom := hu.mono_overHom
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range u := by
    apply SubgroupFunctor.range_le_of_algClosed_points hu
    intro x hx
    rw [← hq.2.2.2, mem_range_kernelι_iff]
    exact derived_one_le_ker q (h hx)
  let huRep : (SubgroupFunctor.range u).IsRepresentedBy u := ⟨inferInstance, rfl⟩
  let j := huRep.factorHom i hle
  have hj : j ≫ u = i := huRep.factorHom_comp i hle
  have hjc : IsClosedSubgroup j := by
    have hcomp : j.hom.hom.left ≫ u.hom.hom.left = i.hom.hom.left :=
      congrArg (fun a => a.hom.hom.left) hj
    have : IsClosedImmersion (j.hom.hom.left ≫ u.hom.hom.left) := hcomp.symm ▸ hi
    exact IsClosedImmersion.of_comp _ u.hom.hom.left
  have : Smooth U.X.hom := hUs
  have : IsAffineHom U.X.hom := hu.isAffineHom
  exact unipotentClosedSubgroup k U N j hjc hU

end Langlands.GroupScheme.SemisimpleCentralizer
