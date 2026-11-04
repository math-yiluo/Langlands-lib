import Langlands.Topology.GroupAction.InducedCharts
import Langlands.Topology.GroupAction.InducedStages
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.GroupTheory.Index

/-! # Covering maps from subgroup restriction on actual induced spaces -/

noncomputable section

universe u v w

namespace Langlands.TopologicalInduction

open Topology Set

section Helpers

variable {A : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Apply the same homeomorphism separately to every actual coproduct copy. -/
private def copiesCongr (e : X ≃ₜ Y) : (Σ _ : A, X) ≃ₜ (Σ _ : A, Y) :=
  (Equiv.sigmaCongrRight fun _ : A => e.toEquiv).toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ => continuous_sigmaMk.comp e.continuous)
    (isOpenMap_sigma.mpr fun _ => isOpenMap_sigmaMk.comp e.isOpenMap)

/-- The projection of a product with a discrete space is evenly covered. -/
private theorem evenlyCovered_fst (D : Type w) [TopologicalSpace D]
    [DiscreteTopology D] (x : X) :
    IsEvenlyCovered (Prod.fst : X × D → X) x D := by
  refine ⟨inferInstance, univ, mem_univ _, isOpen_univ, isOpen_univ, ?_, ?_⟩
  · exact (Homeomorph.Set.univ (X × D)).trans
      ((Homeomorph.Set.univ X).symm.prodCongr (Homeomorph.refl D))
  · intro z
    rfl

end Helpers

section Untwist

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) {X : Type v} [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X]

/-- In each coset copy, move the local coordinate by its chosen representative. -/
private def copiesUntwist (hH : IsOpen (H : Set G)) :
    CosetCopies H X ≃ₜ X × (G ⧸ H) := by
  letI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  exact
    { toFun := fun p => (p.1.out • p.2, p.1)
      invFun := fun p => ⟨p.2, p.2.out⁻¹ • p.1⟩
      left_inv := fun ⟨c, x⟩ => by simp
      right_inv := fun ⟨x, c⟩ => by simp
      continuous_toFun := continuous_sigma fun c =>
        (continuous_const_smul c.out).prodMk continuous_const
      continuous_invFun := continuous_prod_of_discrete_right.mpr fun c =>
        continuous_sigmaMk.comp (continuous_const_smul c.out⁻¹) }

/-- Induction of a restricted full-group space is a product with the coset set.
The homeomorphism uses chosen coset representatives and is not asserted equivariant. -/
def untwistHomeomorph (hH : IsOpen (H : Set G)) :
    Space H X ≃ₜ X × (G ⧸ H) :=
  (cosetCopiesHomeomorph H hH).symm.trans (copiesUntwist H hH)

@[simp]
theorem untwistHomeomorph_symm_apply (hH : IsOpen (H : Set G))
    (x : X) (c : G ⧸ H) :
    (untwistHomeomorph H hH).symm (x, c) = mk H c.out (c.out⁻¹ • x) := rfl

end Untwist

section Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H J : Subgroup G} (hHJ : H ≤ J)
  {X : Type v} [TopologicalSpace X] [MulAction J X] [ContinuousSMul J X]

/-- Restrict the given `J` action along the actual subgroup inclusion. -/
abbrev subgroupRestrictionAction : MulAction H X :=
  MulAction.compHom X (Subgroup.inclusion hHJ)

/-- The original quotient with exactly the restricted action, made explicit so that
no instance search must guess the intermediate subgroup. -/
abbrev SubgroupSource :=
  @Space G _ H X (subgroupRestrictionAction hHJ)

omit [IsTopologicalGroup G] in
/-- The restricted action is continuous on the original topology. -/
theorem continuousSMul_subgroupRestrictionAction :
    letI := subgroupRestrictionAction (X := X) hHJ
    ContinuousSMul H X := by
  let := subgroupRestrictionAction (X := X) hHJ
  exact MulAction.continuousSMul_compHom
    (continuous_subtype_val.subtype_mk (fun h => hHJ h.property))

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [ContinuousSMul J X] in
private theorem subgroupUnit_smul (h : H) (x : X) :
    unit J ((Subgroup.inclusion hHJ h) • x) = (h : G) • unit J x :=
  unit_subgroup_smul (Subgroup.inclusion hHJ h) x

/-- Forget the smaller balancing subgroup while retaining the original local point. -/
def subgroupMap : C(SubgroupSource (X := X) hHJ, Space J X) := by
  letI := subgroupRestrictionAction (X := X) hHJ
  letI := continuousSMul_subgroupRestrictionAction (X := X) hHJ
  exact extend ⟨unit J, continuous_unit⟩ (subgroupUnit_smul hHJ)

@[simp]
theorem subgroupMap_mk (g : G) (x : X) :
    subgroupMap hHJ (@mk G _ H X (subgroupRestrictionAction hHJ) g x) = mk J g x :=
  smul_unit g x

theorem subgroupMap_smul (g : G) (z : SubgroupSource (X := X) hHJ) :
    subgroupMap hHJ (g • z) = g • subgroupMap hHJ z := by
  let := subgroupRestrictionAction (X := X) hHJ
  exact lift_smul _ (subgroupUnit_smul hHJ) g z

omit [IsTopologicalGroup G] in
/-- The relative subgroup is open in the intermediate group. -/
theorem isOpen_subgroupOf (hH : IsOpen (H : Set G)) :
    IsOpen (H.subgroupOf J : Set J) :=
  hH.preimage continuous_subtype_val

/-- A global product chart for the actual subgroup-restriction map.
Its first coordinate will be proved to be the original map itself. -/
def subgroupProductHomeomorph (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G)) :
    SubgroupSource (X := X) hHJ ≃ₜ Space J X × (J ⧸ H.subgroupOf J) := by
  letI := subgroupRestrictionAction (X := X) hHJ
  letI := continuousSMul_subgroupRestrictionAction (X := X) hHJ
  exact (stagesHomeomorph hHJ).symm.trans
    ((cosetCopiesHomeomorph J (X := Space (H.subgroupOf J) X) hJ).symm.trans
      ((copiesCongr (A := G ⧸ J)
        (untwistHomeomorph (H.subgroupOf J) (isOpen_subgroupOf hH))).trans
        ((Homeomorph.sigmaProdDistrib (X := fun _ : G ⧸ J => X)
          (Y := J ⧸ H.subgroupOf J)).symm.trans
          ((cosetCopiesHomeomorph J hJ).prodCongr (Homeomorph.refl _)))))

/-- The original map on the inverse product chart is exactly projection. -/
@[simp]
theorem subgroupMap_product_symm (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G))
    (y : Space J X) (c : J ⧸ H.subgroupOf J) :
    subgroupMap hHJ ((subgroupProductHomeomorph hHJ hH hJ).symm (y, c)) = y := by
  let := subgroupRestrictionAction (X := X) hHJ
  let := continuousSMul_subgroupRestrictionAction (X := X) hHJ
  obtain ⟨⟨d, x⟩, rfl⟩ := (cosetCopiesHomeomorph J (X := X) hJ).surjective y
  dsimp only [subgroupProductHomeomorph]
  erw [Homeomorph.symm_trans_apply, Homeomorph.symm_trans_apply,
    Homeomorph.symm_trans_apply, Homeomorph.symm_trans_apply]
  simp only [Homeomorph.symm_symm, Homeomorph.prodCongr_symm,
    Homeomorph.coe_prodCongr, Prod.map_apply, Homeomorph.refl_symm,
    Homeomorph.refl_apply, Homeomorph.symm_apply_apply, Homeomorph.sigmaProdDistrib_apply]
  change subgroupMap hHJ
    (stagesHomeomorph hHJ
      (mk J d.out ((untwistHomeomorph (H.subgroupOf J) (isOpen_subgroupOf hH)).symm
        (x, c)))) = mk J d.out x
  rw [untwistHomeomorph_symm_apply]
  erw [stagesHomeomorph_mk, subgroupMap_mk]
  rw [mk_balance]
  simp

/-- The first product coordinate is the unchanged balanced-quotient map. -/
@[simp]
theorem subgroupProductHomeomorph_fst (hH : IsOpen (H : Set G))
    (hJ : IsOpen (J : Set G)) (z : SubgroupSource (X := X) hHJ) :
    (subgroupProductHomeomorph hHJ hH hJ z).1 = subgroupMap hHJ z := by
  have h := subgroupMap_product_symm hHJ hH hJ
    (subgroupProductHomeomorph hHJ hH hJ z).1
    (subgroupProductHomeomorph hHJ hH hJ z).2
  simpa using h.symm

/-- Every target point has an evenly covered neighbourhood with the full relative coset set. -/
theorem subgroupMapEvenlyCovered (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G))
    (y : Space J X) :
    IsEvenlyCovered (subgroupMap hHJ : SubgroupSource hHJ → Space J X) y
      (J ⧸ H.subgroupOf J) := by
  let : DiscreteTopology (J ⧸ H.subgroupOf J) :=
    QuotientGroup.discreteTopology (isOpen_subgroupOf hH)
  have h := (evenlyCovered_fst (J ⧸ H.subgroupOf J) y).comp_homeomorph
    (subgroupProductHomeomorph hHJ hH hJ)
  simpa only [Function.comp_def, subgroupProductHomeomorph_fst] using h

/-- Subgroup restriction is an actual covering, without a finite-index premise. -/
theorem isCoveringMap_subgroupMap (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G)) :
    IsCoveringMap (subgroupMap hHJ : SubgroupSource (X := X) hHJ → Space J X) :=
  fun y => (subgroupMapEvenlyCovered hHJ hH hJ y).to_isEvenlyCovered_preimage

/-- All points of the literal original fiber correspond to relative cosets. -/
def subgroupFiberHomeomorph (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G))
    (y : Space J X) :
    (J ⧸ H.subgroupOf J) ≃ₜ (subgroupMap hHJ : SubgroupSource hHJ → Space J X) ⁻¹' {y} :=
  (subgroupMapEvenlyCovered hHJ hH hJ y).fiberHomeomorph

/-- Finite relative index gives finite literal fibers. -/
theorem finite_subgroupMap_fiber [Finite (J ⧸ H.subgroupOf J)]
    (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G)) (y : Space J X) :
    Finite ((subgroupMap hHJ : SubgroupSource hHJ → Space J X) ⁻¹' {y}) :=
  Finite.of_equiv (J ⧸ H.subgroupOf J) (subgroupFiberHomeomorph hHJ hH hJ y).toEquiv

/-- The degree of the actual map is exactly the relative subgroup index. -/
theorem card_subgroupMap_fiber (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G))
    (y : Space J X) :
    Nat.card ((subgroupMap hHJ : SubgroupSource hHJ → Space J X) ⁻¹' {y}) = H.relIndex J :=
  Nat.card_congr (subgroupFiberHomeomorph hHJ hH hJ y).toEquiv.symm

/-- With finite relative index the original subgroup map is proper. -/
theorem isProperMap_subgroupMap [Finite (J ⧸ H.subgroupOf J)]
    (hH : IsOpen (H : Set G)) (hJ : IsOpen (J : Set G)) :
    IsProperMap (subgroupMap hHJ : SubgroupSource (X := X) hHJ → Space J X) := by
  have h := isProperMap_fst_of_compactSpace.comp
    (subgroupProductHomeomorph (X := X) hHJ hH hJ).isProperMap
  simpa only [Function.comp_def, subgroupProductHomeomorph_fst] using h

end Subgroup

end Langlands.TopologicalInduction
