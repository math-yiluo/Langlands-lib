import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.FppfLocalGroupIso
import Langlands.GroupScheme.Rational.InnerDiscrepancyRefinement
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Subgroup-preserving local isomorphisms and stabilizer-valued discrepancies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H A P : GroupScheme S} {U V : Over S}

namespace AutomorphicAction

/-- The acting points preserving a subgroup after every refinement of the test scheme. -/
def subgroupStabilizer (a : AutomorphicAction A G) (F : SubgroupFunctor G) :
    SubgroupFunctor A where
  carrier T :=
    { carrier := {x | ∀ (W : Over S) (t : W ⟶ T) (g : W ⟶ G.X),
          a.act (t ≫ x) g ∈ F.carrier W ↔ g ∈ F.carrier W}
      one_mem' := by
        intro W t g
        rw [MonObj.comp_one, a.act_one_left]
      mul_mem' := by
        intro x y hx hy W t g
        rw [MonObj.comp_mul, a.act_mul_left, hx, hy]
      inv_mem' := by
        intro x hx W t g
        have h := hx W t (a.act (t ≫ x)⁻¹ g)
        rw [a.act_act_inv] at h
        rw [GrpObj.comp_inv]
        exact h.symm }
  comp_mem t x hx W s g := by
    rw [← Category.assoc]
    exact hx W (s ≫ t) g

/-- For conjugation, the subgroup stabilizer is precisely its all-refinement normalizer. -/
theorem conjugation_subgroupStabilizer (F : SubgroupFunctor G) :
    (conjugation (𝟙 G)).subgroupStabilizer F = F.normalizer := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  constructor
  · intro hx W t g hg
    have hf := (hx W t g).mpr hg
    have hb := (hx W t ((t ≫ x)⁻¹ * g * (t ≫ x))).mp
    simp only [conjugation_act, Grp.id_hom_hom, Category.comp_id] at hf hb
    have hcancel : (t ≫ x) * ((t ≫ x)⁻¹ * g * (t ≫ x)) * (t ≫ x)⁻¹ = g := by group
    exact ⟨hf, hb (by rw [hcancel]; exact hg)⟩
  · intro hx W t g
    simp only [conjugation_act, Grp.id_hom_hom, Category.comp_id]
    constructor
    · intro hg
      have h := (hx W t _ hg).2
      have hcancel : (t ≫ x)⁻¹ * ((t ≫ x) * g * (t ≫ x)⁻¹) * (t ≫ x) = g := by
        group
      rwa [hcancel] at h
    · exact fun hg => (hx W t g hg).1

end AutomorphicAction

namespace LocalGroupIso

/-- Each local isomorphism identifies two subgroup functors on every relative test. -/
def PreservesSubgroup (e : LocalGroupIso G H U)
    (F : SubgroupFunctor G) (F' : SubgroupFunctor H) : Prop :=
  ∀ {T : Over S} (c : T ⟶ U) (g : T ⟶ G.X),
    e.toFun c g ∈ F'.carrier T ↔ g ∈ F.carrier T

variable {e : LocalGroupIso G H U} {F : SubgroupFunctor G} {F' : SubgroupFunctor H}

/-- Inverting a subgroup-preserving family preserves the inverse pair of subgroups. -/
theorem PreservesSubgroup.symm (h : e.PreservesSubgroup F F') :
    e.symm.PreservesSubgroup F' F := by
  intro T c g
  exact (h c ((e.toFun c).symm g)).symm.trans
    (by rw [MulEquiv.apply_symm_apply])

/-- Any restriction of the parameter scheme retains subgroup preservation. -/
theorem PreservesSubgroup.refine (h : e.PreservesSubgroup F F') (r : V ⟶ U) :
    (e.refine r).PreservesSubgroup F F' := fun _ _ => h _ _

/-- A discrepancy of subgroup-preserving local isomorphisms preserves the source subgroup. -/
theorem RepresentsDiscrepancy.mem_subgroupStabilizer
    {a : AutomorphicAction A G} (hp : e.PreservesSubgroup F F')
    {T : Over S} {b c : T ⟶ U} {x : T ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a b c x) :
    x ∈ (a.subgroupStabilizer F).carrier T := by
  intro W t g
  rw [← hp (t ≫ b) (a.act (t ≫ x) g), hx t g, hp (t ≫ c) g]

/-- Every value of a discrepancy cocycle lies in the source subgroup's stabilizer. -/
theorem HasDiscrepancy.mem_subgroupStabilizer
    {a : AutomorphicAction A G} {ξ : Cocycle A U}
    (hp : e.PreservesSubgroup F F') (hξ : e.HasDiscrepancy a ξ)
    {T : Over S} (b c : T ⟶ U) :
    ξ.toFun b c ∈ (a.subgroupStabilizer F).carrier T := by
  apply RepresentsDiscrepancy.mem_subgroupStabilizer hp
  intro W t g
  rw [← ξ.naturality]
  exact hξ (t ≫ b) (t ≫ c) g

/-- Lift an inner discrepancy to a supplied monic representative of the source stabilizer. -/
def subgroupInnerCocycle (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (he : e.HasInnerDiscrepancy a)
    (F : SubgroupFunctor G) (F' : SubgroupFunctor H) (hp : e.PreservesSubgroup F F')
    (j : P ⟶ A) (hj : (a.subgroupStabilizer F).IsRepresentedBy j) : Cocycle P U := by
  let : Mono j.hom.hom := hj.1
  apply (e.innerCocycle a ha he).lift j
  intro T b c
  apply SubgroupFunctor.mem_range.mp
  rw [hj.2]
  exact HasDiscrepancy.mem_subgroupStabilizer hp
    (e.innerCocycle_hasDiscrepancy a ha he) b c

/-- The lifted cocycle recovers the original natural discrepancy under the inclusion. -/
theorem subgroupInnerCocycle_comp (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (he : e.HasInnerDiscrepancy a)
    (F : SubgroupFunctor G) (F' : SubgroupFunctor H) (hp : e.PreservesSubgroup F F')
    (j : P ⟶ A) (hj : (a.subgroupStabilizer F).IsRepresentedBy j)
    {T : Over S} (b c : T ⟶ U) :
    (e.subgroupInnerCocycle a ha he F F' hp j hj).toFun b c ≫ j.hom.hom =
      (e.innerCocycle a ha he).toFun b c := by
  let : Mono j.hom.hom := hj.1
  unfold subgroupInnerCocycle
  apply Cocycle.lift_toFun
  intro Z b c
  apply SubgroupFunctor.mem_range.mp
  rw [hj.2]
  exact HasDiscrepancy.mem_subgroupStabilizer hp
    (e.innerCocycle_hasDiscrepancy a ha he) b c

/-- The stabilizer-valued cocycle records the discrepancy for the restricted action. -/
theorem subgroupInnerCocycle_hasDiscrepancy (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (he : e.HasInnerDiscrepancy a)
    (F : SubgroupFunctor G) (F' : SubgroupFunctor H) (hp : e.PreservesSubgroup F F')
    (j : P ⟶ A) (hj : (a.subgroupStabilizer F).IsRepresentedBy j) :
    e.HasDiscrepancy (a.restrict j) (e.subgroupInnerCocycle a ha he F F' hp j hj) := by
  intro T b c g
  rw [AutomorphicAction.restrict_act, e.subgroupInnerCocycle_comp]
  exact e.innerCocycle_hasDiscrepancy a ha he b c g

/-- Triviality in the subgroup stabilizer descends the original local family. -/
def isoOfTrivialSubgroupInnerCocycle (e : LocalGroupIso G H U)
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
    (a : AutomorphicAction A G) (ha : a.IsFaithful) (he : e.HasInnerDiscrepancy a)
    (F : SubgroupFunctor G) (F' : SubgroupFunctor H) (hp : e.PreservesSubgroup F F')
    (j : P ⟶ A) (hj : (a.subgroupStabilizer F).IsRepresentedBy j)
    (htriv : (e.subgroupInnerCocycle a ha he F F' hp j hj).IsTrivial) : G ≅ H :=
  e.descendOfTrivialFppf (a.restrict j) (e.subgroupInnerCocycle a ha he F F' hp j hj)
    (e.subgroupInnerCocycle_hasDiscrepancy a ha he F F' hp j hj) htriv

end LocalGroupIso

end Langlands.GroupScheme
