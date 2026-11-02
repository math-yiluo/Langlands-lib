import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Automorphic actions on represented invariant subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G C : GroupScheme S} (a : AutomorphicAction H G)

/-- Stability under the given action, on every scheme over the base. -/
def IsStable (F : SubgroupFunctor G) : Prop :=
  ∀ (T : Over S) (h : T ⟶ H.X) (g : T ⟶ G.X),
    g ∈ F.carrier T → a.act h g ∈ F.carrier T

variable {F : SubgroupFunctor G} (i : C ⟶ G)
    (hi : F.IsRepresentedBy i) (hF : a.IsStable F)

/-- Factor the action morphism through a represented stable subgroup. -/
def representedActionHom : H.X ⊗ C.X ⟶ C.X :=
  Classical.choose (SubgroupFunctor.mem_range.1 (by
    rw [hi.2]
    exact hF _ (fst H.X C.X) (snd H.X C.X ≫ i.hom.hom) (by
      rw [← hi.2]
      exact SubgroupFunctor.mem_range.2 ⟨snd H.X C.X, rfl⟩)))

theorem representedActionHom_comp :
    representedActionHom a i hi hF ≫ i.hom.hom =
      a.act (fst H.X C.X) (snd H.X C.X ≫ i.hom.hom) :=
  Classical.choose_spec (SubgroupFunctor.mem_range.1 (by
    rw [hi.2]
    exact hF _ (fst H.X C.X) (snd H.X C.X ≫ i.hom.hom) (by
      rw [← hi.2]
      exact SubgroupFunctor.mem_range.2 ⟨snd H.X C.X, rfl⟩)))

theorem lift_representedActionHom_comp {T : Over S} (h : T ⟶ H.X)
    (c : T ⟶ C.X) :
    (lift h c ≫ representedActionHom a i hi hF) ≫ i.hom.hom =
      a.act h (c ≫ i.hom.hom) := by
  rw [Category.assoc, representedActionHom_comp, a.naturality,
    lift_fst, lift_snd_assoc]

/-- The actual action on a represented invariant subgroup. Its laws follow by
cancelling the representing monomorphism and using the ambient action laws. -/
def onRepresentedSubgroup : AutomorphicAction H C := by
  letI : Mono i.hom.hom := hi.1
  exact
    { hom := representedActionHom a i hi hF
      one_left := fun c => by
        apply (cancel_mono i.hom.hom).1
        rw [lift_representedActionHom_comp, a.act_one_left]
      mul_left := fun h h' c => by
        apply (cancel_mono i.hom.hom).1
        rw [lift_representedActionHom_comp, lift_representedActionHom_comp,
          lift_representedActionHom_comp, a.act_mul_left]
      mul_right := fun h c c' => by
        apply (cancel_mono i.hom.hom).1
        rw [lift_representedActionHom_comp, MonObj.mul_comp, a.act_mul_right,
          MonObj.mul_comp, lift_representedActionHom_comp,
          lift_representedActionHom_comp] }

/-- The representing inclusion intertwines the constructed and ambient actions. -/
theorem onRepresentedSubgroup_act_comp {T : Over S} (h : T ⟶ H.X)
    (c : T ⟶ C.X) :
    (onRepresentedSubgroup a i hi hF).act h c ≫ i.hom.hom =
      a.act h (c ≫ i.hom.hom) :=
  lift_representedActionHom_comp a i hi hF h c

/-- There is only one action morphism with the required inclusion equation. -/
theorem onRepresentedSubgroup_hom_unique (b : AutomorphicAction H C)
    (hb : b.hom ≫ i.hom.hom =
      a.act (fst H.X C.X) (snd H.X C.X ≫ i.hom.hom)) :
    b.hom = (onRepresentedSubgroup a i hi hF).hom := by
  let : Mono i.hom.hom := hi.1
  apply (cancel_mono i.hom.hom).1
  exact hb.trans (representedActionHom_comp a i hi hF).symm

section CommutativeSource

variable {A : CommGroupScheme S} {K : GroupScheme S}
    (a : AutomorphicAction A.toGrp G) (j : K ⟶ A.toGrp)

/-- For a commutative acting group, the subgroup fixed by a restriction is stable
under the whole acting group. The restricted source need not be smooth. -/
theorem fixed_restrict_isStable : a.IsStable (a.restrict j).fixedSubgroup := by
  intro T h g hg V b k
  rw [a.naturality, restrict_act, ← a.act_mul_left, mul_comm, a.act_mul_left]
  have e := hg V b k
  rw [restrict_act] at e
  rw [e]

variable (i : C ⟶ G) (hi : (a.restrict j).fixedSubgroup.IsRepresentedBy i)

/-- The whole commutative group acts on a group scheme representing the fixed
subgroup of the restricted action. Representability is an explicit input. -/
def onRepresentedFixedSubgroup : AutomorphicAction A.toGrp C :=
  onRepresentedSubgroup a i hi (fixed_restrict_isStable a j)

theorem onRepresentedFixedSubgroup_act_comp {T : Over S}
    (h : T ⟶ A.X) (c : T ⟶ C.X) :
    (onRepresentedFixedSubgroup a j i hi).act h c ≫ i.hom.hom =
      a.act h (c ≫ i.hom.hom) :=
  onRepresentedSubgroup_act_comp a i hi (fixed_restrict_isStable a j) h c

/-- The restricted source acts trivially on the representing fixed subgroup,
including on every nonreduced test scheme. -/
theorem onRepresentedFixedSubgroup_restrict_act {T : Over S}
    (k : T ⟶ K.X) (c : T ⟶ C.X) :
    ((onRepresentedFixedSubgroup a j i hi).restrict j).act k c = c := by
  let : Mono i.hom.hom := hi.1
  apply (cancel_mono i.hom.hom).1
  rw [restrict_act, onRepresentedFixedSubgroup_act_comp]
  have hc : c ≫ i.hom.hom ∈ (a.restrict j).fixedSubgroup.carrier T := by
    rw [← hi.2]
    exact SubgroupFunctor.mem_range.2 ⟨c, rfl⟩
  have e := hc T (𝟙 T) k
  simpa only [Category.id_comp, restrict_act] using e

end CommutativeSource

end Langlands.GroupScheme.AutomorphicAction
