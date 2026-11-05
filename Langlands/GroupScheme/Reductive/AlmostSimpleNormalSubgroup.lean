import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Reductive.NormalUnipotentCommutation

/-! # Almost-simple normal factors and smooth connected normal subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G A H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- A normal almost-simple factor either lies in a smooth connected normal
subgroup or commutes with that subgroup on every test scheme. -/
theorem IsAlmostSimple.range_le_or_commute_of_normal
    (hA : IsAlmostSimple A) (a : A ⟶ G) (j : H ⟶ G)
    (ha : IsClosedSubgroup a) (hj : IsClosedSubgroup j)
    (han : (SubgroupFunctor.range a).IsNormal)
    (hjn : (SubgroupFunctor.range j).IsNormal) :
    SubgroupFunctor.range a ≤ SubgroupFunctor.range j ∨
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ A.X) (y : T ⟶ H.X),
        Commute (x ≫ a.hom.hom) (y ≫ j.hom.hom) := by
  let : Smooth A.X.hom := hA.isSemisimple.isConnectedReductive.smooth
  let : ConnectedSpace A.X.left := hA.isSemisimple.isConnectedReductive.connectedSpace
  let : IsClosedImmersion a.hom.hom.left := ha
  let : Mono a.hom.hom := Over.mono_of_mono_left _
  let D := (normalCommutator a j ha hj han hjn).val
  have hD := (normalCommutator a j ha hj han hjn).property
  let : Smooth D.group.X.hom := hD.1.1
  let : GeometricallyConnected D.group.X.hom := hD.1.2.2.1
  have hDc : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  let p := D.minimalHom a ha (factorsThrough_commutatorMap_left a j han)
  let q := D.minimalHom j hj (factorsThrough_commutatorMap_right a j hjn)
  have hp : p ≫ a = D.inclusion :=
    D.minimalHom_comp a ha (factorsThrough_commutatorMap_left a j han)
  have hq : q ≫ j = D.inclusion :=
    D.minimalHom_comp j hj (factorsThrough_commutatorMap_right a j hjn)
  have hp' : p.hom.hom ≫ a.hom.hom = D.inclusion.hom.hom :=
    congrArg (fun f => f.hom.hom) hp
  have hq' : q.hom.hom ≫ j.hom.hom = D.inclusion.hom.hom :=
    congrArg (fun f => f.hom.hom) hq
  have hpc : IsClosedSubgroup p :=
    IsClosedSubgroup.of_comp ha (by rw [hp]; exact D.closed)
  have hpn : (SubgroupFunctor.range p).IsNormal := by
    intro T g x _ hx
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hx' : (v ≫ p.hom.hom) ≫ a.hom.hom ∈
        (SubgroupFunctor.range D.inclusion).carrier T := by
      apply SubgroupFunctor.mem_range.2
      refine ⟨v, ?_⟩
      rw [← hp, Grp.comp_hom_hom, Category.assoc]
    have hn := hD.2 T (g ≫ a.hom.hom) _ (Subgroup.mem_top _) hx'
    obtain ⟨v', hv'⟩ := SubgroupFunctor.mem_range.1 hn
    apply SubgroupFunctor.mem_range.2
    refine ⟨v', ?_⟩
    apply (cancel_mono a.hom.hom).mp
    change v' ≫ D.inclusion.hom.hom = _ at hv'
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hp'] using hv'
  rcases hA.normalSubgroup_trivial_or_full D.group p hpc inferInstance hDc hpn with
    hbot | htop
  · right
    intro T x y
    have hx : (lift x y ≫ D.factor) ≫ p.hom.hom ∈
        (SubgroupFunctor.range p).carrier T :=
      SubgroupFunctor.mem_range.2 ⟨lift x y ≫ D.factor, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    have he := congrArg (fun z => z ≫ a.hom.hom) hx
    have hcomm : (x ≫ a.hom.hom) * (y ≫ j.hom.hom) *
        (x ≫ a.hom.hom)⁻¹ * (y ≫ j.hom.hom)⁻¹ = 1 := by
      rw [Category.assoc _ p.hom.hom a.hom.hom, hp',
        D.factor_comp_points, commutatorMap_lift, MonObj.one_comp] at he
      exact he
    apply (commute_iff_eq _ _).2
    exact (mul_inv_eq_iff_eq_mul).mp (mul_inv_eq_one.mp hcomm)
  · left
    intro T z hz
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hz
    have hx : x ∈ (SubgroupFunctor.range p).carrier T := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨d, hd⟩ := SubgroupFunctor.mem_range.1 hx
    refine SubgroupFunctor.mem_range.2 ⟨d ≫ q.hom.hom, ?_⟩
    rw [Category.assoc, hq', ← hp', ← Category.assoc, hd]

end Langlands.GroupScheme
