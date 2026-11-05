import Langlands.GroupScheme.Derived.DynamicRootContainment
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Rational.RootParabolicProper
import Langlands.GroupScheme.Rational.SemigroupWeightSupport

/-! # Nonzero torus weights in the actual derived tangent -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

namespace RelativeRoot

/-- Every nonzero adjoint weight of a split torus lies in the actual
dual-number tangent submodule of the full derived subgroup. -/
theorem weightSpace_le_tangentSubmodule_derivedSubgroup
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    weightSpace i χ ≤ tangentSubmodule (derivedSubgroup G) :=
  (weightSpace_le_tangentSubmodule_subgroup i hT hχ).trans
    (tangentSubmodule_mono (subgroup_le_derivedSubgroup i hT hχ))

/-- If the zero adjoint weight comes from the torus, its tangent submodule
together with the full derived tangent spans the ambient Lie module. -/
theorem tangentSubmodule_derivedSubgroup_sup_torus_eq_top
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hzero : weightSpace i 0 ≤ tangentSubmodule (SubgroupFunctor.range i)) :
    tangentSubmodule (derivedSubgroup G) ⊔
      tangentSubmodule (SubgroupFunctor.range i) = ⊤ := by
  apply top_unique
  rw [← iSup_actionWeightSpace_eq_top (AutomorphicAction.conjugation i) hT]
  apply iSup_le
  intro χ
  rw [actionWeightSpace_conjugation]
  by_cases hχ : χ = 0
  · subst χ
    exact hzero.trans le_sup_right
  · exact (weightSpace_le_tangentSubmodule_derivedSubgroup i hT hχ).trans le_sup_left

end RelativeRoot

namespace IsDerivedSubgroup

variable {D : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G}

/-- Every nonzero adjoint weight lies in the actual tangent of a supplied
derived inclusion. -/
theorem weightSpace_le_tangentSubmodule_range (hd : IsDerivedSubgroup d)
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    weightSpace i χ ≤ RelativeRoot.tangentSubmodule (SubgroupFunctor.range d) := by
  rw [hd.2]
  exact RelativeRoot.weightSpace_le_tangentSubmodule_derivedSubgroup i hT hχ

/-- Explicit zero-weight containment makes the actual derived and torus
tangent submodules span the ambient Lie module. -/
theorem tangentSubmodule_range_sup_torus_eq_top
    (hd : IsDerivedSubgroup d) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hzero : weightSpace i 0 ≤
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range i)) :
    RelativeRoot.tangentSubmodule (SubgroupFunctor.range d) ⊔
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range i) = ⊤ := by
  rw [hd.2]
  exact RelativeRoot.tangentSubmodule_derivedSubgroup_sup_torus_eq_top i hT hzero

/-- Self-centralization of a split torus gives the zero-weight containment,
so its tangent and the actual derived tangent span the ambient Lie module. -/
theorem tangentSubmodule_range_sup_selfCentralizing_torus_eq_top
    (hd : IsDerivedSubgroup d) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    RelativeRoot.tangentSubmodule (SubgroupFunctor.range d) ⊔
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range i) = ⊤ := by
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  apply hd.tangentSubmodule_range_sup_torus_eq_top i hT
  intro X hX
  change X.toMul.val ∈ (SubgroupFunctor.range i).carrier _
  rw [← hself]
  exact Lie.mem_torusCentralizer_of_mem_weightSpace_zero i X.toMul hX

variable [IsAffineHom D.X.hom]

/-- For a supplied actual derived inclusion, every nonzero adjoint weight
lies in the range of its actual differential. -/
theorem weightSpace_le_range_targetMapLinear (hd : IsDerivedSubgroup d)
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ≠ 0) :
    weightSpace i χ ≤ LinearMap.range (Lie.targetMapLinear d k) := by
  let : Mono d.hom.hom := hd.isRepresentedBy.1
  rw [← RelativeRoot.tangentSubmodule_range d, hd.2]
  exact RelativeRoot.weightSpace_le_tangentSubmodule_derivedSubgroup i hT hχ

/-- Under explicit zero-weight containment, the actual differentials of a
derived inclusion and a split torus together span the ambient Lie module. -/
theorem range_targetMapLinear_sup_torus_eq_top
    (hd : IsDerivedSubgroup d) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hzero : weightSpace i 0 ≤
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range i)) :
    LinearMap.range (Lie.targetMapLinear d k) ⊔
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range i) = ⊤ := by
  let : Mono d.hom.hom := hd.isRepresentedBy.1
  rw [← RelativeRoot.tangentSubmodule_range d, hd.2]
  exact RelativeRoot.tangentSubmodule_derivedSubgroup_sup_torus_eq_top i hT hzero

end IsDerivedSubgroup

end Langlands.GroupScheme
