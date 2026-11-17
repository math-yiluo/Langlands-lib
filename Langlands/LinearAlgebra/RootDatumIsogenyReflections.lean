import Langlands.LinearAlgebra.RootDatumIsogenyChambers

/-! # Reflection compatibility of root-datum isogenies -/

noncomputable section

universe u v u' v'

namespace Langlands.LinearAlgebra.RootDatumIsogeny

variable {p : ℕ} {J : Type v} {X Y : Type u} {J' : Type v'} {X' Y' : Type u'}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
  [Finite J] [Finite J']
  [Module.Finite ℤ X] [Module.Finite ℤ Y]
  [Module.Finite ℤ X'] [Module.Finite ℤ Y']
  {P : RootDatum J X Y} {Q : RootDatum J' X' Y'}
  [P.IsReduced] [Q.IsReduced]

/-- Reflection compatibility for the root factors and the root-index bijection. -/
def PreservesReflections (f : RootDatumIsogeny p P Q) : Prop :=
  ∀ i j : J, f.rootFactor (P.reflectionPerm i j) = f.rootFactor j ∧
    f.indexEquiv (P.reflectionPerm i j) =
      Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j)

/-- Corresponding reflections preserve both root factors and the root bijection. -/
theorem reflectionPerm_compatibility (f : RootDatumIsogeny p P Q) (i j : J) :
    f.rootFactor (P.reflectionPerm i j) = f.rootFactor j ∧
      f.indexEquiv (P.reflectionPerm i j) =
        Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j) := by
  let a := P.reflectionPerm i j
  let b := Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j)
  have he : (f.rootFactor a : ℤ) • Q.root (f.indexEquiv a) =
      (f.rootFactor j : ℤ) • Q.root b := by
    rw [← f.root_weightMap a]
    change f.weightMap (P.root (P.reflectionPerm i j)) = _
    rw [P.root_reflectionPerm, f.weightMap_reflection, f.root_weightMap, map_smul]
    rw [← Q.root_reflectionPerm]
  have hp : 0 < (f.rootFactor a : ℤ) := by exact_mod_cast f.rootFactor_pos a
  have hq : 0 < (f.rootFactor j : ℤ) := by exact_mod_cast f.rootFactor_pos j
  have hdep : ¬ LinearIndependent ℤ ![Q.root (f.indexEquiv a), Q.root b] := by
    intro h
    have hz := (LinearIndependent.pair_iff.mp h)
      (f.rootFactor a : ℤ) (-(f.rootFactor j : ℤ))
      (by rw [neg_smul, he, add_neg_cancel])
    exact (ne_of_gt hp) hz.1
  have hr : Q.root (f.indexEquiv a) = Q.root b := by
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := Q) _ _ hdep with h | h
    · exact h
    · have hc := congrArg (fun x => Q.toLinearMap x (Q.coroot b)) he
      simp only [h, map_smul, map_neg, LinearMap.smul_apply, LinearMap.neg_apply,
        Q.root_coroot_two, smul_eq_mul] at hc
      omega
  have hc := congrArg (fun x => Q.toLinearMap x (Q.coroot b)) he
  simp only [hr, map_smul, LinearMap.smul_apply, Q.root_coroot_two, smul_eq_mul] at hc
  refine ⟨?_, Q.root.injective hr⟩
  exact_mod_cast (by omega : (f.rootFactor a : ℤ) = (f.rootFactor j : ℤ))

/-- Every supplied root-datum isogeny satisfies reflection compatibility. -/
theorem preservesReflections (f : RootDatumIsogeny p P Q) : f.PreservesReflections :=
  f.reflectionPerm_compatibility

/-- Root factors are constant along each reflection orbit. -/
theorem rootFactor_reflectionPerm (f : RootDatumIsogeny p P Q) (i j : J) :
    f.rootFactor (P.reflectionPerm i j) = f.rootFactor j :=
  (f.reflectionPerm_compatibility i j).1

/-- The root bijection intertwines corresponding reflections. -/
theorem indexEquiv_reflectionPerm (f : RootDatumIsogeny p P Q) (i j : J) :
    f.indexEquiv (P.reflectionPerm i j) =
      Q.reflectionPerm (f.indexEquiv i) (f.indexEquiv j) :=
  (f.reflectionPerm_compatibility i j).2

/-- The inverse root bijection also intertwines corresponding reflections. -/
theorem indexEquiv_symm_reflectionPerm (f : RootDatumIsogeny p P Q) (i j : J') :
    f.indexEquiv.symm (Q.reflectionPerm i j) =
      P.reflectionPerm (f.indexEquiv.symm i) (f.indexEquiv.symm j) := by
  apply f.indexEquiv.injective
  simp only [Equiv.apply_symm_apply, f.indexEquiv_reflectionPerm]

end Langlands.LinearAlgebra.RootDatumIsogeny
