/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line.LineInvertibleClassification
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineTwist
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism

/-! # Automorphisms preserve the degree-one twist over a field

## References

* EGA II, Remark 4.2.7
* Stacks, Tags 0BXJ and 01XS
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine

private lemma finrankH_twist_nonneg (k : Type u) [Field k] (d : ℕ) :
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).finrankH k 0 = d + 1 := by
  obtain ⟨e⟩ := nonempty_H_zero_twist_equiv k d
  change Module.finrank k _ = _
  rw [e.finrank_eq,
    Module.finrank_eq_nat_card_basis (ProjectiveSpace.homogeneousSubmoduleBasis _ k d),
    Nat.card_congr (degreeEqEquivFin d)]
  simp

/-- Pullback by a field-linear projective-line automorphism preserves the actual twist. -/
theorem automorphism_twist_one_over_field (k : Type u) [Field k]
    (a : ProjectiveLine (Spec (.of k)) ≅ ProjectiveLine (Spec (.of k)))
    (ha : a.hom ≫ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) =
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) :
    Nonempty ((Scheme.Modules.pullback a.hom).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1) ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1) := by
  let : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
  obtain ⟨d, ⟨e⟩, _⟩ := existsUnique_degree_of_isInvertible k
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)))
    (fun m ↦ ⟨twistData _ m⟩)
    ((Scheme.Modules.pullback a.hom).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1))
  have hdim : (ProjectiveSpace.twist (ULift.{u} (Fin 2))
      (Spec (.of k)) d).finrankH k 0 = 2 := by
    rw [← Scheme.Modules.finrankH_congr k e 0,
      Scheme.Modules.finrankH_pullback_of_isIso a.hom]
    simpa only [Nat.cast_one] using finrankH_twist_nonneg k 1
  have hd : d = 1 := by
    rcases lt_or_ge d 0 with hd | hd
    · have := subsingleton_H_zero_twist_of_neg k d hd
      have hz : (ProjectiveSpace.twist (ULift.{u} (Fin 2))
          (Spec (.of k)) d).finrankH k 0 = 0 := Module.finrank_zero_of_subsingleton
      omega
    · lift d to ℕ using hd
      rw [finrankH_twist_nonneg] at hdim
      omega
  subst d
  exact ⟨e⟩

end AlgebraicGeometry.ProjectiveLine
