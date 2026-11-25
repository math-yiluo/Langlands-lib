/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PicardGroup

/-! # Frames for invertible modules on the standard projective-line charts

## References

* Stacks Project, Tag 0BXJ, proof
* Stacks Project, Tag 0BXJ, proof, first paragraph,
  specialized to the projective line over a field
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

/-- An invertible module has a free generator on each of the two standard charts. -/
theorem exists_standardChart_frames (k : Type u) [Field k]
    (L : (ProjectiveLine (Spec (.of k))).Modules) [Scheme.Modules.IsInvertible L]
    (i : ULift.{u} (Fin 2)) :
    ∃ g : Γ(L, standardOpen _ (Spec (.of k)) i), Scheme.Modules.IsFreeGenerator g := by
  let U := chart k {i}
  let r := polyEquivChart k (ne_other i)
  have : IsDomain Γ(ProjectiveLine (Spec (.of k)), U) := r.symm.toMulEquiv.isDomain _
  have : IsPrincipalIdealRing Γ(ProjectiveLine (Spec (.of k)), U) :=
    IsPrincipalIdealRing.of_surjective r r.surjective
  have hU : IsAffineOpen U := isAffineOpen_chart k (Set.singleton_nonempty i)
  have := Scheme.Modules.invertible_sections_of_isAffineOpen L hU
  obtain ⟨f⟩ := CommRing.Pic.mk_eq_one_iff.mp
    (Subsingleton.elim
      (CommRing.Pic.mk Γ(ProjectiveLine (Spec (.of k)), U) Γ(L, U)) 1)
  have hg : Scheme.Modules.IsFreeGenerator (f.symm 1) :=
    Scheme.Modules.isFreeGenerator_of_bijective_smul L hU (by
      convert f.symm.bijective using 1
      ext a
      simp only [← map_smul, smul_eq_mul, mul_one])
  exact ⟨_, hg.map (chart_singleton k i).ge⟩

end AlgebraicGeometry.ProjectiveLine
