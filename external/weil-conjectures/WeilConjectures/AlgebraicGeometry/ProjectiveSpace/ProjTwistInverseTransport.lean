/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

import WeilConjectures.AlgebraicGeometry.ProjShiftedFreeTwist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineTwist

/-!
# Transport of a polynomial Proj twist to the projective line

## References

* Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any chart-compatible comparison transports the Proj twist to the projective-space twist. -/
theorem proj_twist_inverse_transport (k : Type u) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k) (d : ℤ) :
    Nonempty ((Scheme.Modules.pullback C.iso.inv).obj
      (twist (homogeneousSubmodule (Fin 2) k) d) ≅
        ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) := by
  classical
  let L := ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d
  let T := ProjectiveLine.twistData (Spec (.of k)) d
  obtain ⟨C', ⟨L', ⟨T'⟩, ⟨e'⟩⟩, _⟩ := proj_shifted_free_is_twist k d
  have hcov : (⨆ i : ULift.{u} (Fin 2),
      basicOpen (homogeneousSubmodule (Fin 2) k) (X i.down)) = ⊤ := by
    have h := iSup_basicOpen_eq_top' (homogeneousSubmodule (Fin 2) k)
      X (fun i ↦ ⟨1, isHomogeneous_X k i⟩) (adjoin_range_X_eq_top (Fin 2) k)
    refine top_le_iff.mp fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hC : C'.iso.hom = C.iso.hom := by
    apply (linearCover (homogeneousSubmodule (Fin 2) k)
      (fun j : ULift.{u} (Fin 2) ↦ X j.down)
      (fun j ↦ X_mem_homogeneousSubmodule_one k j.down) hcov).hom_ext
    intro i
    exact (C'.chart_eq i).trans (C.chart_eq i).symm
  let T₀ := ProjectiveLine.twistData (Spec (.of k)) d
  obtain ⟨e₀, _, _⟩ := T₀.existsUnique_iso T'
  obtain ⟨e₁, _, _⟩ := T₀.existsUnique_iso T
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction C'.iso.hom
  let a := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction C'.iso.hom)
  let e := e' ≪≫ a.app L' ≪≫
    (Scheme.Modules.pullback C'.iso.hom).mapIso (e₀.symm ≪≫ e₁) ≪≫
    (Scheme.Modules.pullbackCongr hC).app L
  exact ⟨(Scheme.Modules.pullback C.iso.inv).mapIso e ≪≫
    (Scheme.Modules.pullbackComp C.iso.inv C.iso.hom).app L ≪≫
    (Scheme.Modules.pullbackCongr C.iso.inv_hom_id).app L ≪≫
    (Scheme.Modules.pullbackId _).app L⟩

end AlgebraicGeometry.Proj
