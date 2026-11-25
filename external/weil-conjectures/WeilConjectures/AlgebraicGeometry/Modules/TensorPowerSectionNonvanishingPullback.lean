/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Pullback of tensor-power sections and their nonvanishing loci

## References

* Stacks Project, Modules, Tags 01CD and 01CT
* Morphisms, Tag 0892, part (2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A section of a positive tensor power pulls back to a section of the same power
of the pulled-back invertible module, with inverse-image nonvanishing locus.
-/
theorem exists_tensorPow_section_nonvanishing_pullback {X Y : Scheme.{u}}
    (g : Y ⟶ X) (L : X.Modules) [L.IsInvertible] (n : ℕ) (hn : 0 < n)
    (s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤)) :
    ∃ t : (((tensorPullback g).obj L).tensorPow n).val.presheaf.obj (Opposite.op ⊤),
      nonvanishingLocus (((tensorPullback g).obj L).tensorPow n) t =
        g ⁻¹' nonvanishingLocus (L.tensorPow n) s := by
  classical
  have _hpos : 0 < n := hn
  let a := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  obtain ⟨b⟩ := nonempty_pullback_tensorPow_iso g L n
  obtain ⟨c⟩ := tensorPow_iso (a.app L).symm n
  let e := a.app (L.tensorPow n) ≪≫ b ≪≫ c
  let r : Γ((tensorPullback g).obj (L.tensorPow n), ⊤) :=
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
      (L.tensorPow n)).val.app (Opposite.op ⊤) s
  refine ⟨e.hom.app ⊤ r, ?_⟩
  rw [nonvanishingLocus_iso e r]
  ext y
  exact nonvanishing_tensorPullback g (L.tensorPow n) s y

end AlgebraicGeometry.Scheme.Modules
