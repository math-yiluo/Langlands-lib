/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Finite
import WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
/-! Source: Stacks Project, Sites Tag 0738(4) (blueprint: aux-weil-pbc-affine-sections-colimit). -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Sections on an affine étale object preserve filtered colimits of sheaves for the
finite affine étale pretopology. The proof uses finite affine refinements of coverings,
filtered colimit representatives on the finite family and the sheaf equalizer condition.
The empty covering is included.

Source: Stacks Project, Sites Tag 0738(4) and Tag 00VM; Categories Tag 002W.
(blueprint: aux-weil-pbc-affine-sections-colimit).
Proof: evaluation preserves presheaf colimits. For a finite covering presieve,
lift its compatible family to a common stage of the filtered diagram. There are
finitely many pairs of covering arrows, so the eventual equality criterion at
those pullbacks and a filtered wide span make the family compatible at one stage.
The stagewise sheaf condition glues it. Separatedness follows by the same finite
wide-span argument applied to two candidate sections. Hence the presheaf colimit
is a sheaf on the finite affine pretopology. Inclusion creates its colimit and
evaluation preserves it; uniqueness of colimits transports this to K. -/
theorem affineSections_colimit
    {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    (E : J ⥤ Sheaf (Scheme.fullAffineEtaleTopology S) (Type (u + 1)))
    (K : Cocone E) (hK : IsColimit K) (W : S.FullAffineEtale) :
    Nonempty (IsColimit (((sheafSections (Scheme.fullAffineEtaleTopology S)
      (Type (u + 1))).obj (op W)).mapCocone K))  := by
  obtain ⟨P, hP⟩ := Scheme.fullAffineEtalePrecoverage_isPretopology S
  have hfinite : Scheme.fullAffineEtalePrecoverage S ≤ Precoverage.finite S.FullAffineEtale := by
    intro X R hR
    obtain ⟨n, V, f, rfl, _, _⟩ := hR
    exact Precoverage.ofArrows_mem_finite V f
  have : CreatesColimit E
      (sheafToPresheaf (Scheme.fullAffineEtaleTopology S) (Type (u + 1))) :=
    Sheaf.createsColimitOfIsSheaf E (fun e he ↦ by
      rw [isSheaf_iff_isSheaf_of_type]
      change Presieve.IsSheaf (Scheme.fullAffineEtalePrecoverage S).toGrothendieck e.pt
      have hcov : P.toCoverage.toPrecoverage = Scheme.fullAffineEtalePrecoverage S := hP
      have ht : P.toCoverage.toGrothendieck =
          (Scheme.fullAffineEtalePrecoverage S).toGrothendieck :=
        (Coverage.toGrothendieck_toPrecoverage P.toCoverage).symm.trans
          (congrArg Precoverage.toGrothendieck hcov)
      exact ht ▸ ((Presieve.isSheaf_coverage P.toCoverage e.pt).mpr (by
        intro X R hR
        have hf : R.uncurry.Finite := hfinite X (by simpa [hP] using hR)
        exact CategoryTheory.finitePresieve_isSheafFor_filteredColimit _ e he R hf
          (fun i ↦ Presieve.IsSheaf.isSheafFor_of_mem_precoverage
            ((isSheaf_iff_isSheaf_of_type _ _).mp (E.obj i).property)
            (by simpa [hP] using hR)))))
  let F := (sheafSections (Scheme.fullAffineEtaleTopology S) (Type (u + 1))).obj (op W)
  have : PreservesColimit E F := by
    change PreservesColimit E
      (sheafToPresheaf (Scheme.fullAffineEtaleTopology S) (Type (u + 1)) ⋙
        (evaluation _ _).obj (op W))
    infer_instance
  exact ⟨isColimitOfPreserves F hK⟩
end AlgebraicGeometry
