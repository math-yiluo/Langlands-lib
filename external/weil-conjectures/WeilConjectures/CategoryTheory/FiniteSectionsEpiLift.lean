/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections

/-! # Simultaneous local lifting of finitely many module sections

Source: Stacks Project, Modules on Sites, Tag 093U (3), lifting the chosen generators.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace SheafOfModules

/-- Finitely many sections lift through a module-sheaf epimorphism on a common covering
sieve, including the case of no sections.
Source: Stacks Project, Modules on Sites, Tag 093U (3), extension paragraph.
(auxiliary; not a blueprint node).

Proof: Forgetting to abelian sheaves preserves epimorphisms because it preserves
cokernels. An epimorphism of abelian sheaves is locally surjective, so the image sieve
of every chosen section is covering. Their finite intersection is covering, and on
each member every section has a lift. For an empty family the intersection is the
maximal sieve and the lifting assertion is vacuous. -/
theorem exists_cover_lift_finite_sections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {F G : SheafOfModules.{u} R} (p : F ⟶ G) [Epi p] (U : C)
    {ι : Type v} [Finite ι] (s : ι → G.val.obj (op U)) :
    ∃ S ∈ J U, ∀ (V : C) (f : V ⟶ U), S f →
      ∀ i, ∃ t : F.val.obj (op V), p.val.app (op V) t = G.val.map f.op (s i) := by
  let φ := (SheafOfModules.toSheaf.{u} R).map p
  have : Epi φ := inferInstance
  have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' _ φ).2 inferInstance
  have : Presheaf.IsLocallySurjective J φ.hom := inferInstance
  refine ⟨⨅ i, Presheaf.imageSieve φ.hom (s i),
    J.iInf_mem _ (fun i ↦ Presheaf.imageSieve_mem J φ.hom (s i)), ?_⟩
  intro V f hf i
  exact (iInf_le (fun i ↦ Presheaf.imageSieve φ.hom (s i)) i) _ hf

end SheafOfModules
