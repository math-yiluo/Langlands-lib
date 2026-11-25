/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Local representatives through an epimorphism of module sheaves

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- A section germ lifts through an epimorphism of module sheaves on a local site.
This has no finite-generation or finite-presentation hypothesis.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`),
third paragraph, right exactness on stalks of the presentation.
(blueprint: lem-weil-pbc-local-module-epi-germ-lift)

Proof: The cokernel of f is zero because f is an epimorphism. Its underlying
abelian sheaf cokernel is the sheafification of the sectionwise cokernel.
Consequently f is locally surjective: for a section s over V, the open subsets
where its restrictions lift form a covering sieve. Choose a member containing
x, with underlying open W contained in V, and choose a section t mapping to
the restriction of s. Naturality of germs then gives the displayed equality.
Equivalently, apply exactness of stalks and cofinality of neighborhoods contained
in U to obtain a preimage germ and represent it below V. There is no assertion
of sectionwise surjectivity on V itself. -/
theorem exists_local_module_epi_germ_lift
    (X : RingedSpace.{u}) (F : Modules X) (x : X) (U : Opens X)
    (A : SheafOfModules.{u} (((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U))
    (f : A ⟶ F.over U) [Epi f]
    (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)) :
    ∃ (W : Opens X) (hxW : x ∈ W) (j : W ⟶ V)
      (t : A.val.obj (op (Over.mk (j ≫ i)))),
      TopCat.Presheaf.germ F.val.presheaf W x hxW
        (f.val.app (op (Over.mk (j ≫ i))) t) =
      TopCat.Presheaf.germ F.val.presheaf V x hxV s := by
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
  let T := SheafOfModules.toSheaf.{u} (R.over U)
  have : Epi (T.map f) := inferInstance
  have hsurj := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} (T.map f)).mpr
    inferInstance
  have hcov := hsurj.imageSieve_mem (U := Over.mk i) s
  rw [GrothendieckTopology.mem_over_iff] at hcov
  obtain ⟨W, j, hj, hxW⟩ := hcov x hxV
  have himg := (Sieve.overEquiv_iff _ j).mp hj
  obtain ⟨t, ht⟩ := himg
  refine ⟨W, hxW, j, t, ?_⟩
  change f.val.app (op (Over.mk (j ≫ i))) t = F.val.presheaf.map j.op s at ht
  rw [ht]
  exact TopCat.Presheaf.germ_res_apply F.val.presheaf j x hxW s

end AlgebraicGeometry.RingedSpace
