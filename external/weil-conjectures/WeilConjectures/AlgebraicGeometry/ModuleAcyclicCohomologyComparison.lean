/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicEffacementLadder
import Mathlib.Algebra.FiveLemma

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- Acyclic module resolutions give comparison for underlying abelian sheaves.

Source: Stacks Project, Tag 095T, second paragraph, and Tag 03FD.
(blueprint: lem-weil-pbc-module-acyclic-cohomology-comparison)

Proof: take an injective resolution of M in sheaves of modules over the constant
prime ring. Forgetting coefficients is exact. By 03FD, its underlying abelian
terms are acyclic on X. Inverse image is exact, commutes with forgetting
coefficients, and by hacyclic the inverse images of these terms are acyclic on Y.
Thus both underlying abelian cohomologies are computed by the section complexes
of this resolution and its inverse image, by Leray's acyclic-resolution lemma.
The maps of section complexes are isomorphisms term by term by hzero; forgetting
coefficients preserves them. Hence their homology maps are bijective in every
degree, including zero. To identify this with cohomologyMap, compare the underlying
resolution into an abelian injective resolution on X and its inverse image into
an abelian injective resolution on Y. The natural restriction maps give a commuting
square of section complexes. The resolution comparison maps induce precisely the
acyclic-resolution isomorphisms. Homotopy uniqueness of comparisons into injective
resolutions identifies the map in this square with the Ext pullback, precomposed
with the constant-integer-sheaf isomorphism, which defines cohomologyMap. This
establishes bijectivity for the canonical map, and includes the zero module sheaf. -/
theorem Etale.bijective_cohomologyMap_of_module_acyclic
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ) [Fact r.Prime]
    (hzero : ∀ G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))),
      IsIso (globalSectionsUpperStarMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) i G))
    (hacyclic : ∀ (J : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J]
        (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj J)) q))
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap i
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj M) q) := by
  induction q generalizing M with
  | zero =>
    exact Etale.bijective_cohomologyMap_of_module_acyclic_zero i r hzero M
  | succ q ih =>
    let U := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})
    let V := (i)^*[AddCommGrpCat.{u + 1}]
    obtain ⟨J, Q, g, δX, δY, hX, hY, hsX, hsY, hδ⟩ :=
      Etale.exists_module_acyclic_effacement_ladder i r hacyclic M q
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      (Sheaf.H.map (U.map g) q) δX (Sheaf.H.map (V.map (U.map g)) q) δY
      (cohomologyMap i (U.obj J) q) (cohomologyMap i (U.obj Q) q)
      (cohomologyMap i (U.obj M) (q + 1))
      (AddMonoidHom.ext fun x ↦ (cohomologyMap_map i q (U.map g) x).symm)
      hδ hX hY (ih J).2 (ih Q) hsX hsY

end AlgebraicGeometry
