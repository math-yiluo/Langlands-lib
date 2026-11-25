/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.StalkInternalHomEvaluation
import WeilConjectures.AlgebraicGeometry.FinitePresentationStalkKernel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Stalk of internal Hom with finitely presented source

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`),
finitely presented case (blueprint: lem-weil-pbc-stalk-internal-hom-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the stalk of internal Hom to the linear maps of stalks is
an isomorphism when the source module is finitely presented. The formula on germs
specifies the canonical map, including evaluation on every smaller neighbourhood.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`).
(blueprint: lem-weil-pbc-stalk-internal-hom-finite-presentation)

The stalks are the module stalks `RingedSpace.moduleStalkFunctor` (def-pc-module-stalk-functor),
whose carriers are the abelian-group stalks in which the germs below live.

Proof:
1. A local morphism induces a stalk map by applying it to representative sections.
   Equality of germs makes this well defined; it is additive and stalk-ring linear
   (`def-weil-pbc-module-stalk`, `def-pur-sheaf-hom`, `def-pur-localized-ringed-site`).
2. Localize at the point to a finite free presentation of F, using
   `def-weil-pbc-module-finite-type-presentation`. Its cokernel presentation is exact
   by `lem-weil-pbc-module-stalk-exact`; restriction preserves the stalks and the map.
3. Apply `lem-weil-pbc-sheaf-hom-finite-presentation-kernel` to obtain the exact sequence
   0 -> Hom(F,G) -> G^n -> G^m of sheaves, with the maps given by evaluation and the
   presentation matrix.
4. Take stalks using `lem-weil-pbc-module-stalk-exact`. Stalks commute with finite sums:
   finitely many representatives, or equalities of germs, share a neighbourhood.
   Thus the internal-Hom stalk is the kernel of G_x^n -> G_x^m.
5. The stalk presentation and `lem-weil-pbc-module-hom-left-exact` identify
   Hom(F_x,G_x) with the same kernel, by evaluation on the finite free basis.
6. The canonical map commutes with these two evaluations by its formula on germs.
   Both evaluations are injective with the same image, so it is bijective. Its
   linearity from step 1 yields the displayed linear equivalence. -/
theorem exists_stalk_internalHom_linearEquiv_of_finitePresentation
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X) :
    ∃ e : (moduleStalkFunctor X x).obj (F.homObj G) ≃ₗ[
        X.presheaf.stalk x]
      ((moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
        (moduleStalkFunctor X x).obj G),
      ∀ (U : Opens X) (hxU : x ∈ U)
        (φ : (SheafOfModules.homObj F G).val.obj (op U))
        (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
        e (TopCat.Presheaf.germ (SheafOfModules.homObj F G).val.presheaf U x hxU φ)
            (TopCat.Presheaf.germ F.val.presheaf V x hxV s) =
          TopCat.Presheaf.germ G.val.presheaf V x hxV
            ((φ.app (op (Over.mk i))) s) := by
  classical
  obtain ⟨c, hc⟩ := exists_stalk_internalHom_linearMap X F G x
  obtain ⟨U, hxU, m, n, s, a, b, β, hb, hab, hs, hβ, hβrange, hβgerm⟩ :=
    exists_finitePresentation_stalk_kernel X F G x
  let R := X.presheaf.stalk x
  let N := (moduleStalkFunctor X x).obj G
  let θn := LinearEquiv.piRing R N (Fin n) R
  let θm := LinearEquiv.piRing R N (Fin m) R
  let ε := θn.toLinearMap.comp (LinearMap.lcomp R N b)
  let α := θm.toLinearMap.comp ((LinearMap.lcomp R N a).comp θn.symm.toLinearMap)
  have hε : Function.Injective ε :=
    θn.injective.comp (LinearMap.lcomp_injective_of_surjective b hb)
  have compare (h : (moduleStalkFunctor X x).obj (F.homObj G)) : ε (c h) = β h := by
    obtain ⟨W, hxW, φ, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (F.homObj G).val.presheaf h
    ext i
    change c (TopCat.Presheaf.germ (F.homObj G).val.presheaf W x hxW φ)
      (b (Pi.single i 1)) = _
    rw [hs]
    have hx : x ∈ U ⊓ W := ⟨hxU, hxW⟩
    rw [← TopCat.Presheaf.germ_res_apply F.val.presheaf
      (homOfLE inf_le_left : U ⊓ W ⟶ U) x hx (s i)]
    exact (hc W hxW φ (U ⊓ W) (homOfLE inf_le_right) hx
      (F.val.presheaf.map (homOfLE inf_le_left : U ⊓ W ⟶ U).op (s i))).trans
        (hβgerm W hxW φ i).symm
  have hinj : Function.Injective c := by
    intro h k hhk
    apply hβ
    rw [← compare h, ← compare k, hhk]
  have hsurj : Function.Surjective c := by
    intro χ
    have hzero : α (ε χ) = 0 := by
      change θm ((LinearMap.lcomp R N a) (θn.symm (θn (χ.comp b)))) = 0
      rw [θn.symm_apply_apply]
      change θm ((χ.comp b).comp a) = 0
      rw [LinearMap.comp_assoc, hab.linearMap_comp_eq_zero, LinearMap.comp_zero, map_zero]
    have hmem : ε χ ∈ LinearMap.range β := by
      rw [hβrange]
      exact hzero
    obtain ⟨h, hh⟩ := hmem
    refine ⟨h, hε ?_⟩
    exact (compare h).trans hh
  exact ⟨LinearEquiv.ofBijective c ⟨hinj, hsurj⟩, hc⟩

end AlgebraicGeometry.RingedSpace
