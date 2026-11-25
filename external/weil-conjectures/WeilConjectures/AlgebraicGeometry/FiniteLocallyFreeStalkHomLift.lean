/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank

/-! # Extending a linear map from a finite locally free stalk

Source: Stacks Project, Tag 05GF, Lemma 10.79.2, finite matrix argument.
(blueprint: lem-sc-finite-locally-free-stalk-hom-lift)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules


private noncomputable def sectionOver {W : Scheme.{u}} (N : W.Modules)
    (U : W.Opens) (s : Γ(N, U)) : (N.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ show Γ(N, V.unop.left) from N.presheaf.map V.unop.hom.op s)
    (fun V V' f ↦ by
      change N.presheaf.map f.unop.left.op (N.presheaf.map V.unop.hom.op s) = _
      rw [← N.presheaf.map_comp_apply]
      rfl)

private noncomputable def overToRestrictHom {W : Scheme.{u}} {M N : W.Modules}
    (U : W.Opens) (f : M.over U ⟶ N.over U) :
    (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N :=
  (overFunctorEquiv U).inv.app M ≫ (overEquiv U).functor.map f ≫
    (overFunctorEquiv U).hom.app N

private lemma overToRestrictHom_app {W : Scheme.{u}} {M N : W.Modules}
    (U : W.Opens) (f : M.over U ⟶ N.over U) (V : U.toScheme.Opens)
    (m : Γ((restrictFunctor U.ι).obj M, V)) :
    Hom.app (overToRestrictHom U f) V m =
      f.val.app (op (Over.mk (homOfLE (show U.ι ''ᵁ V ≤ U from by
        intro z hz
        obtain ⟨t, _ht, rfl⟩ := hz
        exact t.property)))) m := by
  rfl

private noncomputable def projectionWithin {W : Scheme.{u}} (M : W.Modules)
    (C U : W.Opens) (hUC : U ≤ C) {I : Type u} [DecidableEq I]
    (e : M.over C ≅ SheafOfModules.free I) (j : I) :
    M.over U ⟶ SheafOfModules.unit (W.ringCatSheaf.over U) :=
  (SheafOfModules.overFunctorMap W.ringCatSheaf (homOfLE hUC)).inv.app M ≫
    (SheafOfModules.overMap W.ringCatSheaf (homOfLE hUC)).map
      (localProjection M C e j) ≫
    (SheafOfModules.overMapUnitIso (R := W.ringCatSheaf) (homOfLE hUC)).hom

private noncomputable def homFromSections {W : Scheme.{u}} (M N : W.Modules)
    (C U : W.Opens) (hUC : U ≤ C) {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over C ≅ SheafOfModules.free I) (s : I → Γ(N, U)) :
    M.over U ⟶ N.over U :=
  ∑ j, projectionWithin M C U hUC e j ≫ (N.over U).unitHomEquiv.symm (sectionOver N U (s j))

private lemma homFromSections_app {W : Scheme.{u}} (M N : W.Modules)
    (C U : W.Opens) (hUC : U ≤ C) {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over C ≅ SheafOfModules.free I) (s : I → Γ(N, U))
    (D : W.Opens) (hDU : D ≤ U) (m : Γ(M, D)) :
    (homFromSections M N C U hUC e s).val.app (op (Over.mk (homOfLE hDU))) m =
      ∑ j, (show Γ(W, D) from (localProjection M C e j).val.app
          (op (Over.mk (homOfLE (hDU.trans hUC)))) m) •
        N.presheaf.map (homOfLE hDU).op (s j) := by
  rw [homFromSections, SheafOfModules.sum_val_app_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- Any linear map from a finite locally free stalk is represented near the point.
Source: Stacks Project, Tag 05GF, Lemma 10.79.2.
(blueprint: lem-sc-finite-locally-free-stalk-hom-lift)

Proof: Choose a finite free frame for M on an open neighbourhood of x. Apply t to
its finitely many basis germs. Each resulting germ of N is represented by a
section on some neighbourhood. Intersect these neighbourhoods with the frame
open, and restrict the chosen sections there. The free sheaf universal property
extends the assignment of basis vectors to these sections to a module morphism.
For any smaller open and any section of M, the frame writes that section as a
finite sum of coefficient sections times basis vectors. Taking germs commutes
with this sum and scalar multiplication. Linearity of t and the chosen germ
representatives give the displayed equality. If the frame has rank zero, use
the unique map out of the zero sheaf and keep the frame open. No finiteness
condition on N is required. -/
theorem exists_restrict_stalk_hom_lift
    {W : Scheme.{u}} (M N : W.Modules) [M.IsFiniteLocallyFree] (x : W)
    (t : (RingedSpace.moduleStalkFunctor W.toRingedSpace x).obj M ⟶
      (RingedSpace.moduleStalkFunctor W.toRingedSpace x).obj N) :
    ∃ (U : W.Opens) (hxU : x ∈ U)
      (f : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N),
      ∀ (V : U.toScheme.Opens) (hxV : (⟨x, hxU⟩ : U.toScheme) ∈ V)
        (m : Γ((restrictFunctor U.ι).obj M, V)),
        N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩ (Hom.app f V m) =
          t (M.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩ m) := by
  classical
  obtain ⟨C, I, hI, hxC, ⟨e⟩⟩ := exists_mem_over_iso_free M x
  let : Fintype I := hI
  have represent (j : I) := N.presheaf.exists_le_germ_eq
    (t (localBasisGerm M x C hxC e j)) hxC
  choose D hDC hxD b hb using represent
  let U : W.Opens := C ⊓ ⨅ j, D j
  have hUC : U ≤ C := inf_le_left
  have hUD (j : I) : U ≤ D j := inf_le_right.trans (iInf_le _ j)
  have hxU : x ∈ U := ⟨hxC, by
    change x ∈ (↑(⨅ j, D j) : Set W)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxD⟩
  let s (j : I) : Γ(N, U) := N.presheaf.map (homOfLE (hUD j)).op (b j)
  have hs (j : I) : N.presheaf.germ U x hxU (s j) =
      t (localBasisGerm M x C hxC e j) := by
    exact (N.presheaf.germ_res_apply (homOfLE (hUD j)) x hxU (b j)).trans (hb j)
  let f := homFromSections M N C U hUC e s
  refine ⟨U, hxU, overToRestrictHom U f, ?_⟩
  intro V hxV m
  let A := U.ι ''ᵁ V
  have hAU : A ≤ U := by
    intro z hz
    obtain ⟨y, _hy, rfl⟩ := hz
    exact y.property
  have hxA : x ∈ A := ⟨⟨x, hxU⟩, hxV, rfl⟩
  change N.presheaf.germ A x hxA (Hom.app (overToRestrictHom U f) V m) =
    t (M.presheaf.germ A x hxA m)
  rw [overToRestrictHom_app]
  change N.presheaf.germ A x hxA
    ((homFromSections M N C U hUC e s).val.app (op (Over.mk (homOfLE hAU))) m) = _
  rw [homFromSections_app, map_sum]
  have hm := sum_coordinate_basis M x C hxC e (M.presheaf.germ A x hxA m)
  rw [← hm, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  erw [Scheme.Modules.germ_smul]
  rw [coordinateLinear_germ_of_le M x C hxC _ A hxA (hAU.trans hUC)]
  let a : Γ(W, A) := (localProjection M C e j).val.app
    (op (Over.mk (homOfLE (hAU.trans hUC)))) m
  change W.presheaf.germ A x hxA a •
      N.presheaf.germ A x hxA (N.presheaf.map (homOfLE hAU).op (s j)) =
    t.hom (W.presheaf.germ A x hxA a • localBasisGerm M x C hxC e j)
  rw [t.hom.map_smul, N.presheaf.germ_res_apply, hs]


end AlgebraicGeometry.Scheme.Modules
