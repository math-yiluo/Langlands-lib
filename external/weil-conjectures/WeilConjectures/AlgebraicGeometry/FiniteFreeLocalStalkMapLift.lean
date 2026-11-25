/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Lifting images of a finite free local source

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A stalk-linear map composed with a finite free local-source morphism lifts
on a smaller neighborhood. No relations or descent to the quotient are asserted.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`),
third paragraph, finite-coordinate lifting.
(blueprint: lem-weil-pbc-finite-free-local-stalk-map-lift)

Proof: Evaluate f on the finitely many basis sections at U, take their germs at
x, and apply χ. Choose actual section representatives of these germs in G.
Intersect their finitely many neighborhoods with U to obtain V. Restrict each
representative to a compatible section over V; unitHomEquiv and overMapUnitIso
turn it into a morphism from the restricted unit sheaf. Define ψ as the sum of
the restricted coordinate projections followed by these morphisms.
The proved freeSectionsLinearEquiv decomposes every section into its basis
coordinates. Naturality computes f on each basis coordinate, and unitHomEquiv
computes ψ. Additivity, germ_smul, linearity of χ, and germ_res_apply reduce the
required equality to the chosen representative equations. If I is empty,
V = U and both sides are empty sums. -/
theorem exists_finiteFree_local_stalkMap_lift
    (X : RingedSpace.{u}) (F G : Modules X) (x : X)
    (U : Opens X) (hxU : x ∈ U) (I : Type u) [Finite I]
    (f : SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I ⟶ F.over U)
    (χ : (moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
      (moduleStalkFunctor X x).obj G) :
    ∃ (V : Opens X) (hxV : x ∈ V) (i : V ⟶ U)
      (ψ : (SheafOfModules.overMap ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) i).obj
        (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I) ⟶ G.over V),
      ∀ (W : Opens X) (j : W ⟶ V) (hxW : x ∈ W)
        (s : (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I).val.obj
          (op (Over.mk (j ≫ i)))),
        TopCat.Presheaf.germ G.val.presheaf W x hxW
          (ψ.val.app (op (Over.mk j)) s) =
        χ (TopCat.Presheaf.germ F.val.presheaf W x hxW
          (f.val.app (op (Over.mk (j ≫ i))) s)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
  let A := SheafOfModules.free (R := R.over U) I
  let e (k : I) : F.val.obj (op U) :=
    (f.val.app (op (Over.mk (𝟙 U))))
      ((SheafOfModules.ιFree (R := R.over U) k).val.app
        (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)))
  choose D hDU hxD t ht using fun k : I ↦
    TopCat.Presheaf.exists_le_germ_eq G.val.presheaf
      (χ (TopCat.Presheaf.germ F.val.presheaf U x hxU (e k))) hxU
  let V : Opens X := U ⊓ ⨅ k, D k
  have hxV : x ∈ V := by
    refine ⟨hxU, ?_⟩
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxD
  let i : V ⟶ U := homOfLE inf_le_left
  let q (k : I) : V ⟶ D k := homOfLE (inf_le_right.trans (iInf_le D k))
  let T := SheafOfModules.overMap R i
  let σ (k : I) : (G.over V).sections :=
    PresheafOfModules.sectionsMk
      (fun Z ↦ G.val.map (Z.unop.hom ≫ q k).op (t k)) (by
        intro Z Z' a
        change G.val.map a.unop.left.op
          (G.val.map (Z.unop.hom ≫ q k).op (t k)) = _
        rw [← G.val.map_comp_apply]
        congr 2)
  let g (k : I) : T.obj (SheafOfModules.unit (R.over U)) ⟶ G.over V :=
    (SheafOfModules.overMapUnitIso (R := R) i).hom ≫
      (G.over V).unitHomEquiv.symm (σ k)
  let ψ : T.obj A ⟶ G.over V := ∑ k, T.map (SheafOfModules.freeπ k) ≫ g k
  refine ⟨V, hxV, i, ψ, ?_⟩
  intro W j hxW s
  let Z : (Over U)ᵒᵖ := op (Over.mk (j ≫ i))
  let c (k : I) : R.obj.obj (op W) := (SheafOfModules.freeπ k).val.app Z s
  have hs : s = ∑ k, (SheafOfModules.ιFree (R := R.over U) k).val.app Z (c k) := by
    exact ((SheafOfModules.freeSectionsLinearEquiv (R := R.over U) I Z).symm_apply_apply
      s).symm
  have hf (k : I) :
      f.val.app Z ((SheafOfModules.ιFree (R := R.over U) k).val.app Z (c k)) =
        c k • F.val.map (j ≫ i).op (e k) := by
    let h : SheafOfModules.unit (R.over U) ⟶ F.over U :=
      SheafOfModules.ιFree k ≫ f
    have hlin := (h.val.app Z).hom.map_smul (c k) (1 : R.obj.obj (op W))
    have hn := PresheafOfModules.sections_property ((F.over U).unitHomEquiv h)
      (Over.homMk (j ≫ i) : Over.mk (j ≫ i) ⟶ Over.mk (𝟙 U)).op
    have hn' : F.val.map (j ≫ i).op (e k) = h.val.app Z (1 : R.obj.obj (op W)) := hn
    simpa only [smul_eq_mul, mul_one, hn', h, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply] using hlin
  have hg (k : I) :
      (g k).val.app (op (Over.mk j)) (c k) =
        c k • G.val.map (j ≫ q k).op (t k) := by
    have hlin := ((G.over V).unitHomEquiv.symm (σ k)).val.app
      (op (Over.mk j)) |>.hom.map_smul (c k) (1 : R.obj.obj (op W))
    have hv := congrArg (fun z : (G.over V).sections ↦ z.val (op (Over.mk j)))
      ((G.over V).unitHomEquiv.apply_symm_apply (σ k))
    change ((G.over V).unitHomEquiv.symm (σ k)).val.app
      (op (Over.mk j)) (1 : R.obj.obj (op W)) =
        G.val.map (j ≫ q k).op (t k) at hv
    change ((G.over V).unitHomEquiv.symm (σ k)).val.app
      (op (Over.mk j)) (c k) = _
    simpa only [smul_eq_mul, mul_one, hv] using hlin
  have hp : ψ.val.app (op (Over.mk j)) s =
      ∑ k, c k • G.val.map (j ≫ q k).op (t k) := by
    rw [SheafOfModules.sum_val_app_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact hg k
  rw [hp, hs]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hf k]
  erw [PresheafOfModules.germ_smul (R := X.presheaf) G.val,
    PresheafOfModules.germ_smul (R := X.presheaf) F.val, map_smul]
  have hG := TopCat.Presheaf.germ_res_apply G.val.presheaf (j ≫ q k) x hxW (t k)
  have hF := TopCat.Presheaf.germ_res_apply F.val.presheaf (j ≫ i) x hxW (e k)
  erw [hG, hF, ht k]

end AlgebraicGeometry.RingedSpace
