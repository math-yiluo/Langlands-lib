/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.CechZeroCocycleCompatibility

/-!
# The canonical augmented Čech row of an injective sheaf

Source: Stacks Project, Cohomology on Sites, Tags 03AW and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Canonical degree-zero descent for the categorical Čech complex of any sheaf.
Source: Stacks Project, Cohomology on Sites, Tag 03AN.
(blueprint: lem-sc-sheaf-cech-augmentation-degree-zero)

Proof: The single complex has zero differentials, hence its degree-zero homology
is I(X). The Čech complex has no incoming differential in degree zero, hence its
homology there is the kernel of d^0. The projection of d^0 to a pair (i,j) is
restriction from j minus restriction from i. A zero cocycle therefore gives
compatible sections on U_i: identify the single-factor product with U_i by its
unique projection, and pull the pair equation along any pair of arrows with equal
composites to X. The sheaf condition gives a unique section on X restricting to
these sections. Conversely, restriction of a section has zero differential by
functoriality. These constructions are additive and mutually inverse. Product
projection uniqueness and he identify the given e.f 0 with this restriction map,
so its homology map is this isomorphism. For an empty covering family the sheaf
condition says I(X) is zero; the same uniqueness argument works without choosing
an index. Neither injectivity nor sheafification is needed. -/
theorem sheaf_cech_augmentation_quasiIsoAt_zero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C]
    (I : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X)
    (e : (CochainComplex.single₀ AddCommGrpCat.{v}).obj (I.obj.obj (op X)) ⟶
      (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj ((Over.forget X).op ⋙ I.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t =
          I.obj.map (∏ᶜ (fun k ↦ Over.mk (π (t k)))).hom.op) : QuasiIsoAt e 0 := by
  have hm : Mono (e.f 0) := by
    constructor
    intro E x y hxy
    apply I.property.hom_ext_ofArrows π hπ
    intro i
    let q : Over.mk (π i) ⟶ ∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i)) :=
      Pi.lift (fun _ ↦ 𝟙 _)
    have hi := he (fun _ ↦ i)
    have hq : q.left ≫ (∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i))).hom = π i := q.w
    have hr : I.obj.map (∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i))).hom.op ≫
        I.obj.map q.left.op = I.obj.map (π i).op := by
      rw [← I.obj.map_comp, ← op_comp, hq]
    rw [← hr, ← hi, ← Category.assoc, ← Category.assoc, hxy]
    simp only [Category.assoc]
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_isIso_liftCycles _ (by simp) (by simp) (by simp)]
  let L := (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
    ((Over.forget X).op ⋙ I.obj)
  let S := L.sc' 0 0 1
  have hw : e.f 0 ≫ L.d 0 1 = 0 := by
    rw [e.comm]
    simp
  let f := S.liftCycles (e.f 0) hw
  change IsIso f
  have hf : Mono f := mono_of_mono_fac (S.liftCycles_i (e.f 0) hw)
  let z := S.iCycles
  let x := fun i ↦ z ≫ Pi.π (fun s : Fin 1 → ι ↦
    I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) (fun _ ↦ i) ≫
      I.obj.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (Over.mk (π i)))).left.op
  have hx : ∀ ⦃W : C⦄ ⦃i j : ι⦄ (a : W ⟶ U i) (b : W ⟶ U j),
      a ≫ π i = b ≫ π j → x i ≫ I.obj.map a.op = x j ≫ I.obj.map b.op := by
    intro W i j a b hab
    exact cech_zero_cocycle_compatibility I.obj X π z S.iCycles_g a b hab
  let g := I.property.amalgamateOfArrows π hπ x hx
  have hg : g ≫ e.f 0 = z := by
    apply Pi.hom_ext
    intro t
    change Fin 1 → ι at t
    change (g ≫ e.f 0) ≫ Pi.π (fun s : Fin 1 → ι ↦
      I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t =
        z ≫ Pi.π (fun s : Fin 1 → ι ↦
          I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t
    have ht : t = fun _ ↦ t 0 := by
      funext k
      congr 1
      exact Subsingleton.elim _ _
    rw [ht]
    generalize t 0 = i
    let q : Over.mk (π i) ⟶ ∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i)) :=
      Pi.lift (fun _ ↦ 𝟙 _)
    let r : (∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i))) ⟶ Over.mk (π i) :=
      Pi.π _ 0
    have hrq : r ≫ q = 𝟙 _ := by
      apply Pi.hom_ext
      intro k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp [q, r]
    have hw' : (∏ᶜ (fun _ : Fin 1 ↦ Over.mk (π i))).hom = r.left ≫ π i :=
      r.w.symm
    rw [Category.assoc, he, hw', op_comp, I.obj.map_comp, ← Category.assoc]
    rw [I.property.amalgamateOfArrows_map π hπ x hx]
    dsimp [x]
    rw [Category.assoc, Category.assoc, ← I.obj.map_comp, ← op_comp]
    have hleft : r.left ≫ q.left = 𝟙 _ := congrArg Over.Hom.left hrq
    rw [hleft, op_id, I.obj.map_id, Category.comp_id]
  have hgf : g ≫ f = 𝟙 _ := by
    apply (cancel_mono S.iCycles).1
    simp only [Category.assoc, S.liftCycles_i, Category.id_comp, hg, f, z]
  have hfg : f ≫ g = 𝟙 _ := by
    apply (cancel_mono f).1
    rw [Category.assoc, hgf, Category.comp_id, Category.id_comp]
  exact ⟨⟨g, hfg, hgf⟩⟩

end CategoryTheory
