/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Shrinking a finite free local map with zero germ action

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

set_option linter.unusedVariables false in
/-- A morphism from a restricted finite free sheaf which is zero on all germs
becomes the zero morphism on a smaller neighborhood.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`),
second paragraph applied to the finite free relation sheaf in the third paragraph.
(blueprint: lem-weil-pbc-finite-free-local-hom-zero)

Proof: Evaluate ψ on each restricted basis section at V. The hypothesis says
that each of these finitely many image sections has zero germ. The germ equality
criterion supplies, for each basis index, a smaller neighborhood where that
image section vanishes. Intersect these neighborhoods with V. Naturality gives
zero image on the restrictions of every basis section. Restriction preserves
free coproducts and their basis inclusions, so the coproduct universal property,
or freeHomEquiv, implies that the restricted morphism is zero. An empty basis
requires no intersection; the source is already the zero object. -/
theorem exists_finiteFree_local_hom_zero
    (X : RingedSpace.{u}) (G : Modules X) (x : X)
    (U V : Opens X) (hxV : x ∈ V) (i : V ⟶ U) (I : Type u) [Finite I]
    (ψ : (SheafOfModules.overMap ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) i).obj
      (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I) ⟶ G.over V)
    (hψ : ∀ (W : Opens X) (j : W ⟶ V) (hxW : x ∈ W)
      (s : (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I).val.obj
        (op (Over.mk (j ≫ i)))),
      TopCat.Presheaf.germ G.val.presheaf W x hxW
        (ψ.val.app (op (Over.mk j)) s) = 0) :
    ∃ (W : Opens X) (hxW : x ∈ W) (j : W ⟶ V),
      (SheafOfModules.overMap ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) j).map ψ = 0 := by
  classical
  let R := ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
  let F := SheafOfModules.overMap R i
  let b (k : I) : SheafOfModules.unit (R.over V) ⟶ G.over V :=
    F.map (SheafOfModules.ιFree k) ≫ ψ
  let t (k : I) : G.val.obj (op V) :=
    (b k).val.app (op (Over.mk (𝟙 V))) (1 : X.presheaf.obj (op V))
  have ht (k : I) : TopCat.Presheaf.germ G.val.presheaf V x hxV (t k) = 0 := by
    exact hψ V (𝟙 V) hxV _
  have ht' (k : I) : ∃ (W : Opens X) (hxW : x ∈ W) (j : W ⟶ V),
      G.val.presheaf.map j.op (t k) = 0 := by
    obtain ⟨W, hxW, j, j', hj⟩ := TopCat.Presheaf.germ_eq G.val.presheaf
      x hxV hxV (t k) 0 (by simpa using ht k)
    refine ⟨W, hxW, j, ?_⟩
    change G.val.map j.op (t k) = 0
    change G.val.map j.op (t k) = G.val.map j'.op 0 at hj
    simpa only [map_zero] using hj
  choose W hxW j hj using ht'
  let W₀ : Opens X := V ⊓ ⨅ k, W k
  have hxW₀ : x ∈ W₀ :=
    ⟨hxV, by simpa only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter] using hxW⟩
  let j₀ : W₀ ⟶ V := homOfLE inf_le_left
  refine ⟨W₀, hxW₀, j₀, ?_⟩
  let H := SheafOfModules.overMap R j₀
  apply (Limits.isColimitOfPreserves (F ⋙ H)
    (SheafOfModules.isColimitFreeCofan (R := R.over U) I)).hom_ext
  intro k
  dsimp
  rw [← H.map_comp]
  have hb : H.map (b k.as) = 0 := by
    apply SheafOfModules.hom_ext
    ext Z
    change (b k.as).val.app (op (Over.mk (Z.unop.hom ≫ j₀)))
      (1 : X.presheaf.obj (op Z.unop.left)) = 0
    let a : Over.mk (Z.unop.hom ≫ j₀) ⟶ Over.mk (𝟙 V) :=
      Over.homMk (Z.unop.hom ≫ j₀)
    have hn := PresheafOfModules.naturality_apply (b k.as).val a.op
      (1 : X.presheaf.obj (op V))
    have hone : (SheafOfModules.unit (R.over V)).val.map a.op
        (1 : X.presheaf.obj (op V)) =
        (1 : X.presheaf.obj (op Z.unop.left)) := by
      change X.presheaf.map (Z.unop.hom ≫ j₀).op 1 = 1
      exact map_one _
    rw [hone] at hn
    change (b k.as).val.app (op (Over.mk (Z.unop.hom ≫ j₀)))
      (1 : X.presheaf.obj (op Z.unop.left)) =
      G.val.map (Z.unop.hom ≫ j₀).op (t k.as) at hn
    rw [hn]
    let l : Z.unop.left ⟶ W k.as := homOfLE
      (Z.unop.hom.le.trans (inf_le_right.trans (iInf_le W k.as)))
    have he : Z.unop.hom ≫ j₀ = l ≫ j k.as := Subsingleton.elim _ _
    change G.val.presheaf.map (Z.unop.hom ≫ j₀).op (t k.as) = 0
    rw [he, op_comp, G.val.presheaf.map_comp]
    change G.val.map l.op (G.val.map (j k.as).op (t k.as)) = 0
    rw [show G.val.map (j k.as).op (t k.as) = 0 from hj k.as, map_zero]
  change H.map (b k.as) = _
  rw [hb]
  exact Limits.comp_zero.symm

end AlgebraicGeometry.RingedSpace
