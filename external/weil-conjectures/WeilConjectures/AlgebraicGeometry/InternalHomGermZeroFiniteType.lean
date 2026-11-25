/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Detecting the zero germ of a local morphism by finite generation

Source: Stacks Project, Modules, Lemma 01CP, second paragraph.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

private theorem finiteType_neighborhood (X : RingedSpace.{u})
    (F : Modules X) [SheafOfModules.IsFiniteType.{u} F] (x : X) :
    ∃ (A : Opens X), x ∈ A ∧
      ∃ (σ : (F.over A).GeneratingSections), σ.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hcover := q.coversTop ⊤
  rw [Opens.mem_grothendieckTopology] at hcover
  obtain ⟨W, i, hi, hxW⟩ := hcover x (by trivial)
  obtain ⟨a, ⟨j⟩⟩ := hi
  exact ⟨q.X a, (leOfHom j) hxW, q.generators a, hq.isFiniteType a⟩

private theorem map_generators_hom_eq_zero.{u₁, v₁, u₂, v₂}
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type u₂} [Category.{v₂} D] [Limits.HasZeroMorphisms D]
    (T : SheafOfModules.{u} R ⥤ D) [Limits.PreservesColimitsOfSize.{u, u} T]
    [T.PreservesEpimorphisms] {M : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) {N : D} (ψ : T.obj M ⟶ N)
    (h : ∀ a, T.map (M.unitHomEquiv.symm (σ.s a)) ≫ ψ = 0) : ψ = 0 := by
  apply (cancel_epi (T.map σ.π)).mp
  rw [Limits.comp_zero]
  refine (Limits.isColimitOfPreserves T
    (SheafOfModules.isColimitFreeCofan σ.I)).hom_ext (fun a ↦ ?_)
  change T.map (SheafOfModules.ιFree a.as) ≫ T.map σ.π ≫ ψ = _
  rw [← Category.assoc, ← T.map_comp,
    ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  have hs : M.freeHomEquiv σ.π a.as = σ.s a.as :=
    congrFun (M.freeHomEquiv.apply_symm_apply σ.s) a.as
  rw [hs, Limits.comp_zero]
  exact h a.as

set_option backward.isDefEq.respectTransparency false in
private theorem zero_on_generators (X : RingedSpace.{u}) (F G : Modules X)
    (A U V : Opens X) (j : V ⟶ A) (i : V ⟶ U)
    (σ : (F.over A).GeneratingSections)
    (φ : (F.homObj G).val.obj (op U))
    (h : ∀ a : σ.I, φ.app (op (Over.mk i))
      ((σ.s a).val (op (Over.mk j))) = 0) :
    (F.homObj G).val.presheaf.map i.op φ = 0 := by
  let R := ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
  let T := SheafOfModules.overMap R j
  let ψ : F.over V ⟶ G.over V := ⟨PresheafOfModules.restrictOverMap i φ⟩
  have hψ : ψ = 0 := by
    apply map_generators_hom_eq_zero T σ ψ
    intro a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext
    have hunit := congrArg (fun s ↦ s.val (op ((Over.map j).obj W.unop)))
      ((F.over A).unitHomEquiv.apply_symm_apply (σ.s a))
    change ((F.over A).unitHomEquiv.symm (σ.s a)).val.app
      (op ((Over.map j).obj W.unop)) (1 : R.obj.obj (op W.unop.left)) = _ at hunit
    change φ.app (op ((Over.map i).obj W.unop))
      (((F.over A).unitHomEquiv.symm (σ.s a)).val.app
        (op ((Over.map j).obj W.unop)) (1 : R.obj.obj (op W.unop.left))) = 0
    rw [hunit]
    change φ.app (op (Over.mk (W.unop.hom ≫ i)))
      ((σ.s a).val (op (Over.mk (W.unop.hom ≫ j)))) = 0
    have hn := PresheafOfModules.naturality_apply φ
      (Over.homMk W.unop.hom : Over.mk (W.unop.hom ≫ i) ⟶ Over.mk i).op
      ((σ.s a).val (op (Over.mk j)))
    have hs' := PresheafOfModules.sections_property (σ.s a)
      (Over.homMk W.unop.hom : Over.mk (W.unop.hom ≫ j) ⟶ Over.mk j).op
    change F.val.map W.unop.hom.op _ = _ at hs'
    change φ.app (op (Over.mk (W.unop.hom ≫ i)))
      (F.val.map W.unop.hom.op _) = G.val.map W.unop.hom.op _ at hn
    rw [hs', h a, map_zero] at hn
    exact hn
  exact congrArg SheafOfModules.Hom.val hψ

/-- A local morphism from a finite type sheaf whose induced stalk map is zero
has zero germ in internal Hom.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), second
paragraph (finite type case).
(blueprint: lem-weil-pbc-internal-hom-germ-zero-finite-type)

Proof: Restrict to a neighborhood of x where F has finitely many generating
sections. Intersect it with U. The images of these generators have zero germs
by the hypothesis. Shrink once for each generator and intersect the finitely
many resulting neighborhoods. All generator images are then zero sections.
The generators still generate the restriction of F, since restriction preserves
free sheaves and epimorphisms. Thus the restricted morphism is zero: compose
with the free generator epimorphism and use its right cancellation property.
Its germ, equal to the original germ, is consequently zero. If there are no
generators the source is zero on this neighborhood and the assertion is immediate. -/
theorem internalHom_germ_eq_zero_of_finiteType
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFiniteType.{u} F] (x : X)
    (U : Opens X) (hxU : x ∈ U) (φ : (F.homObj G).val.obj (op U))
    (hφ : ∀ (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
      TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) = 0) :
    TopCat.Presheaf.germ (F.homObj G).val.presheaf U x hxU φ = 0 := by
  classical
  obtain ⟨A, hxA, σ, hσ⟩ := finiteType_neighborhood X F x
  let : σ.IsFiniteType := hσ
  let B := A ⊓ U
  let j : B ⟶ A := homOfLE inf_le_left
  let i : B ⟶ U := homOfLE inf_le_right
  have hxB : x ∈ B := ⟨hxA, hxU⟩
  let t (a : σ.I) : G.val.obj (op B) :=
    φ.app (op (Over.mk i)) ((σ.s a).val (op (Over.mk j)))
  have ht (a : σ.I) : TopCat.Presheaf.germ G.val.presheaf B x hxB (t a) =
      TopCat.Presheaf.germ G.val.presheaf B x hxB 0 := by
    rw [map_zero]
    exact hφ B i hxB _
  have ht' (a : σ.I) : ∃ (W : Opens X), x ∈ W ∧
      ∃ (k : W ⟶ B), G.val.presheaf.map k.op (t a) = 0 := by
    obtain ⟨W, hxW, k, k', hk⟩ :=
      TopCat.Presheaf.germ_eq G.val.presheaf x hxB hxB (t a) 0 (ht a)
    exact ⟨W, hxW, k, hk.trans (map_zero _)⟩
  choose W hxW k hk using ht'
  let V := B ⊓ ⨅ a, W a
  have hxV : x ∈ V := by
    refine ⟨hxB, ?_⟩
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxW
  let l : V ⟶ B := homOfLE inf_le_left
  have hz (a : σ.I) : G.val.presheaf.map l.op (t a) = 0 := by
    let n : V ⟶ W a := homOfLE (inf_le_right.trans (iInf_le W a))
    have hl : l = n ≫ k a := Subsingleton.elim _ _
    rw [hl, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hk, map_zero]
  have hgen (a : σ.I) : φ.app (op (Over.mk (l ≫ i)))
      ((σ.s a).val (op (Over.mk (l ≫ j)))) = 0 := by
    have hn := PresheafOfModules.naturality_apply φ
      (Over.homMk l : Over.mk (l ≫ i) ⟶ Over.mk i).op
      ((σ.s a).val (op (Over.mk j)))
    have hs := PresheafOfModules.sections_property (σ.s a)
      (Over.homMk l : Over.mk (l ≫ j) ⟶ Over.mk j).op
    change F.val.map l.op _ = _ at hs
    change φ.app (op (Over.mk (l ≫ i))) (F.val.map l.op _) =
      G.val.presheaf.map l.op (t a) at hn
    rw [hs] at hn
    exact hn.trans (hz a)
  have hres := zero_on_generators X F G A U V (l ≫ j) (l ≫ i) σ φ hgen
  rw [← TopCat.Presheaf.germ_res_apply (F.homObj G).val.presheaf (l ≫ i) x hxV φ,
    hres, map_zero]

end AlgebraicGeometry.RingedSpace
