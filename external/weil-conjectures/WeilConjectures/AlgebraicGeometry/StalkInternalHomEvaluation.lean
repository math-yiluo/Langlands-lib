/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Evaluation of internal Hom on stalks

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), first paragraph
(blueprint: lem-weil-pbc-stalk-internal-hom-evaluation).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u}) (F G : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology X)
  (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) (x : X)

private theorem eval_restrict (U V W : Opens X) (i : V ⟶ U) (j : W ⟶ V)
    (φ : (F.homObj G).val.obj (op U)) (s : F.val.obj (op V)) :
    G.val.presheaf.map j.op (φ.app (op (Over.mk i)) s) =
      φ.app (op (Over.mk (j ≫ i))) (F.val.presheaf.map j.op s) := by
  exact (PresheafOfModules.naturality_apply φ
    (Over.homMk j : Over.mk (j ≫ i) ⟶ Over.mk i).op s).symm

private theorem eval_germ_restrict (U V W : Opens X) (i : V ⟶ U) (j : W ⟶ V)
    (hxW : x ∈ W) (φ : (F.homObj G).val.obj (op U)) (s : F.val.obj (op V)) :
    TopCat.Presheaf.germ G.val.presheaf V x (j.le hxW)
        (φ.app (op (Over.mk i)) s) =
      TopCat.Presheaf.germ G.val.presheaf W x hxW
        (φ.app (op (Over.mk (j ≫ i))) (F.val.presheaf.map j.op s)) := by
  rw [← TopCat.Presheaf.germ_res_apply G.val.presheaf j x hxW, eval_restrict]

private theorem eval_restrict_hom (U V W : Opens X) (i : V ⟶ U) (j : W ⟶ V)
    (φ : (F.homObj G).val.obj (op U)) (s : F.val.obj (op W)) :
    (((F.homObj G).val.presheaf.map i.op φ).app (op (Over.mk j))) s =
      φ.app (op (Over.mk (j ≫ i))) s := by
  rfl

private theorem eval_germ_eq
    (U U' V V' : Opens X) (hxU : x ∈ U) (hxU' : x ∈ U')
    (hxV : x ∈ V) (hxV' : x ∈ V') (i : V ⟶ U) (i' : V' ⟶ U')
    (φ : (F.homObj G).val.obj (op U)) (φ' : (F.homObj G).val.obj (op U'))
    (s : F.val.obj (op V)) (s' : F.val.obj (op V'))
    (hφ : TopCat.Presheaf.germ (F.homObj G).val.presheaf U x hxU φ =
      TopCat.Presheaf.germ (F.homObj G).val.presheaf U' x hxU' φ')
    (hs : TopCat.Presheaf.germ F.val.presheaf V x hxV s =
      TopCat.Presheaf.germ F.val.presheaf V' x hxV' s') :
    TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) =
      TopCat.Presheaf.germ G.val.presheaf V' x hxV' (φ'.app (op (Over.mk i')) s') := by
  obtain ⟨A, hxA, a, a', ha⟩ :=
    TopCat.Presheaf.germ_eq (F.homObj G).val.presheaf x hxU hxU' φ φ' hφ
  obtain ⟨B, hxB, b, b', hb⟩ :=
    TopCat.Presheaf.germ_eq F.val.presheaf x hxV hxV' s s' hs
  let Z := A ⊓ B
  have hxZ : x ∈ Z := ⟨hxA, hxB⟩
  let zA : Z ⟶ A := homOfLE inf_le_left
  let zB : Z ⟶ B := homOfLE inf_le_right
  have hφZ : (F.homObj G).val.presheaf.map (zA ≫ a).op φ =
      (F.homObj G).val.presheaf.map (zA ≫ a').op φ' := by
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg ((F.homObj G).val.presheaf.map zA.op) ha
  have hsZ : F.val.presheaf.map (zB ≫ b).op s =
      F.val.presheaf.map (zB ≫ b').op s' := by
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg (F.val.presheaf.map zB.op) hb
  rw [eval_germ_restrict X F G x U V Z i (zB ≫ b) hxZ,
    eval_germ_restrict X F G x U' V' Z i' (zB ≫ b') hxZ]
  apply congrArg (TopCat.Presheaf.germ G.val.presheaf Z x hxZ)
  have hp : (zB ≫ b) ≫ i = (𝟙 Z) ≫ (zA ≫ a) := Subsingleton.elim _ _
  have hp' : (zB ≫ b') ≫ i' = (𝟙 Z) ≫ (zA ≫ a') := Subsingleton.elim _ _
  rw [hp, hp', ← eval_restrict_hom, ← eval_restrict_hom, hφZ, hsZ]

private theorem exists_eval_value
    (h : (moduleStalkFunctor X x).obj (F.homObj G))
    (v : (moduleStalkFunctor X x).obj F) :
    ∃ t : (moduleStalkFunctor X x).obj G,
      ∀ (U : Opens X) (hxU : x ∈ U) (φ : (F.homObj G).val.obj (op U))
        (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
        TopCat.Presheaf.germ (F.homObj G).val.presheaf U x hxU φ = h →
        TopCat.Presheaf.germ F.val.presheaf V x hxV s = v →
        t = TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) := by
  obtain ⟨U₀, hxU₀, φ₀, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (F.homObj G).val.presheaf h
  obtain ⟨V₀, hxV₀, s₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf v
  let W := U₀ ⊓ V₀
  have hxW : x ∈ W := ⟨hxU₀, hxV₀⟩
  let i₀ : W ⟶ U₀ := homOfLE inf_le_left
  let j₀ : W ⟶ V₀ := homOfLE inf_le_right
  let sW := F.val.presheaf.map j₀.op s₀
  refine ⟨TopCat.Presheaf.germ G.val.presheaf W x hxW
    (φ₀.app (op (Over.mk i₀)) sW), ?_⟩
  intro U hxU φ V i hxV s hφ hs
  apply eval_germ_eq X F G x U₀ U W V hxU₀ hxU hxW hxV i₀ i φ₀ φ sW s
  · exact hφ.symm
  · exact (TopCat.Presheaf.germ_res_apply F.val.presheaf j₀ x hxW s₀).trans hs.symm

private theorem common_germs (A B C : X.carrier.Presheaf Ab.{u})
    (a : A.stalk x) (b : B.stalk x) (c : C.stalk x) :
    ∃ (U : Opens X) (hxU : x ∈ U) (s : A.obj (op U))
      (t : B.obj (op U)) (w : C.obj (op U)),
      A.germ U x hxU s = a ∧ B.germ U x hxU t = b ∧ C.germ U x hxU w = c := by
  obtain ⟨U, hxU, s, rfl⟩ := A.exists_germ_eq a
  obtain ⟨V, hVU, hxV, t, rfl⟩ := B.exists_le_germ_eq b hxU
  obtain ⟨W, hWV, hxW, w, rfl⟩ := C.exists_le_germ_eq c hxV
  refine ⟨W, hxW, A.map (homOfLE (hWV.trans hVU)).op s,
    B.map (homOfLE hWV).op t, w, ?_, ?_, rfl⟩
  · exact A.germ_res_apply _ x hxW s
  · exact B.germ_res_apply _ x hxW t

private theorem common_scalar_germs (A B : X.carrier.Presheaf Ab.{u})
    (r : X.presheaf.stalk x) (a : A.stalk x) (b : B.stalk x) :
    ∃ (U : Opens X) (hxU : x ∈ U) (q : X.presheaf.obj (op U))
      (s : A.obj (op U)) (t : B.obj (op U)),
      X.presheaf.germ U x hxU q = r ∧ A.germ U x hxU s = a ∧ B.germ U x hxU t = b := by
  obtain ⟨U, hxU, q, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, s, rfl⟩ := A.exists_le_germ_eq a hxU
  obtain ⟨W, hWV, hxW, t, rfl⟩ := B.exists_le_germ_eq b hxV
  refine ⟨W, hxW, X.presheaf.map (homOfLE (hWV.trans hVU)).op q,
    A.map (homOfLE hWV).op s, t, ?_, ?_, rfl⟩
  · exact X.presheaf.germ_res_apply _ x hxW q
  · exact A.germ_res_apply _ x hxW s

set_option backward.isDefEq.respectTransparency false in
/-- The canonical stalk evaluation is linear in the germ of the local morphism and
in the germ of its argument, with no finiteness assumption on the source.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), first paragraph.
(blueprint: lem-weil-pbc-stalk-internal-hom-evaluation)

Proof: Represent the two input germs on a common neighborhood and evaluate the local
morphism there. If either representative changes, equality of germs lets us shrink
until both representatives agree; naturality of the local morphism then makes the
output germ unchanged. Addition and scalar multiplication can likewise be checked
on a common neighborhood, where they are the linearity identities for evaluation.
Thus the resulting evaluation function gives the displayed linear map. -/
theorem exists_stalk_internalHom_linearMap :
    ∃ c : (moduleStalkFunctor X x).obj (F.homObj G) →ₗ[X.presheaf.stalk x]
        ((moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
          (moduleStalkFunctor X x).obj G),
      ∀ (U : Opens X) (hxU : x ∈ U) (φ : (F.homObj G).val.obj (op U))
        (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
        c (TopCat.Presheaf.germ (F.homObj G).val.presheaf U x hxU φ)
            (TopCat.Presheaf.germ F.val.presheaf V x hxV s) =
          TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) := by
  classical
  choose c hc using exists_eval_value X F G x
  have hc' (U : Opens X) (hxU : x ∈ U) (φ : (F.homObj G).val.obj (op U))
      (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)) :
      c (TopCat.Presheaf.germ (F.homObj G).val.presheaf U x hxU φ)
          (TopCat.Presheaf.germ F.val.presheaf V x hxV s) =
        TopCat.Presheaf.germ G.val.presheaf V x hxV (φ.app (op (Over.mk i)) s) :=
    hc _ _ U hxU φ V i hxV s rfl rfl
  have add_right (h : (moduleStalkFunctor X x).obj (F.homObj G))
      (v w : (moduleStalkFunctor X x).obj F) : c h (v + w) = c h v + c h w := by
    obtain ⟨U, hxU, φ, s, t, rfl, rfl, rfl⟩ :=
      common_germs X x (F.homObj G).val.presheaf F.val.presheaf F.val.presheaf h v w
    rw [← map_add (TopCat.Presheaf.germ F.val.presheaf U x hxU).hom,
      hc' U hxU φ U (𝟙 U) hxU, hc' U hxU φ U (𝟙 U) hxU,
      hc' U hxU φ U (𝟙 U) hxU, map_add, map_add]
  have smul_right (h : (moduleStalkFunctor X x).obj (F.homObj G))
      (r : X.presheaf.stalk x) (v : (moduleStalkFunctor X x).obj F) :
      c h (r • v) = r • c h v := by
    obtain ⟨U, hxU, q, φ, s, rfl, rfl, rfl⟩ :=
      common_scalar_germs X x (F.homObj G).val.presheaf F.val.presheaf r h v
    rw [← PresheafOfModules.germ_smul (R := X.presheaf) F.val,
      hc' U hxU φ U (𝟙 U) hxU, hc' U hxU φ U (𝟙 U) hxU, map_smul,
      PresheafOfModules.germ_smul (R := X.presheaf) G.val]
  have add_left (h k : (moduleStalkFunctor X x).obj (F.homObj G))
      (v : (moduleStalkFunctor X x).obj F) : c (h + k) v = c h v + c k v := by
    obtain ⟨U, hxU, φ, ψ, s, rfl, rfl, rfl⟩ :=
      common_germs X x (F.homObj G).val.presheaf (F.homObj G).val.presheaf
        F.val.presheaf h k v
    change (F.homObj G).val.obj (op U) at φ ψ
    rw [← map_add (TopCat.Presheaf.germ (F.homObj G).val.presheaf U x hxU).hom,
      hc' U hxU (φ + ψ) U (𝟙 U) hxU,
      hc' U hxU φ U (𝟙 U) hxU, hc' U hxU ψ U (𝟙 U) hxU]
    change TopCat.Presheaf.germ G.val.presheaf U x hxU
      (((φ.app (op (Over.mk (𝟙 U)))).hom +
        (ψ.app (op (Over.mk (𝟙 U)))).hom) s) = _
    rw [LinearMap.add_apply, map_add]
  have smul_left (r : X.presheaf.stalk x)
      (h : (moduleStalkFunctor X x).obj (F.homObj G))
      (v : (moduleStalkFunctor X x).obj F) : c (r • h) v = r • c h v := by
    obtain ⟨U, hxU, q, φ, s, rfl, rfl, rfl⟩ :=
      common_scalar_germs X x (F.homObj G).val.presheaf F.val.presheaf r h v
    change (F.homObj G).val.obj (op U) at φ
    rw [← PresheafOfModules.germ_smul (R := X.presheaf) (F.homObj G).val,
      hc' U hxU (q • φ) U (𝟙 U) hxU, hc' U hxU φ U (𝟙 U) hxU]
    have he : (q • φ).app (op (Over.mk (𝟙 U))) s =
        q • φ.app (op (Over.mk (𝟙 U))) s := by
      exact LinearMap.congr_fun
        ((PresheafOfModules.homObjEvalId F.val G.val U).map_smul q φ) s
    rw [he, PresheafOfModules.germ_smul (R := X.presheaf) G.val]
  let C : (moduleStalkFunctor X x).obj (F.homObj G) →ₗ[X.presheaf.stalk x]
      ((moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
        (moduleStalkFunctor X x).obj G) :=
    { toFun := fun h ↦
        { toFun := c h
          map_add' := add_right h
          map_smul' := smul_right h }
      map_add' := fun h k ↦ LinearMap.ext (add_left h k)
      map_smul' := fun r h ↦ LinearMap.ext (smul_left r h) }
  exact ⟨C, hc'⟩

end AlgebraicGeometry.RingedSpace
