/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Internal Hom turns coproducts into products

Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {A M N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pairing (f : A ⟶ homObj M N) (U : Cᵒᵖ)
    (a : A.obj U) (m : M.obj U) : N.obj U :=
  (f.app U a).app (op (Over.mk (𝟙 U.unop))) m

set_option backward.isDefEq.respectTransparency false in
private lemma pairing_natural (f : A ⟶ homObj M N) {U V : Cᵒᵖ} (g : U ⟶ V)
    (a : A.obj U) (m : M.obj U) :
    N.map g (pairing f U a m) = pairing f V (A.map g a) (M.map g m) := by
  have h := naturality_apply (f.app U a)
    (Over.homMk g.unop : Over.mk g.unop ⟶ Over.mk (𝟙 U.unop)).op m
  have hf := naturality_apply f g a
  dsimp only [homObj_map_apply] at hf
  dsimp only [pairing]
  rw [hf]
  exact h.symm.trans
    (restrictOver_hom_app_congr (f.app U a) (Category.id_comp g.unop).symm _)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def transposeApp (f : A ⟶ homObj M N) {U : C}
    (m : M.obj (op U)) : (restrictOver R U).obj A ⟶ (restrictOver R U).obj N where
  app W := ModuleCat.ofHom
    { toFun := fun a ↦ pairing f (op W.unop.left) a (M.map W.unop.hom.op m)
      map_add' := by
        intro a b
        dsimp only [pairing]
        rw [map_add]
        rw [add_app]
        rfl
      map_smul' := by
        intro r a
        dsimp only [pairing]
        rw [map_smul]
        rw [smul_app]
        change R.map (𝟙 W.unop.left).op r •
          pairing f (op W.unop.left) a (M.map W.unop.hom.op m) =
            r • pairing f (op W.unop.left) a (M.map W.unop.hom.op m)
        simp }
  naturality {W W'} g := by
    ext a
    change pairing f (op W'.unop.left) (A.map g.unop.left.op a)
      (M.map W'.unop.hom.op m) =
        N.map g.unop.left.op
          (pairing f (op W.unop.left) a (M.map W.unop.hom.op m))
    rw [pairing_natural]
    congr 1
    rw [← map_comp_apply, ← op_comp, Over.w]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def transpose (f : A ⟶ homObj M N) : M ⟶ homObj A N where
  app U := ModuleCat.ofHom (Y := (homObj A N).obj U)
    { toFun := transposeApp f
      map_add' := by
        intro m n
        apply hom_ext
        intro W
        ext a
        rw [add_app]
        change pairing f _ a (M.map W.unop.hom.op (m + n)) =
          pairing f _ a (M.map W.unop.hom.op m) + pairing f _ a (M.map W.unop.hom.op n)
        dsimp only [pairing]
        rw [(M.map W.unop.hom.op).hom.map_add, map_add]
      map_smul' := by
        intro r m
        apply hom_ext
        intro W
        ext a
        rw [smul_app]
        change pairing f _ a (M.map W.unop.hom.op (r • m)) =
          R.map W.unop.hom.op r • pairing f _ a (M.map W.unop.hom.op m)
        dsimp only [pairing]
        rw [M.map_smul, map_smul]
        rfl }
  naturality {U V} g := by
    ext m : 2
    apply hom_ext
    intro W
    ext a
    change pairing f (op W.unop.left) a
      (M.map W.unop.hom.op (M.map g m)) =
        pairing f (op W.unop.left) a
          (M.map (W.unop.hom ≫ g.unop).op m)
    rw [← map_comp_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
private lemma transpose_transpose (f : A ⟶ homObj M N) :
    transpose (transpose f) = f := by
  apply hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply hom_ext
  intro W
  ext m
  change pairing f (op W.unop.left) (A.map W.unop.hom.op a)
    (M.map (𝟙 W.unop.left).op m) = (f.app U a).app W m
  simp only [op_id, map_id]
  have h := naturality_apply f W.unop.hom.op a
  change _ = restrictOverMap W.unop.hom (f.app U a) at h
  dsimp only [pairing]
  rw [h]
  exact restrictOver_hom_app_congr (f.app U a) (Category.id_comp W.unop.hom) m

set_option backward.isDefEq.respectTransparency false in
private lemma transpose_pre {M' : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}
    (f : A ⟶ homObj M N) (g : M' ⟶ M) :
    transpose (f ≫ homObjMap g (𝟙 N)) = g ≫ transpose f := by
  apply hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply hom_ext
  intro W
  ext a
  change pairing f (op W.unop.left) a
    (g.app (op W.unop.left) (M'.map W.unop.hom.op m)) =
      pairing f (op W.unop.left) a (M.map W.unop.hom.op (g.app U m))
  rw [naturality_apply g]

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def transpose {A M N : Mod}
    (f : A ⟶ homObj (R := R) M N) : M ⟶ homObj (R := R) A N :=
  ⟨PresheafOfModules.transpose f.val⟩

set_option backward.isDefEq.respectTransparency false in
private lemma transpose_transpose {A M N : Mod} (f : A ⟶ homObj (R := R) M N) :
    transpose R (transpose R f) = f :=
  hom_ext (PresheafOfModules.transpose_transpose f.val)

set_option backward.isDefEq.respectTransparency false in
private lemma transpose_pre {A M M' N : Mod} (f : A ⟶ homObj (R := R) M N)
    (g : M' ⟶ M) :
    transpose R (f ≫ homObjMap (R := R) g (𝟙 N)) = g ≫ transpose R f :=
  hom_ext (PresheafOfModules.transpose_pre f.val g.val)

/-- Internal Hom into a fixed sheaf takes any coproduct cofan to a product fan.
Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO
(blueprint: lem-sc-internal-hom-coproduct-fan).

Proof: A map A → homObj M N defines a restriction-compatible bilinear pairing:
evaluate its component at U and a section a at the identity object of the slice over U.
Swapping the pairing's inputs gives a map M → homObj A N. Naturality identifies the
double transpose with the original map and makes precomposition in M correspond to
postcomposition of the transpose. These constructions are made on the underlying
presheaves and lift directly to sheaf morphisms.
For a test fan with vertex A, transpose its projections M i → homObj A N, descend
through the given coproduct, and transpose back to obtain A → homObj c.pt N.
The precomposition law and involutivity reduce factorization to the coproduct's
factorization law. Transposing a candidate lift reduces uniqueness to the coproduct's
uniqueness law. This is the local bilinear correspondence underlying Stacks 03EO;
no tensor object or sheafification is needed. The argument keeps separate object and
morphism universes. For an empty family the same universal property makes the internal
Hom terminal, and zero summands require no exception. Every constructed lift is
specified by the coproduct universal property. -/
theorem internalHomCoproductFanIsLimit {I : Type w} (M : I → Mod)
    (c : Cofan M) (hc : IsColimit c) (N : Mod) :
    Nonempty (IsLimit (Fan.mk (homObj (R := R) c.pt N)
      (fun i ↦ homObjMap (R := R) (c.inj i) (𝟙 N)))) := by
  -- Transposition swaps the two inputs of the local bilinear pairing.
  -- Applying it twice is the identity, and precomposition becomes postcomposition.
  -- Thus the coproduct desc supplies the lift and its universal property supplies uniqueness.
  classical
  let t := Fan.mk (homObj (R := R) c.pt N)
    (fun i ↦ homObjMap (R := R) (c.inj i) (𝟙 N))
  refine ⟨Fan.IsLimit.mk t
    (fun s ↦ transpose R (Cofan.IsColimit.desc hc (fun i ↦ transpose R (s.proj i))))
    (fun s i ↦ ?_) (fun s f hf ↦ ?_)⟩
  · apply_fun transpose R
    · change transpose R
        (transpose R (Cofan.IsColimit.desc hc (fun j ↦ transpose R (s.proj j))) ≫
          homObjMap (R := R) (c.inj i) (𝟙 N)) = _
      rw [transpose_pre, transpose_transpose]
      exact Cofan.IsColimit.fac hc (fun i ↦ transpose R (s.proj i)) i
    · intro f g h
      simpa only [transpose_transpose] using congrArg (transpose R) h
  · apply_fun transpose R
    · rw [transpose_transpose]
      apply Cofan.IsColimit.hom_ext hc
      intro i
      rw [Cofan.IsColimit.fac]
      exact (transpose_pre R f (c.inj i)).symm.trans (congrArg (transpose R) (hf i))
    · intro f g h
      simpa only [transpose_transpose] using congrArg (transpose R) h

end SheafOfModules
