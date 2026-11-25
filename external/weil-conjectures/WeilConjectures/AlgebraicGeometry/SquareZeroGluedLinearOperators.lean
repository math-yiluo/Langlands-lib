/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

import WeilConjectures.AlgebraicGeometry.SquareZeroGluedScalarExistsUnique



/-! # The quotient action on a square-zero ideal

Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Linear operators obtained by multiplying with local lifts in a square-zero extension.
Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of its proof.
(blueprint: lem-sc-square-zero-glued-linear-operators)

Proof: Short exactness identifies I with the kernel of p, sectionwise. Cover U by
opens on which f lifts to b. The product b*i(x) is in the kernel and has a unique
preimage in I. On overlaps two lifts differ by a kernel section, which annihilates
i(x) by square-zero. The preimages glue uniquely. The construction is additive and
O_X(U)-linear in x: check these identities after restricting to the lifting cover,
apply the injective inclusion i, and use distributivity and commutativity in B.
This gives a linear endomorphism for each f, without asserting any ring laws in f.
Uniqueness of gluing proves restriction compatibility. For f=p(b), use b itself
as a lift. Empty opens and the zero kernel are covered by the same uniqueness
argument. No chosen object is installed as a definition. -/
theorem square_zero_glued_linear_operators (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0) :
    ∃ (σ : ∀ U : X.Opens, C.right.obj.obj (op U) →
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U))),
      (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        @id (B.right.obj.obj (op U)) (i.val.app (op U) (σ U (p.right.hom.app (op U) b) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) ∧
      (∀ (U V : X.Opens) (j : V ⟶ U) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
        I.val.map j.op (σ U f x) = σ V (C.right.obj.map j.op f) (I.val.map j.op x)) := by
  classical
  have hex := square_zero_glued_scalar_exists_unique X B C p I i hw hS hsq
  choose a ha hu using hex
  dsimp only [id] at ha hu
  have hadd (U : X.Opens) (f : C.right.obj.obj (op U)) (x y : I.val.obj (op U)) :
      a U f (x + y) = a U f x + a U f y := by
    symm
    apply hu U f (x + y)
    intro V j b hb
    simp only [map_add, ha U f x V j b hb, ha U f y V j b hb, mul_add]
  have hsmul (U : X.Opens) (f : C.right.obj.obj (op U))
      (r : (moduleRings X.toRingedSpace).obj.obj (op U)) (x : I.val.obj (op U)) :
      a U f (r • x) = r • a U f x := by
    symm
    apply hu U f (r • x)
    intro V j b hb
    rw [I.val.map_smul, I.val.map_smul]
    simp only [map_smulₛₗ, RingHom.id_apply]
    rw [ha U f x V j b hb]
    change _ * (b * _) = b * (_ * _)
    exact mul_left_comm _ _ _
  let α (U : X.Opens) (f : C.right.obj.obj (op U)) :
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U)) :=
    { toFun := a U f
      map_add' := hadd U f
      map_smul' := hsmul U f }
  refine ⟨α, ?_, ?_⟩
  · intro U b x
    change @id (B.right.obj.obj (op U))
      (i.val.app (op U) (a U (p.right.hom.app (op U) b) x)) =
        b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)
    simpa using ha U (p.right.hom.app (op U) b) x U (𝟙 U) b (by simp)
  · intro U V j f x
    change I.val.map j.op (a U f x) = a V (C.right.obj.map j.op f) (I.val.map j.op x)
    apply hu V (C.right.obj.map j.op f) (I.val.map j.op x)
    intro W k b hb
    have hcomp : p.right.hom.app (op W) b = C.right.obj.map (k ≫ j).op f := by
      simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hb
    simpa only [op_comp, PresheafOfModules.map_comp_apply]
      using ha U f x W (k ≫ j) b hcomp


end AlgebraicGeometry
