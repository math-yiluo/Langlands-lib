/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
/-! # The presheaf change-of-rings map

Construction part of the tensor change-of-rings presentation.
-/

@[expose] public section

universe u
open CategoryTheory Opposite MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf change-of-rings map exists with its section formula.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps-map).

Proof: on an open W send (c,p) to eta_W(c tensor_B p), where eta is
the change-of-rings sheafification unit. Additivity in each variable follows
from additivity of the pure tensor and linearity of eta. For a section r of
O_Y, the second-factor relation gives c tensor_B (B.hom(r)p) =
phi(B.hom(r))c tensor_B p = C.hom(r)c tensor_B p. Thus the pairing is
O_Y-balanced, and linear in either factor for the restricted O_Y-action on
the target. The sectionwise tensor universal property gives an O_Y-linear
map C(W) tensor_O P(W) to T(W). Restrictions send c tensor_B p to the tensor
of the restricted factors, and eta is natural; hence these maps commute
with restrictions on pure tensors. Tensor induction extends this equality
to every section. They therefore form the required presheaf morphism.
There is no sheafification extension in this lemma. Empty opens and zero
modules satisfy the same tensor universal properties.
-/
theorem exists_changeOfRings_tensor_presheaf_map (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    letI := presheafMonoidalCategory Y
    ∃ (g : C.toModule.val ⊗ P₀.val ⟶ T.val),
      ∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app (op W) (c ⊗ₜ[Y.presheaf.obj (op W)] p) =
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
            (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p) := by
  classical
  dsimp only
  let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
  let Q := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app Q
  let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
    (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
  let := presheafMonoidalCategory Y
  let a (W : Y.Opensᵒᵖ) : (C.toModule.val ⊗ P₀.val).obj W ⟶ T.val.obj W :=
    ModuleCat.MonoidalCategory.tensorLift
      (fun c p ↦ η.app W (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p))
      (by
        intro c d p
        exact (congrArg (η.app W) (TensorProduct.add_tmul
          (M := (ModuleCat.restrictScalars (φ.right.hom.app W).hom).obj
            (ModuleCat.of (C.right.obj.obj W) (C.right.obj.obj W)))
          (N := P.val.obj W) c d p)).trans
          ((η.app W).hom.map_add _ _))
      (by
        intro r c p
        change η.app W ((C.hom.hom.app W r * (show C.right.obj.obj W from c))
          ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p) = C.hom.hom.app W r • _
        exact (η.app W).hom.map_smul (C.hom.hom.app W r)
          (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p))
      (by
        intro c p q
        exact (congrArg (η.app W) (TensorProduct.tmul_add
          (M := (ModuleCat.restrictScalars (φ.right.hom.app W).hom).obj
            (ModuleCat.of (C.right.obj.obj W) (C.right.obj.obj W)))
          (N := P.val.obj W) c p q)).trans
          ((η.app W).hom.map_add _ _))
      (by
        intro r c p
        change η.app W (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom]
          (B.hom.hom.app W r • (show P.val.obj W from p))) = C.hom.hom.app W r • _
        let : Module (B.right.obj.obj W) (C.right.obj.obj W) :=
          Module.compHom (C.right.obj.obj W) (φ.right.hom.app W).hom
        change η.app W (c ⊗ₜ[B.right.obj.obj W]
          (B.hom.hom.app W r • (show P.val.obj W from p))) = _
        refine (congrArg (η.app W)
          (TensorProduct.tmul_smul (R := B.right.obj.obj W) (B.hom.hom.app W r)
            (show C.right.obj.obj W from c) (show P.val.obj W from p))).trans ?_
        have h : φ.right.hom.app W (B.hom.hom.app W r) = C.hom.hom.app W r := by
          have hw := congrArg (fun f ↦ f.hom.app W) (CategoryTheory.Under.w φ)
          exact congrArg (fun f ↦ f r) hw
        change η.app W ((φ.right.hom.app W (B.hom.hom.app W r) *
          (show C.right.obj.obj W from c)) ⊗ₜ[B.right.obj.obj W,
          (φ.right.hom.app W).hom] p) = _
        exact (congrArg (fun s : C.right.obj.obj W ↦ η.app W
          ((s * (show C.right.obj.obj W from c))
            ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] (show P.val.obj W from p))) h).trans
          ((η.app W).hom.map_smul (C.hom.hom.app W r)
            (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p)))
  refine ⟨{ app := a, naturality := ?_ }, ?_⟩
  · intro U V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro c p
    change η.app V (C.right.obj.map f c ⊗ₜ[B.right.obj.obj V,
      (φ.right.hom.app V).hom] P.val.map f p) =
      T.val.map f (η.app U (c ⊗ₜ[B.right.obj.obj U, (φ.right.hom.app U).hom] p))
    have ht := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ.right P f) c p
    change Q.map f (c ⊗ₜ[B.right.obj.obj U, (φ.right.hom.app U).hom] p) = _ at ht
    exact (congrArg (η.app V) ht.symm).trans (PresheafOfModules.naturality_apply η f _)
  · intro W c p
    rfl
end AlgebraicGeometry.Scheme.Modules
