/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Universal property of the change-of-rings balancing map

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-balancing-universal).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence clause for the balancing factorization.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: aux-lem-weil-pbc-change-of-rings-tensor-balancing-universal-exists)
The sectionwise balanced map factors through the change-of-rings sheafification by
the tensor universal property and sheafification universal property. -/
theorem changeOfRings_tensor_balancing_universal_exists (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    ∀ (a d : tensorObj B.toModule S ⟶ S) (g : S ⟶ T),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        a.app W (tmulSection (M := B.toModule)
          b (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p)) →
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        d.app W (tmulSection (M := B.toModule)
          b (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀)
            (φ.right.hom.app (op W) b * c) p) →
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app W (tmulSection (M := C.toModule) (N := P₀) c p) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app
              (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) →
      ∀ (Q : Y.Modules) (f : S ⟶ Q), a ≫ f = d ≫ f → ∃ t : T ⟶ Q, g ≫ t = f := by
  classical
  -- Evaluate the equality of action composites on a nested pure tensor.
  intro P₀ S T a d g ha hd hg Q f hfd
  let K := (PresheafOfModules.restrictScalars (𝓻 C.hom).hom).obj
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)
  have hb (W : Y.Opens) (b : B.right.obj.obj (op W))
      (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)) :
      f.app W (tmulSection (M := C.toModule) (N := P₀)
        (φ.right.hom.app (op W) b * c) p) =
      f.app W (tmulSection (M := C.toModule) (N := P₀) c (b • p)) := by
    have h := congrArg (fun k ↦ k.app W (tmulSection (M := B.toModule)
      b (tmulSection (M := C.toModule) (N := P₀) c p))) hfd
    change f.app W (a.app W _) = f.app W (d.app W _) at h
    rw [ha, hd] at h
    exact h.symm
  -- Lift the resulting balanced additive pairing sectionwise.
  let h (W : Y.Opens) : C.right.obj.obj (op W) →+ P.val.obj (op W) →+
      Q.val.obj (op W) :=
    { toFun := fun c ↦
        { toFun := fun p ↦ f.app W (tmulSection (M := C.toModule) (N := P₀) c p)
          map_zero' := by
            rw [tmulSection_zero (M := C.toModule) (N := P₀), map_zero]
          map_add' := fun p p' ↦
            (congrArg (f.app W) (tmulSection_add (M := C.toModule) (N := P₀) c p p')).trans
              ((f.app W).hom.map_add _ _) }
      map_zero' := by
        apply AddMonoidHom.ext
        intro p
        change f.app W (tmulSection (M := C.toModule) (N := P₀) 0 p) = 0
        rw [zero_tmulSection, map_zero]
      map_add' := by
        intro c c'
        apply AddMonoidHom.ext
        intro p
        exact (congrArg (f.app W)
          (add_tmulSection (M := C.toModule) (N := P₀) c c' p)).trans
            ((f.app W).hom.map_add _ _) }
  let L (W : Y.Opens) : K.obj (op W) →+ Q.val.obj (op W) :=
    TensorProduct.liftAddHom (h W) (hb W)
  have hL (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)) :
      L W (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p) =
        f.app W (tmulSection (M := C.toModule) (N := P₀) c p) :=
    TensorProduct.liftAddHom_tmul _ _ _ _
  -- The lift is O-linear and restriction-compatible by tensor induction.
  let k : K ⟶ Q.val :=
    { app := fun W ↦ ModuleCat.ofHom (X := K.obj W) (Y := Q.val.obj W)
        { toFun := L W.unop
          map_add' := (L W.unop).map_add
          map_smul' := by
            intro r x
            induction x using TensorProduct.inductionOn with
            | tmul c p =>
              change L W.unop ((C.hom.hom.app W r *
                (show C.right.obj.obj W from c)) ⊗ₜ[B.right.obj.obj W,
                  (φ.right.hom.app W).hom] p) = _
              rw [hL, hL]
              exact (congrArg (f.app W.unop)
                (smul_tmulSection (M := C.toModule) (N := P₀) r c p)).trans
                ((f.val.app W).hom.map_smul r _)
            | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy }
      naturality := by
        intro W V i
        ext x
        induction x using TensorProduct.inductionOn with
        | tmul c p =>
          change L V.unop (SheafOfModules.changeOfRingsMap φ.right P i
            (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p)) =
            Q.val.map i (L W.unop (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p))
          rw [show SheafOfModules.changeOfRingsMap φ.right P i
            (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p) = _ from
            Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ.right P i) c p]
          rw [hL, hL]
          have hn := PresheafOfModules.naturality_apply f.val i
            (tmulSection (M := C.toModule) (N := P₀) c p)
          change f.app V.unop ((tensorObj C.toModule P₀).val.map i (tmulSection
            (M := C.toModule) (N := P₀) c p)) = _ at hn
          exact (congrArg (f.app V.unop) (tmulSection_map
            (M := C.toModule) (N := P₀) (leOfHom i.unop) c p).symm).trans hn
        | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy }
  -- Scalar restriction leaves the underlying additive sheafification unit unchanged.
  let η : K ⟶ T.val :=
    (PresheafOfModules.restrictScalars (𝓻 C.hom).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P))
  let : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology Y) η := by
    change Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify _ _)
    infer_instance
  let : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology Y) η := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify _ _)
    infer_instance
  let t : T ⟶ Q := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective η Q.isSheaf).symm k⟩
  have ht : η ≫ t.val = k :=
    (PresheafOfModules.homEquivOfIsLocallyBijective η Q.isSheaf).apply_symm_apply k
  -- Compare the two maps out of the sheaf tensor on pure tensors before sheafification.
  refine ⟨t, ?_⟩
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification C.toModule P₀).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv (MonoidalCategory.tensorObj C.toModule.val P₀.val) Q).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro c p
  change t.val.app W (g.app W.unop (tmulSection (M := C.toModule) (N := P₀) c p)) =
    f.app W.unop (tmulSection (M := C.toModule) (N := P₀) c p)
  rw [hg]
  exact (congrArg (fun k ↦ k.app W
    (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p)) ht).trans (hL W.unop c p)

end AlgebraicGeometry.Scheme.Modules
