/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.BalancedActionAffineOpen
import WeilConjectures.AlgebraicGeometry.AffineBaseChangeSectionsInduction

/-! # Balanced actions on affine sections of the direct-image algebra

Source: Stacks Project, Tags 01LX, 01SB and 0897, affine tensor-action construction.
(blueprint: lem-weil-pbc-balanced-action-affine-sections).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- The balanced tensor action on affine opens, including compatibility on inclusions.

Source: Stacks Project, Tags 01LX (2)-(3), 01SB and 0897, relative-spectrum paragraph.
(blueprint: lem-weil-pbc-balanced-action-affine-sections).

Proof: For U affine, write D = O_X(U) and N = M(U). Affine base change identifies
O_Y(pi inverse U) with D tensor_A B, sending pi-sharp(d) to d tensor 1 and
fB-sharp(b) to 1 tensor b. The endomorphisms rho(b)_U are D-linear; their
A-action agrees with the D-action by the scalar hypothesis. The tensor-product
universal property gives the unique action (d tensor b)x = d rho(b)_U(x), and
its unit, multiplication, and addition identities give a ring map to additive
endomorphisms of N. This proves the two displayed generator identities and
uniqueness on each affine U. For an inclusion of affine opens V into U, the
restriction on the direct-image algebra sends pi-sharp(d) to pi-sharp(d|V)
and fB-sharp(b)|pi-inverse(U) to fB-sharp(b)|pi-inverse(V). On the former
generators compatibility is semilinearity of the original module restrictions;
on the latter it is naturality of rho(b). Each tensor is a finite sum of pure
tensors, so additivity proves compatibility for every algebra section. Thus
no affine intersection is assumed affine and no localization of M is needed.
The tensor universal property also handles zero modules and zero rings. -/
theorem balancedAction_affine_sections
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (M : X.Modules) (hM : M.IsQuasicoherent)
    (rho : B →+* End M)
    (hscalar : ∀ a : A, rho (algebraMap A B a) =
      .of (M.smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a))) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf
    ∃! tau : ∀ U : X.affineOpens,
      C.obj.obj (op U.val) →+* AddMonoid.End (M.val.obj (op U.val)),
      (∀ (U V : X.affineOpens) (i : U.val ⟶ V.val)
        (r : C.obj.obj (op V.val)) (x : M.val.obj (op V.val)),
        M.val.map i.op (tau V r x) =
          tau U (C.obj.map i.op r) (M.val.map i.op x)) ∧
      (∀ (U : X.affineOpens) (r : X.presheaf.obj (op U.val))
        (x : M.val.obj (op U.val)), tau U (pi.app U.val r) x = r • x) ∧
      (∀ (U : X.affineOpens) (b : B) (x : M.val.obj (op U.val)),
        tau U (Y.presheaf.map (homOfLE (le_top (a := pi ⁻¹ᵁ U.val))).op
          (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b)) x =
            (rho b).asHom.val.app (op U.val) x) := by
  classical
  dsimp only
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let Y := pullback f g
  let pi : Y ⟶ X := pullback.fst f g
  let fB : Y ⟶ Spec (.of B) := pullback.snd f g
  let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf
  have hex (U : X.affineOpens) := balancedAction_affine_open f M hM rho hscalar U
  let tau := fun U ↦ Classical.choose (hex U)
  have ht (U : X.affineOpens) := Classical.choose_spec (hex U)
  have hd (U : X.affineOpens) := (ht U).1.1
  have hb (U : X.affineOpens) := (ht U).1.2
  refine ⟨tau, ⟨?_, hd, hb⟩, ?_⟩
  · intro U V i r x
    have hn : ∀ r : C.obj.obj (op V.val), ∀ x : M.val.obj (op V.val),
        M.val.map i.op (tau V r x) =
          tau U (C.obj.map i.op r) (M.val.map i.op x) := by
      apply affineBaseChange_sections_induction f V
      · intro d x
        rw [hd V]
        have he := (CategoryTheory.congr_fun (pi.naturality i.op) d).symm
        change C.obj.map i.op (pi.app V.val d) =
          pi.app U.val (X.presheaf.map i.op d) at he
        rw [he, hd U]
        exact M.val.map_smul i.op d x
      · intro b x
        rw [hb V]
        have he : C.obj.map i.op
            (Y.presheaf.map (homOfLE (le_top (a := pi ⁻¹ᵁ V.val))).op
              (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b)) =
            Y.presheaf.map (homOfLE (le_top (a := pi ⁻¹ᵁ U.val))).op
              (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b) := by
          change Y.presheaf.map _ (Y.presheaf.map _ _) = _
          rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
          rfl
        rw [he, hb U]
        exact (PresheafOfModules.naturality_apply (rho b).asHom.val i.op x).symm
      · intro r s hr hs x
        rw [map_add, map_add, map_add]
        change M.val.map i.op (tau V r x + tau V s x) =
          tau U (C.obj.map i.op r) (M.val.map i.op x) +
            tau U (C.obj.map i.op s) (M.val.map i.op x)
        rw [map_add, hr, hs]
      · intro r s hr hs x
        rw [map_mul, map_mul, map_mul]
        change M.val.map i.op (tau V r (tau V s x)) =
          tau U (C.obj.map i.op r) (tau U (C.obj.map i.op s) (M.val.map i.op x))
        rw [hr, hs]
    exact hn r x
  · intro tau' ht'
    funext U
    exact (ht U).2 (tau' U) ⟨ht'.2.1 U, ht'.2.2 U⟩


end AlgebraicGeometry
