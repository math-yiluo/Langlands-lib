/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Tilde and the unbounded total tensor complex

Source: Stacks Project, Tag 08DX, proof of the affine computation.
(blueprint: lem-pc-affine-tilde-total-tensor).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance affineTotalTensor (A : Type u) [CommRing A] :
    MonoidalCategory (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) :=
  SheafOfModules.monoidalCategory (Spec (.of A)).sheaf

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Both the global linear map and its sheaf extension are uniquely determined:
-- pure tensors generate the module tensor, and the tilde adjunction detects the extension.
private noncomputable def tildeTensorHom (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    tilde (M ⊗ N) ⟶ tilde M ⊗ tilde N :=
  (affine_tilde_tensor R M N).choose_spec.2.2.choose

private instance tildeTensorHom_isIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    IsIso (tildeTensorHom R M N) :=
  (affine_tilde_tensor R M N).choose_spec.2.2.choose_spec.2.1

open scoped TensorProduct in
private theorem tildeTensorHom_tmul (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (m : M) (n : N) :
    (tildeTensorHom R M N).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
      Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n) :=
  ((affine_tilde_tensor R M N).choose_spec.2.2.choose_spec.1 _).trans
    ((affine_tilde_tensor R M N).choose_spec.1 m n)

open scoped TensorProduct in
private theorem tildeTensor_hom_ext (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (F : (Spec R).Modules) (f g : tilde (M ⊗ N) ⟶ F)
    (h : ∀ (m : M) (n : N),
      f.app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
        g.app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n))) : f = g := by
  apply ((tilde.adjunction (R := R)).homEquiv (M ⊗ N) F).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  exact h

open scoped TensorProduct in
private theorem tildeTensorHom_naturality_left (R : CommRingCat.{u})
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    tilde.map (f ▷ N) ≫ tildeTensorHom R M' N =
      tildeTensorHom R M N ≫ tilde.map f ▷ tilde N := by
  apply tildeTensor_hom_ext
  intro m n
  change (tildeTensorHom R M' N).app ⊤
      ((tilde.map (f ▷ N)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n))) =
    (tilde.map f ▷ tilde N).app ⊤
      ((tildeTensorHom R M N).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)))
  have ht := congrArg (fun k ↦ k (m ⊗ₜ[R] n)) (tilde.toOpen_map_app (f ▷ N) ⊤)
  change (tilde.map (f ▷ N)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
    tilde.toOpen (M' ⊗ N) ⊤ (f m ⊗ₜ[R] n) at ht
  rw [ht, tildeTensorHom_tmul, tildeTensorHom_tmul,
    Scheme.Modules.whiskerRight_app_tmulSection]
  congr 1
  exact (congrArg (fun k ↦ k m) (tilde.toOpen_map_app f ⊤)).symm

open scoped TensorProduct in
private theorem tildeTensorHom_naturality_right (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    tilde.map (M ◁ g) ≫ tildeTensorHom R M N' =
      tildeTensorHom R M N ≫ tilde M ◁ tilde.map g := by
  apply tildeTensor_hom_ext
  intro m n
  change (tildeTensorHom R M N').app ⊤
      ((tilde.map (M ◁ g)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n))) =
    (tilde M ◁ tilde.map g).app ⊤
      ((tildeTensorHom R M N).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)))
  have ht := congrArg (fun k ↦ k (m ⊗ₜ[R] n)) (tilde.toOpen_map_app (M ◁ g) ⊤)
  change (tilde.map (M ◁ g)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
    tilde.toOpen (M ⊗ N') ⊤ (m ⊗ₜ[R] g n) at ht
  rw [ht, tildeTensorHom_tmul, tildeTensorHom_tmul,
    Scheme.Modules.whiskerLeft_app_tmulSection]
  congr 1
  exact (congrArg (fun k ↦ k n) (tilde.toOpen_map_app g ⊤)).symm

private noncomputable def tildeTensorNatIso (R : CommRingCat.{u}) :
    (Functor.postcompose₂.obj (tilde.functor R)).obj (curriedTensor (ModuleCat.{u} R)) ≅
      (((Functor.whiskeringLeft₂ _).obj (tilde.functor R)).obj (tilde.functor R)).obj
        (curriedTensor (Spec R).Modules) :=
  NatIso.ofComponents (fun M ↦
    NatIso.ofComponents (fun N ↦ asIso (tildeTensorHom R M N))
      (fun g ↦ tildeTensorHom_naturality_right R M g))
    (fun f ↦ by
      ext N : 2
      exact tildeTensorHom_naturality_left R f N)

private noncomputable instance affineTotalTensorColimits (A : Type u) [CommRing A] :
    Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) := by
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-- Tilde commutes naturally with the total tensor complex, for two arbitrary unbounded
module complexes. Source: Stacks Project, Tag 08DX, proof of part (2), and Tag 01I8.
(blueprint: lem-pc-affine-tilde-total-tensor).

Proof: the affine tilde tensor comparison of Tag 01I8 identifies, in each bidegree,
`tilde(P.X p) tensor tilde(N.X q)` with `tilde(P.X p tensor N.X q)`. Its uniqueness
on pure global tensors implies naturality in both factors. Consequently it respects
both differentials, including the sign on the second differential. The tilde functor
is a left adjoint to global sections, and therefore preserves every coproduct indexed
by the pairs (p,q) with p+q=n, even when the complexes are unbounded. Apply these
coproduct comparisons degreewise to obtain mutually inverse chain maps. Checking on
each summand gives naturality with respect to maps of both input complexes. Applying
Q to this natural total-complex isomorphism gives the stated localized comparison. -/
theorem affineTilde_totalTensor_natIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    Nonempty
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
        (curriedTensor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))).map₂CochainComplex ⋙
        (Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} A) ℤ)
          (CochainComplex
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
          (CochainComplex
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)).obj
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex
              (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj DerivedCategory.Q ≅
        (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q)) := by
  let T : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  let : T.Additive := by
    have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    exact Functor.additive_of_preservesBinaryBiproducts T
  let e := asIso (HomologicalComplex.mapBifunctorComparisonNatTrans
    (c₁ := .up ℤ) (c₂ := .up ℤ)
    (F := curriedTensor (ModuleCat.{u} A))
    (F' := curriedTensor
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)))
    (G₁ := T) (G₂ := T) (G := T)
    (tildeTensorNatIso (.of A)).hom (.up ℤ))
  let Q : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤
      schemeDerivedCategory (Spec (.of A)) := DerivedCategory.Q
  refine ⟨NatIso.ofComponents (fun P ↦
    NatIso.ofComponents (fun N ↦ (Q.mapIso ((e.app P).app N)).symm) ?_) ?_⟩
  · intro N N' g
    have h := (e.inv.app P).naturality g
    have h' := congrArg Q.map h
    simpa only [T, Q, id, Functor.map₂CochainComplex, Functor.map_comp,
      Functor.mapIso_inv, Iso.symm_hom, Iso.app_inv,
      Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.whiskeringRight_obj_map,
      Functor.whiskeringLeft₂, Functor.postcompose₂,
      Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.whiskeringRight_obj_obj,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatIso.ofComponents_hom_app] using h'
  · intro P P' f
    apply NatTrans.ext
    funext N
    have h := congr_app (e.inv.naturality f) N
    have h' := congrArg Q.map h
    simpa only [T, Q, id, Functor.map₂CochainComplex, Functor.map_comp,
      Functor.mapIso_inv, Iso.symm_hom, Iso.app_inv,
      Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.whiskeringRight_obj_map,
      Functor.whiskeringLeft₂, Functor.postcompose₂,
      Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.whiskeringRight_obj_obj,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatIso.ofComponents_hom_app] using h'

end AlgebraicGeometry
