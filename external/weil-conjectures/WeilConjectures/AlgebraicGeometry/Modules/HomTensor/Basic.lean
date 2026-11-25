/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Presheaf

/-!
# The morphism Mᵛ ⊗ N ⟶ Hom(M, N) of sheaves of modules on a scheme

The morphism `Mᵛ ⊗ N ⟶ Hom(M, N)` of sheaves of modules on a scheme
(`AlgebraicGeometry.Scheme.Modules.dualTensorHom`), its naturality in `M`, and the isomorphism
`Mᵛ ⊗ N ≅ Hom(M, N)` for an invertible `N` (`AlgebraicGeometry.Scheme.Modules.dualTensorHomIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The identification `M ⊗ P ≅ a(M ⊗ P)` of the tensor product of sheaves of modules with the
sheafification of the tensor product of presheaves is natural in `M`: for `f : M ⟶ M'` the square
```
  M ⊗ P  ---------> a(M ⊗ P)
    |                  |
  f ⊗ P             a(f ⊗ P)
    v                  v
  M' ⊗ P ---------> a(M' ⊗ P)
```
commutes. -/
lemma whiskerRight_tensorObjIsoSheafification_hom {M M' : X.Modules} (f : M ⟶ M')
    (P : X.Modules) :
    f ▷ P ≫ (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M' P).hom =
      (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M P).hom ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ▷ P.val) := by
  exact SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom (R := X.sheaf) f P

/-- The morphism `Mᵛ ⊗ N ⟶ Hom(M, N)`, `φ ⊗ n ↦ (m ↦ φ(m) n)`, of sheaves of modules: the
sheafification of the corresponding morphism of presheaves of modules. -/
noncomputable def dualTensorHom (M N : X.Modules) : Mᵛ ⊗ N ⟶ homObj M N :=
  (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) Mᵛ N).hom ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.dualTensorHom M.val N.val) ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (homObj M N)

/-- If `N` is trivial on an open `U`, then `Mᵛ ⊗ N ⟶ Hom(M, N)` is bijective on sections of
the underlying presheaves over every open `V ⊆ U`. -/
lemma presheafDualTensorHom_app_bijective {M N : X.Modules} {U V : X.Opens} (g : V ⟶ U)
    (E : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Bijective ((PresheafOfModules.dualTensorHom M.val N.val).app (op V)) := by
  have hE (W : Over V) : N.val.map W.hom.op (E.inv.val.app (op (Over.mk g)) (1 : Γ(X, V))) =
      E.inv.val.app (op (Over.mk (W.hom ≫ g))) (1 : Γ(X, W.left)) := by
    refine (PresheafOfModules.naturality_apply E.inv.val
      (Over.homMk W.hom (Subsingleton.elim _ _) : Over.mk (W.hom ≫ g) ⟶ Over.mk g).op
      (1 : Γ(X, V))).symm.trans ?_
    exact congrArg (E.inv.val.app (op (Over.mk (W.hom ≫ g))))
      (PresheafOfModules.unit_map_one (R := X.ringCatSheaf.obj) W.hom.op)
  refine PresheafOfModules.dualTensorHom_app_bijective
    (E.inv.val.app (op (Over.mk g)) (1 : Γ(X, V)))
    { app W := E.hom.val.app (op (Over.mk (W.unop.hom ≫ g)))
      naturality {A B} f := E.hom.val.naturality (Over.homMk f.unop.left (Subsingleton.elim _ _) :
        Over.mk (B.unop.hom ≫ g) ⟶ Over.mk (A.unop.hom ≫ g)).op } (fun W r ↦ ?_) (fun W x ↦ ?_)
  · have h1 : E.hom.val.app (op (Over.mk (W.unop.hom ≫ g)))
        (E.inv.val.app (op (Over.mk (W.unop.hom ≫ g))) (1 : Γ(X, W.unop.left))) =
          (1 : Γ(X, W.unop.left)) :=
      congrArg (fun f ↦ f.val.app (op (Over.mk (W.unop.hom ≫ g))) (1 : Γ(X, W.unop.left)))
        E.inv_hom_id
    erw [hE W.unop, (E.hom.val.app _).hom.map_smul, h1]
    exact mul_one r
  · refine ⟨E.hom.val.app (op (Over.mk (W.unop.hom ≫ g))) x, ?_⟩
    have h2 : E.inv.val.app (op (Over.mk (W.unop.hom ≫ g)))
        (E.hom.val.app (op (Over.mk (W.unop.hom ≫ g))) x) = x :=
      congrArg (fun f ↦ f.val.app (op (Over.mk (W.unop.hom ≫ g))) x) E.hom_inv_id
    erw [hE W.unop, ← (E.inv.val.app _).hom.map_smul, smul_eq_mul, mul_one, h2]

/-- **`Hom(M, N) ≅ Mᵛ ⊗ N` for an invertible `N`.** The morphism `Mᵛ ⊗ N ⟶ Hom(M, N)` is an
isomorphism if `N` is invertible: it is the sheafification of a morphism of presheaves which is
bijective on sections over every open on which `N` is trivial. -/
instance isIso_dualTensorHom (M N : X.Modules) [N.IsInvertible] : IsIso (dualTensorHom M N) := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := N) x
  have hcov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact TopologicalSpace.IsOpenCover.mk
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩)
  have hW : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (PresheafOfModules.dualTensorHom M.val N.val) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop hcov _ fun V x g ↦
        (presheafDualTensorHom_app_bijective g (overIsoUnitOfPullbackIotaIso (e x).some)).1,
      Presheaf.isLocallySurjective_of_coversTop hcov _ fun V x g ↦
        (presheafDualTensorHom_app_bijective g (overIsoUnitOfPullbackIotaIso (e x).some)).2⟩
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  have : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.dualTensorHom M.val N.val)) := hW
  have hc : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
    (homObj M N)) := inferInstance
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' this hc)

/-- `Mᵛ ⊗ N ⟶ Hom(M, N)` is natural in `M`: for `f : M ⟶ M'` the square
```
  M'ᵛ ⊗ N ---> Hom(M', N)
     |              |
  fᵛ ⊗ N           f^*
     v              v
  Mᵛ ⊗ N  ---> Hom(M, N)
```
commutes. -/
lemma dualTensorHom_naturality {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules) :
    dualMap f ▷ N ≫ dualTensorHom M N =
      dualTensorHom M' N ≫ SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 N) := by
  simp only [dualTensorHom]
  rw [← Category.assoc, whiskerRight_tensorObjIsoSheafification_hom, Category.assoc,
    ← Functor.map_comp_assoc]
  erw [PresheafOfModules.dualTensorHom_naturality]
  rw [Functor.map_comp_assoc]
  erw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality
    (SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 N))]
  rfl

/-- **`Hom(M, N) ≅ Mᵛ ⊗ N` for an invertible `N`**, naturally in `M`. -/
noncomputable def dualTensorHomIso (N : X.Modules) [N.IsInvertible] :
    dualFunctor X ⋙ tensorRight N ≅ (SheafOfModules.homFunctor X.sheaf).flip.obj N :=
  NatIso.ofComponents (fun M ↦ asIso (dualTensorHom M.unop N)) fun f ↦
    dualTensorHom_naturality f.unop N

end AlgebraicGeometry.Scheme.Modules
