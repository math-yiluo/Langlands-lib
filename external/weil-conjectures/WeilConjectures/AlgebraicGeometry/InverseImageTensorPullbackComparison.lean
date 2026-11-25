/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Inverse image as tensor pullback along the identity adjoint ring map

Source: Stacks Project, Sheaves, Tags 008A and 0094; Cohomology, Tag 06YC.
(blueprint: lem-pc-inverse-image-tensor-pullback-comparison).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def changeOfRingsPresheafIdIso {X : TopCat.{u}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    M.val ≅ SheafOfModules.changeOfRingsPresheaf.{u, u, u} (𝟙 R) M := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (M.val.obj U)).symm) ?_
  intro U V i
  ext m
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (M.val.obj V)
      (M.val.map i m) =
    SheafOfModules.changeOfRingsMap.{u, u, u} (𝟙 R) M i
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [SheafOfModules.changeOfRingsMap] using
    (Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u, u, u} (𝟙 R) M i) (1 : R.obj.obj U) m).symm


private def changeOfRingsIdIso {X : TopCat.{u}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    SheafOfModules.changeOfRings.{u, u, u} (𝟙 R) M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso (changeOfRingsPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M)

private theorem changeOfRingsIdIso_naturality {X : TopCat.{u}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    {M N : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N) :
    (changeOfRingsIdIso R M).hom ≫ a =
      SheafOfModules.changeOfRingsHom.{u, u, u} (𝟙 R) M a ≫
        (changeOfRingsIdIso R N).hom := by
  let F := PresheafOfModules.sheafification (𝟙
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  let ψ : SheafOfModules.changeOfRingsPresheaf.{u, u, u} (𝟙 R) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} (𝟙 R) N :=
    { app := fun U ↦ (ModuleCat.extendScalars (RingHom.id (R.obj.obj U))).map (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (𝟙 R) M a }
  have hp : (changeOfRingsPresheafIdIso R M).hom ≫ ψ =
      a.val ≫ (changeOfRingsPresheafIdIso R N).hom := by
    ext U m
    change (ModuleCat.extendScalars (RingHom.id (R.obj.obj U))).map (a.val.app U)
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m) =
        (ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (N.val.obj U) (a.val.app U m)
    exact ConcreteCategory.congr_hom ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.naturality
      (a.val.app U)) m
  have hp' : (changeOfRingsPresheafIdIso R M).inv ≫ a.val =
      ψ ≫ (changeOfRingsPresheafIdIso R N).inv := by
    rw [← cancel_epi (changeOfRingsPresheafIdIso R M).hom]
    simp only [← Category.assoc, hp]
    simp
  change F.map (changeOfRingsPresheafIdIso R M).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (changeOfRingsPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit_naturality a]
  change F.map (changeOfRingsPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]

private def changeOfRingsEqIdIso {X : TopCat.{u}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (α : R ⟶ R) (hα : α = 𝟙 R)
    (M : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    SheafOfModules.changeOfRings.{u, u, u} α M ≅ M := by
  subst α
  exact changeOfRingsIdIso R M

private theorem changeOfRingsEqIdIso_naturality {X : TopCat.{u}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (α : R ⟶ R) (hα : α = 𝟙 R)
    {M N : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N) :
    (changeOfRingsEqIdIso R α hα M).hom ≫ a =
      SheafOfModules.changeOfRingsHom.{u, u, u} α M a ≫
        (changeOfRingsEqIdIso R α hα N).hom := by
  subst α
  exact changeOfRingsIdIso_naturality R a

/-- Tensor pullback to the inverse-image ring agrees with termwise module inverse image.
Source: Stacks Project, Sheaves, Tags 008A and 0094; Cohomology, Tag 06YC.

Proof: the adjoint of the inverse-image ring adjunction unit is the identity on
`inverseImageRing f R`, by the adjunction triangle identity. In degree `n`, the tensor
pullback therefore extends scalars along the identity on that ring sheaf. On sections,
identify `A ⊗[A] M` with `M` by `a ⊗ m ↦ a • m`, with inverse `m ↦ 1 ⊗ m`.
The balancing relation proves both inverse identities. The characterized restrictions
of `changeOfRingsPresheaf` commute with these maps, since module restrictions are
semilinear. Thus they form an isomorphism of presheaves of modules. Sheafify it and
compose with the sheafification counit isomorphism for the already sheaf-valued
inverse-image module. Naturality in module maps follows on pure tensors from
`id ⊗ a` and `a (r • m) = r • a m`, and survives sheafification. Apply this naturality
to each differential of `K` to get inverse morphisms of complexes degreewise.
This uses neither K-flatness nor exactness; it also applies to empty spaces and to
zero rings and modules.
(blueprint: lem-pc-inverse-image-tensor-pullback-comparison). -/
theorem exists_inverseImage_tensorPullback_iso {X Y : TopCat.{u}} (f : X ⟶ Y)
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    Nonempty (CochainComplex.tensorPullbackComplex f (inverseImageRing f R) R
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) CommRingCat.{u} _ _).unit.app R) K ≅
      ((inverseImageModuleFunctor f R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) CommRingCat.{u} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
  have hα : CochainComplex.tensorPullbackRingMap f (inverseImageRing f R) R
      (adj.unit.app R) = 𝟙 (inverseImageRing f R) := adj.homEquiv_symm_unit R
  let e (M : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
      SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap f (inverseImageRing f R) R (adj.unit.app R))
        (inverseImageModule f R M) ≅ inverseImageModule f R M :=
    changeOfRingsEqIdIso (inverseImageRing f R) _ hα (inverseImageModule f R M)
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun i ↦ e (K.X i)) ?_⟩
  intro i j _
  change (e (K.X i)).hom ≫ inverseImageModuleMap f R (K.X i) (K.d i j) =
    SheafOfModules.changeOfRingsHom.{u, u, u}
      (CochainComplex.tensorPullbackRingMap f (inverseImageRing f R) R (adj.unit.app R))
      (inverseImageModule f R (K.X i)) (inverseImageModuleMap f R (K.X i) (K.d i j)) ≫
        (e (K.X j)).hom
  exact changeOfRingsEqIdIso_naturality (inverseImageRing f R) _ hα
    (inverseImageModuleMap f R (K.X i) (K.d i j))

end
end TopCat.Sheaf
