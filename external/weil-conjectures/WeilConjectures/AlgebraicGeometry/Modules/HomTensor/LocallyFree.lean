/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Free

/-!
# Hom(M, N) ≅ Mᵛ ⊗ N for a finite locally free M

The morphism `Mᵛ ⊗ N ⟶ Hom(M, N)` is natural in `N`, and an isomorphism if `M` is finite locally
free (`AlgebraicGeometry.Scheme.Modules.isIso_dualTensorHom_of_isFiniteLocallyFree`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- `Mᵛ ⊗ N ⟶ Hom(M, N)` is natural in `N`. -/
lemma dualTensorHom_naturality_right (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    Mᵛ ◁ g ≫ dualTensorHom M N' =
      dualTensorHom M N ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 M) g := by
  simp only [dualTensorHom]
  rw [← Category.assoc, SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom (R := X.sheaf),
    Category.assoc,
    ← Functor.map_comp_assoc]
  erw [PresheafOfModules.dualTensorHom_naturality_right]
  rw [Functor.map_comp_assoc]
  erw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality
    (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 M) g)]
  rfl

/-- **`Hom(M, N) ≅ Mᵛ ⊗ N` for a finite locally free `M`.** The morphism
`Mᵛ ⊗ N ⟶ Hom(M, N)` is an isomorphism if `M` is finite locally free: it is the sheafification
of a morphism of presheaves which is bijective on sections over every open on which `M` is
free of finite rank. -/
instance isIso_dualTensorHom_of_isFiniteLocallyFree (M N : X.Modules)
    [M.IsFiniteLocallyFree] : IsIso (dualTensorHom M N) := by
  obtain ⟨q, hq, hf⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  have hb (V : X.Opens) (i : q.I) (g : V ⟶ q.X i) :
      Function.Bijective ((PresheafOfModules.dualTensorHom M.val N.val).app (op V)) := by
    have := (hf.isFiniteType i).finite
    have := hq.isIso i
    exact SheafOfModules.dualTensorHom_app_bijective_of_iso_free (R := X.sheaf) M N
      (asIso (q.generators i).π) g
  have hW : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (PresheafOfModules.dualTensorHom M.val N.val) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).2⟩
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  have : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.dualTensorHom M.val N.val)) := hW
  have hc : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
    (homObj M N)) := inferInstance
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' this hc)

end AlgebraicGeometry.Scheme.Modules
