/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars

/-!
# Extension of scalars of sheaves of modules preserves flatness

Let `S` be an algebra over a commutative ring `R`, not necessarily flat. For a module `M` over
`S` and a module `N` over `R`, the module `M ⊗_S (S ⊗_R N)` with scalars restricted to `R` is
`M ⊗_R N` (`ModuleCat.restrictScalarsTensorExtendScalarsIso`). Sheafifying, for sheaves `M` of
`S`-modules and `N` of `R`-modules on a site, `M ⊗ (S ⊗_R N)` with scalars restricted to `R` is
`M ⊗ N` (`CategoryTheory.Sheaf.tensorRightExtendScalarsCompRestrictScalarsIso`). Since
restriction of scalars is exact and reflects isomorphisms, extension of scalars sends flat
sheaves to flat sheaves (`CategoryTheory.Sheaf.flat_extendScalars_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The linear equivalence `M ⊗_S (S ⊗_R N) ≃ M ⊗_R N`, for a module `M` over `S` and a module
`N` over `R`, with scalars restricted to `R`. -/
noncomputable def restrictScalarsTensorExtendScalarsEquiv (M : ModuleCat.{u} S)
    (N : ModuleCat.{u} R) :
    (restrictScalars φ).obj (M ⊗ (extendScalars φ).obj N) ≃ₗ[R]
      ((restrictScalars φ).obj M ⊗ N : ModuleCat R) :=
  letI := φ.toAlgebra
  letI : Module R M := Module.compHom M φ
  haveI : IsScalarTower R S M := ⟨fun r s m ↦ mul_smul (φ r) s m⟩
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M N).restrictScalars R

lemma restrictScalarsTensorExtendScalarsEquiv_tmul (M : ModuleCat.{u} S)
    (N : ModuleCat.{u} R) (m : M) (s : S) (n : N) :
    restrictScalarsTensorExtendScalarsEquiv φ M N (m ⊗ₜ (s ⊗ₜ n)) =
      TensorProduct.tmul R (M := (restrictScalars φ).obj M) (s • m) n :=
  rfl


/-- The isomorphism `M ⊗_S (S ⊗_R N) ≅ M ⊗_R N` of modules over `R`, for a module `M` over `S`
and a module `N` over `R`. -/
noncomputable def restrictScalarsTensorExtendScalarsIso (M : ModuleCat.{u} S)
    (N : ModuleCat.{u} R) :
    (restrictScalars φ).obj (M ⊗ (extendScalars φ).obj N) ≅ (restrictScalars φ).obj M ⊗ N :=
  (restrictScalarsTensorExtendScalarsEquiv φ M N).toModuleIso

/-- The naturality of `M ⊗_S (S ⊗_R N) ≅ M ⊗_R N` in `M` and `N`. -/
@[reassoc]
lemma restrictScalarsTensorExtendScalarsIso_hom_naturality {M M' : ModuleCat.{u} S}
    {N N' : ModuleCat.{u} R} (f : M ⟶ M') (g : N ⟶ N') :
    (restrictScalars φ).map (f ⊗ₘ (extendScalars φ).map g) ≫
        (restrictScalarsTensorExtendScalarsIso φ M' N').hom =
      (restrictScalarsTensorExtendScalarsIso φ M N).hom ≫ ((restrictScalars φ).map f ⊗ₘ g) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  induction x using TensorProduct.inductionOn with
  | tmul m t =>
    induction t using TensorProduct.inductionOn with
    | tmul s n =>
      exact congrArg (fun y ↦ TensorProduct.tmul R (M := (restrictScalars φ).obj M') y (g n))
        (f.hom.map_smul s m).symm
    | add t t' ht ht' =>
      erw [TensorProduct.tmul_add]
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ht ht').trans (map_add _ _ _).symm)
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end ModuleCat

namespace CategoryTheory

namespace Presheaf

variable {C : Type*} [Category* C] {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- For presheaves `Q` of `S`-modules and `P` of `R`-modules, `Q ⊗ (S ⊗_R P)` with scalars
restricted to `R` is `Q ⊗ P`, naturally in `Q`. -/
noncomputable def tensorRightExtendScalarsCompRestrictScalarsIso (P : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    tensorRight (P ⋙ ModuleCat.extendScalars φ) ⋙
        (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.restrictScalars φ) ≅
      (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.restrictScalars φ) ⋙ tensorRight P :=
  NatIso.ofComponents
    (fun Q ↦ NatIso.ofComponents
      (fun U ↦ ModuleCat.restrictScalarsTensorExtendScalarsIso φ (Q.obj U) (P.obj U))
      (fun f ↦ ModuleCat.restrictScalarsTensorExtendScalarsIso_hom_naturality φ _ _))
    (fun g ↦ by
      ext U : 2
      have h := ModuleCat.restrictScalarsTensorExtendScalarsIso_hom_naturality φ (g.app U)
        (𝟙 (P.obj U))
      rw [Functor.map_id, tensorHom_id, tensorHom_id] at h
      exact h)

end Presheaf

namespace Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} S))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} S)]

/-- Restriction of scalars of sheaves reflects isomorphisms. -/
instance reflectsIsomorphisms_restrictScalars : (restrictScalars J φ).ReflectsIsomorphisms where
  reflects {M N} g _ := by
    have : IsIso ((sheafToPresheaf J _).map g) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      have : IsIso ((ModuleCat.restrictScalars φ).map (((sheafToPresheaf J _).map g).app U)) :=
        inferInstanceAs (IsIso (((sheafToPresheaf J _).map ((restrictScalars J φ).map g)).app U))
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars φ)
    exact isIso_of_reflects_iso _ (sheafToPresheaf J _)

/-- Tensoring with the sheafification of a presheaf `P` is computed by tensoring the underlying
presheaves with `P` and sheafifying. -/
noncomputable def tensorRightPresheafToSheafObjIso (P : Cᵒᵖ ⥤ ModuleCat.{u + 1} S) :
    tensorRight ((presheafToSheaf J _).obj P) ≅
      sheafToPresheaf J _ ⋙ tensorRight P ⋙ presheafToSheaf J _ :=
  (tensorRight _).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} S)).counit).symm
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J _) (presheafToSheafCompTensorRightIso P)

/-- **Extension of scalars and tensor products.** For sheaves `M` of `S`-modules and `N` of
`R`-modules, the sheaf `M ⊗ (S ⊗_R N)` with scalars restricted to `R` is `M ⊗ N`, naturally in
`M`. -/
noncomputable def tensorRightExtendScalarsCompRestrictScalarsIso
    (N : Sheaf J (ModuleCat.{u + 1} R)) :
    tensorRight ((Sheaf.composeAndSheafify J
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj N) ⋙ restrictScalars J φ ≅
      restrictScalars J φ ⋙ tensorRight N :=
  haveI : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
    preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} S) := inferInstance
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} R) := inferInstance
  let ιS := sheafToPresheaf J (ModuleCat.{u + 1} S)
  let ιR := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let aS := presheafToSheaf J (ModuleCat.{u + 1} S)
  let aR := presheafToSheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} φ)
  let P := N.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ
  Functor.isoWhiskerRight (tensorRightPresheafToSheafObjIso J P) (restrictScalars J φ) ≪≫
    Functor.associator ιS (tensorRight P ⋙ aS) (restrictScalars J φ) ≪≫
    Functor.isoWhiskerLeft ιS (Functor.associator (tensorRight P) aS (restrictScalars J φ)) ≪≫
    Functor.isoWhiskerLeft ιS (Functor.isoWhiskerLeft (tensorRight P)
      (sheafComposeNatIso J (ModuleCat.restrictScalars φ)
        (sheafificationAdjunction J (ModuleCat.{u + 1} S))
        (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
    Functor.isoWhiskerLeft ιS (Functor.associator (tensorRight P) W aR).symm ≪≫
    Functor.isoWhiskerLeft ιS (Functor.isoWhiskerRight
      (Presheaf.tensorRightExtendScalarsCompRestrictScalarsIso φ N.obj) aR) ≪≫
    Functor.isoWhiskerLeft ιS (Functor.associator W (tensorRight N.obj) aR) ≪≫
    (Functor.associator ιS W (tensorRight N.obj ⋙ aR)).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (restrictScalars J φ ⋙ ιR)) _ ≪≫
    Functor.associator (restrictScalars J φ) ιR (tensorRight N.obj ⋙ aR) ≪≫
    Functor.isoWhiskerLeft (restrictScalars J φ) (tensorRightIso N).symm

omit [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} S))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} S)] in
/-- **Extension of scalars preserves flat sheaves.** For a flat sheaf `N` of `R`-modules, the
sheaf `S ⊗_R N` of `S`-modules is flat: with scalars restricted to `R`, tensoring with it is
tensoring with `N` (`CategoryTheory.Sheaf.tensorRightExtendScalarsCompRestrictScalarsIso`),
which is exact, and restriction of scalars is exact and reflects isomorphisms. -/
theorem flat_extendScalars_obj {N : Sheaf J (ModuleCat.{u + 1} R)} (hN : ObjectProperty.flat N) :
    ObjectProperty.flat ((Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj N) := by
  have := hN.tensorRight.preservesFiniteLimits
  have := hN.tensorRight.preservesFiniteColimits
  have : PreservesFiniteLimits (tensorRight ((Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj N) ⋙ restrictScalars J φ) :=
    preservesFiniteLimits_of_natIso (tensorRightExtendScalarsCompRestrictScalarsIso J φ N).symm
  have : PreservesFiniteColimits (tensorRight ((Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj N) ⋙ restrictScalars J φ) :=
    preservesFiniteColimits_of_natIso (tensorRightExtendScalarsCompRestrictScalarsIso J φ N).symm
  have : PreservesFiniteLimits (tensorRight ((Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj N)) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (restrictScalars J φ)
  have : PreservesFiniteColimits (tensorRight ((Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj N)) :=
    preservesFiniteColimits_of_reflects_of_preserves _ (restrictScalars J φ)
  refine ⟨(exactFunctor_iff _).2
    ⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _).symm,
      preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _).symm⟩,
    (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩

end Sheaf

end CategoryTheory
