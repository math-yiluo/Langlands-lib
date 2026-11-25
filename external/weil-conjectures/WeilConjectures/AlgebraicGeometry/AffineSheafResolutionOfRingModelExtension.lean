/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModel


public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # Sheafifying an actual affine ring resolution -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem tilde_preservesKernel (A : Type u) [CommRing A]
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (tilde.functor (.of A)) := by
  let T := tilde.functor (.of A)
  let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
  let : T.Full := ff.full
  let : T.Faithful := ff.faithful
  let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  have : (T.obj M).IsQuasicoherent := by
    change (tilde.{u} (R := .of A) M).IsQuasicoherent
    infer_instance
  have : (T.obj N).IsQuasicoherent := by
    change (tilde.{u} (R := .of A) N).IsQuasicoherent
    infer_instance
  let k := kernel (T.map f)
  have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
  have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
  let e : T.obj ((moduleSpecΓFunctor (R := .of A)).obj k) ≅ k :=
    asIso (Scheme.Modules.fromTildeΓ (R := .of A) k)
  let t := T.preimage (e.hom ≫ kernel.ι (T.map f))
  have ht : t ≫ f = 0 := by
    apply T.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
      Category.assoc, kernel.condition, comp_zero, t]
  let c := KernelFork.ofι t ht
  have hc : IsLimit (c.map T) := by
    apply IsLimit.ofIsoLimit (kernelIsKernel (T.map f))
    exact Fork.ext e.symm (by simp [c, t, KernelFork.map])
  have hc' : IsLimit c :=
    isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
  exact preservesLimit_of_preserves_limit_cone hc'
    ((c.isLimitMapConeEquiv T).symm hc)

set_option backward.isDefEq.respectTransparency false in
private theorem pushforward_spec_smul (X : Scheme.{u}) (M : X.Modules)
    (a : Γ(X, ⊤)) (m : Γ((pushforward X.toSpecΓ).obj M, ⊤)) :
    a • (show (moduleSpecΓFunctor.obj ((pushforward X.toSpecΓ).obj M)) from m) =
      (a • (show Γ(M, ⊤) from m) : Γ(M, ⊤)) := by
  have h1 := congr(Hom.app
    $(pushforward_map_smulHom X.toSpecΓ M ((ΓSpecIso Γ(X, ⊤)).inv a)) ⊤ m)
  rw [pushforward_map_app, smulHom_app_apply] at h1
  refine h1.symm.trans ?_
  erw [smulHom_app_apply]
  have h2 : X.toSpecΓ.appTop ((ΓSpecIso Γ(X, ⊤)).inv a) = a := by
    rw [← CommRingCat.comp_apply, toSpecΓ_appTop, Iso.inv_hom_id]
    rfl
  rw [h2, show (homOfLE (le_top : X.toSpecΓ ⁻¹ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ ⊤)).op =
    𝟙 _ from Subsingleton.elim _ _]
  erw [CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem pushforward_toSpecΓ_isQuasicoherent
    (X : Scheme.{u}) [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward X.toSpecΓ).obj M).IsQuasicoherent := by
  let H := pushforward X.toSpecΓ
  let K := pushforward X.isoSpec.inv
  let S := restrictFunctor X.isoSpec.inv
  have he : X.toSpecΓ ≫ X.isoSpec.inv = 𝟙 X := X.toSpecΓ_isoSpec_inv
  let β₁ := pushforwardComp X.toSpecΓ X.isoSpec.inv
  let β₂ := pushforwardCongr he
  let β : H ⋙ K ≅ 𝟭 X.Modules := β₁ ≪≫ β₂ ≪≫ pushforwardId X
  let γ : H ≅ S :=
    (Functor.isoWhiskerLeft H (restrictFunctorAdjCounitIso X.isoSpec.inv)).symm ≪≫
      Functor.isoWhiskerRight β S ≪≫ Functor.leftUnitor S
  have hS : (S.obj M).IsQuasicoherent := by
    exact isQuasicoherent_restrictFunctor X.isoSpec.inv M
  exact
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (γ.app M).symm hS

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The associated-sheaf/global-sections counit is natural on any affine scheme,
and invertible on quasi-coherent modules.
Source: Stacks Project, Lemma 26.7.5 (Tag 01IB).
(blueprint: lem-pc-affine-sheaf-resolution-from-ring-model), proof step 1.

Proof: Push a module forward along X.toSpecΓ. Its global sections agree with the
original sections as Γ(X,⊤)-modules: the scalar action uses ΓSpecIso.inv followed
by X.toSpecΓ.appTop = ΓSpecIso.hom, whose composite is the identity. This gives a
natural isomorphism of global-section functors. Apply tilde to that isomorphism,
compose with the spectrum counit, and restrict back along X.toSpecΓ. The
restriction adjunction counit identifies the result with the original module.
Pushforward along this scheme isomorphism is naturally isomorphic to restriction
along its inverse and therefore preserves quasi-coherence. The spectrum counit
is invertible on a quasi-coherent module by Tag 01IB, so the composite is too.
The empty affine scheme and zero module satisfy the same argument. -/
private theorem exists_affineChart_counit (X : Scheme.{u}) [IsAffine X] :
    ∃ ε : SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤) ⋙
        (tilde.functor Γ(X, ⊤) ⋙ restrictFunctor X.toSpecΓ) ⟶ 𝟭 X.Modules,
      ∀ M : X.Modules, M.IsQuasicoherent → IsIso (ε.app M) := by
  classical
  let H := pushforward X.toSpecΓ
  let R := restrictFunctor X.toSpecΓ
  let α : SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤) ≅
      H ⋙ moduleSpecΓFunctor (R := Γ(X, ⊤)) :=
    NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
      (X₁ := (SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤)).obj M)
      (X₂ := moduleSpecΓFunctor.obj (H.obj M))
      { __ := AddEquiv.refl _
        map_smul' a m := (pushforward_spec_smul X M a m).symm })
      (by intro M N f; rfl)
  let ε : SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤) ⋙
      (tilde.functor Γ(X, ⊤) ⋙ R) ⟶ 𝟭 X.Modules :=
    Functor.whiskerRight α.hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft H
        (fromTildeΓNatTrans (R := Γ(X, ⊤)))) R ≫
      (restrictFunctorAdjCounitIso X.toSpecΓ).hom
  refine ⟨ε, ?_⟩
  intro M hM
  have : M.IsQuasicoherent := hM
  have : (H.obj M).IsQuasicoherent := pushforward_toSpecΓ_isQuasicoherent X M
  have h₁ : IsIso (α.hom.app M) := inferInstance
  have h₂ : IsIso ((fromTildeΓNatTrans (R := Γ(X, ⊤))).app (H.obj M)) := by
    exact isIso_fromTildeΓ_of_isQuasicoherent (H.obj M)
  have h₃ : IsIso ((restrictFunctorAdjCounitIso X.toSpecΓ).hom.app M) := inferInstance
  dsimp only [ε, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance



end AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Exact associated objects and the termwise affine counit compute global-section
homology, without claiming that global sections are exact on all sheaves. -/
noncomputable def sectionsHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (unit : 𝟭 C ≅ L ⋙ R) (ε : R ⋙ L ⟶ 𝟭 D)
    (K : CochainComplex D ℤ) (hε : ∀ n : ℤ, IsIso (ε.app (K.X n))) (n : ℤ) :
    ((R.mapHomologicalComplex (.up ℤ)).obj K).homology n ≅ R.obj (K.homology n) := by
  let H := (R.mapHomologicalComplex (.up ℤ)).obj K
  let q : (L.mapHomologicalComplex (.up ℤ)).obj H ⟶ K :=
    { f i := ε.app (K.X i)
      comm' i j hij := (ε.naturality (K.d i j)).symm }
  have : ∀ i : ℤ, IsIso (q.f i) := hε
  have : IsIso q := HomologicalComplex.Hom.isIso_of_components q
  let c : L.obj (H.homology n) ≅ K.homology n :=
    ((H.sc n).mapHomologyIso L).symm ≪≫
      (HomologicalComplex.homologyFunctor D (.up ℤ) n).mapIso (asIso q)
  exact unit.app (H.homology n) ≪≫ R.mapIso c


end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections commute with homology of a termwise quasi-coherent complex
on an affine scheme, via the exact associated-sheaf functor and its counit.
Source: Stacks Project, Tags 01IB and 01HV. -/
theorem nonempty_affineSectionsHomologyIso
    (X : Scheme.{u}) [IsAffine X] (K : CochainComplex X.Modules ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) (n : ℤ) :
    Nonempty ((((SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤)).mapHomologicalComplex
        (.up ℤ)).obj K).homology n ≅
      (SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤)).obj (K.homology n)) := by
  let A := Γ(X, ⊤)
  let T := tilde.functor A
  let R := restrictFunctor X.toSpecΓ
  let G := SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤)
  let F := T ⋙ R
  let H := pushforward X.toSpecΓ
  let α : G ≅ H ⋙ moduleSpecΓFunctor (R := A) :=
    NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
      (X₁ := G.obj M) (X₂ := moduleSpecΓFunctor.obj (H.obj M))
      { __ := AddEquiv.refl _
        map_smul' a m := (pushforward_spec_smul X M a m).symm })
      (by intro M N f; rfl)
  let adj : F ⊣ G :=
    ((tilde.adjunction (R := A)).comp (restrictAdjunction X.toSpecΓ)).ofNatIsoRight α.symm
  let E : (Spec A).Modules ≌ X.Modules := CategoryTheory.Equivalence.mk
    (restrictFunctor X.isoSpec.hom) (restrictFunctor X.isoSpec.inv)
    ((restrictFunctorComp X.isoSpec.inv X.isoSpec.hom).symm ≪≫
      restrictFunctorCongr X.isoSpec.inv_hom_id ≪≫ restrictFunctorId).symm
    ((restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm ≪≫
      restrictFunctorCongr X.isoSpec.hom_inv_id ≪≫ restrictFunctorId)
  let : R.Full := E.fullyFaithfulFunctor.full
  let : R.Faithful := E.fullyFaithfulFunctor.faithful
  let : T.IsLeftAdjoint := (tilde.adjunction (R := A)).isLeftAdjoint
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let : G.Additive := ⟨rfl⟩
  let : T.Full := (tilde.fullyFaithfulFunctor (R := A)).full
  let : T.Faithful := (tilde.fullyFaithfulFunctor (R := A)).faithful
  let : F.Additive := adj.left_adjoint_additive
  have : IsIso adj.unit := inferInstance
  have : PreservesFiniteLimits T := by
    let : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N),
        PreservesLimit (parallelPair f 0) T :=
      fun {_ _} f ↦ tilde_preservesKernel (A : Type u) f
    exact Functor.preservesFiniteLimits_of_preservesKernels _
  let : PreservesFiniteLimits R := by
    change PreservesFiniteLimits (restrictFunctor X.toSpecΓ)
    infer_instance
  let : PreservesFiniteColimits R := by
    change PreservesFiniteColimits (restrictFunctor X.toSpecΓ)
    infer_instance
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  let ε := Classical.choose (exists_affineChart_counit X)
  have hε := Classical.choose_spec (exists_affineChart_counit X)
  exact ⟨CategoryTheory.sectionsHomologyIso F G (asIso adj.unit) ε K (fun i ↦ hε _ (hqc i)) n⟩


end AlgebraicGeometry.Scheme.Modules
