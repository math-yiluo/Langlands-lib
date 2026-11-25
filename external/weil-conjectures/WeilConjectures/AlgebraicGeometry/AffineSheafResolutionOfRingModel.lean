/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.CategoryTheory.Preadditive.LeftExact

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

/-- Sheafification transfers an actual finite-free ring resolution to an affine scheme.
Source: Stacks Project, Tag 01IB (affine equivalence), and Tag 01HV (exactness of tilde).
(blueprint: lem-pc-affine-sheaf-resolution-from-ring-model).

Proof: Identify the affine scheme with the spectrum of its global section ring via its
canonical affine isomorphism. Transport the tilde/global-sections adjunction across this
isomorphism. Apply tilde termwise to P and to f. Localization of modules is exact, so
sheafification is exact and sends f to a quasi-isomorphism. Since every term of C is
quasi-coherent, the counit from the sheafified global-sections complex to C is a termwise
isomorphism; its naturality makes it an isomorphism of complexes. Compose with that
counit to obtain the required map. The zero-preserving tilde functor preserves the
termwise upper bound. For each term of P choose a finite basis, enumerate it by Fin r,
and lift its index universe by ULift. Tilde carries the resulting free-module isomorphism
to an isomorphism with the free sheaf on ULift (Fin r). These choices occur only within
this existential proof, not in a definition. The zero ring and empty affine scheme
produce zero sheaves, so rank zero works in those cases. -/
theorem exists_affine_sheaf_resolution_of_ring_model
    {T : Scheme.{u}} (U : T.Opens) [IsAffine U.toScheme]
    (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (P : CochainComplex (ModuleCat.{u}
        (U.toScheme.ringCatSheaf.obj.obj (.op ⊤))) ℤ)
    (hP : P.IsStrictlyLE d)
    (hfree : ∀ i : ℤ, Module.Free (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) (P.X i) ∧
      Module.Finite (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) (P.X i))
    (f : P ⟶ ((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf
      (.op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    [QuasiIso f] :
    ∃ Q : CochainComplex U.toScheme.Modules ℤ, Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ, Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      ∃ e : Q ⟶ C, QuasiIso e := by
  classical
  let X := U.toScheme
  let A := Γ(X, ⊤)
  let R := restrictFunctor X.toSpecΓ
  let F := tilde.functor Γ(X, ⊤) ⋙ R
  let G := SheafOfModules.evaluation.{u} X.ringCatSheaf (.op ⊤)
  let : G.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  let : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N),
      PreservesLimit (parallelPair g 0) (tilde.functor Γ(X, ⊤)) :=
    fun {_ _} g ↦ tilde_preservesKernel A g
  let : PreservesFiniteLimits (tilde.functor Γ(X, ⊤)) :=
    Functor.preservesFiniteLimits_of_preservesKernels _
  let : PreservesFiniteLimits R := by
    change PreservesFiniteLimits (restrictFunctor X.toSpecΓ)
    infer_instance
  let : PreservesFiniteColimits R := by
    change PreservesFiniteColimits (restrictFunctor X.toSpecΓ)
    infer_instance
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  let Q : CochainComplex X.Modules ℤ := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hQ : Q.IsStrictlyLE d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact F.map_isZero ((CochainComplex.isStrictlyLE_iff P d).mp hP n hn)
  have hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := X.ringCatSheaf) (ULift.{u} (Fin r))) := by
    intro n
    let : Module.Free A (P.X n) := (hfree n).1
    let : Module.Finite A (P.X n) := (hfree n).2
    let I := Module.Free.ChooseBasisIndex A (P.X n)
    let b := Module.Free.chooseBasis A (P.X n)
    let v : I ≃ ULift.{u} (Fin (Fintype.card I)) :=
      (Fintype.equivFin I).trans Equiv.ulift.symm
    let c := (b.reindex v).repr.toModuleIso
    refine ⟨Fintype.card I, ⟨?_⟩⟩
    exact R.mapIso ((tilde.functor Γ(X, ⊤)).mapIso c ≪≫
        tildeFinsupp (ULift.{u} (Fin (Fintype.card I)))) ≪≫
      (SheafOfModules.mapFreeIso R (ULift.{u} (Fin (Fintype.card I)))
        (restrictUnitIso X.toSpecΓ).symm).symm
  obtain ⟨ε, hε⟩ := exists_affineChart_counit X
  let q : (F.mapHomologicalComplex (.up ℤ)).obj
      ((G.mapHomologicalComplex (.up ℤ)).obj C) ⟶ C :=
    { f n := ε.app (C.X n)
      comm' i j hij := (ε.naturality (C.d i j)).symm }
  have : ∀ n : ℤ, IsIso (q.f n) := fun n ↦ hε (C.X n) (hCqc n)
  have : IsIso q := HomologicalComplex.Hom.isIso_of_components q
  let e := (F.mapHomologicalComplex (.up ℤ)).map f ≫ q
  exact ⟨Q, hQ, hQfree, e, by dsimp [e]; infer_instance⟩

end AlgebraicGeometry.Scheme.Modules
