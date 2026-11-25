/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.Projective
import WeilConjectures.AlgebraicGeometry.AffineAssociatedModuleFlatOver
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Sheafifying a finite-projective comparison with affine sections

Source: Stacks Project, Tags 01IB and 08EB.
(blueprint: lem-pc-affine-projective-sections-sheafification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

-- Generalize kernel preservation to the exactness interface needed below.
private theorem tilde_preservesFiniteLimits (A : Type u) [CommRing A] :
    PreservesFiniteLimits (tilde.functor (.of A)) := by
  let : (tilde.functor (.of A)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ tilde.map_zero⟩
  let : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (tilde.functor (.of A)) := by
    intro M N f
    let T := tilde.functor (.of (A : Type u))
    let ff : T.FullyFaithful :=
      tilde.fullyFaithfulFunctor (R := .of (A : Type u))
    let : T.Full := ff.full
    let : T.Faithful := ff.faithful
    let : T.IsLeftAdjoint :=
      (tilde.adjunction (R := .of (A : Type u))).isLeftAdjoint
    let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
    have : (T.obj M).IsQuasicoherent := by
      change (tilde.{u} (R := .of (A : Type u)) M).IsQuasicoherent
      infer_instance
    have : (T.obj N).IsQuasicoherent := by
      change (tilde.{u} (R := .of (A : Type u)) N).IsQuasicoherent
      infer_instance
    let k := Limits.kernel (T.map f)
    have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of (A : Type u)) k) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
        (R := .of (A : Type u)) k
    let e : T.obj ((moduleSpecΓFunctor
        (R := .of (A : Type u))).obj k) ≅ k :=
      asIso (Scheme.Modules.fromTildeΓ (R := .of (A : Type u)) k)
    let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map f))
    have ht : t ≫ f = 0 := by
      apply T.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
        Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
    let c := Limits.KernelFork.ofι t ht
    have hc : Limits.IsLimit (c.map T) := by
      apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map f))
      exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
    have hc' : Limits.IsLimit c :=
      Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
    exact Limits.preservesLimit_of_preserves_limit_cone hc'
      ((c.isLimitMapConeEquiv T).symm hc)
  exact Functor.preservesFiniteLimits_of_preservesKernels _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def affineSectionsIso (Y : Scheme.{u}) [IsAffine Y] :
    restrictFunctor (isAffineOpen_top Y).fromSpec ⋙ moduleSpecΓFunctor ≅
      SheafOfModules.evaluation.{u} Y.ringCatSheaf (op ⊤) :=
  NatIso.ofComponents
    (fun M ↦ (sectionsRestrictFromSpecLinearEquiv M (isAffineOpen_top Y)).toModuleIso)
    (by
      intro M N f
      ext m
      dsimp only [sectionsRestrictFromSpecLinearEquiv, LinearEquiv.toModuleIso,
        ModuleCat.hom_comp, LinearMap.comp_apply]
      change N.presheaf.map (homOfLE _).op
          (f.val.app _ ((M.restrictAppIso _ ⊤).hom m)) =
        f.val.app _ (M.presheaf.map (homOfLE _).op ((M.restrictAppIso _ ⊤).hom m))
      exact (ConcreteCategory.congr_hom (f.mapPresheaf.naturality _) _).symm)

-- Compare section scalar actions before introducing the homological complex.
private theorem affine_restrictTilde_flat (Y : Scheme.{u}) [IsAffine Y]
    (M : ModuleCat.{u} Γ(Y, ⊤)) [Module.Projective Γ(Y, ⊤) M] :
    ((restrictFunctor Y.isoSpec.hom).obj ((tilde.functor Γ(Y, ⊤)).obj M)).IsFlatOver
      (𝟙 Y) := by
  have hflat := flatOver_affineAssociatedModule Y M
    (inferInstance : Module.Flat Γ(Y, ⊤) M)
  let e := (restrictFunctorIsoPullback Y.isoSpec.hom).app
    ((tilde.functor Γ(Y, ⊤)).obj M)
  intro V U hUV
  let : Module Γ(Y, V.1)
      Γ((restrictFunctor Y.isoSpec.hom).obj ((tilde.functor Γ(Y, ⊤)).obj M), U.1) :=
    Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V.1 U.1 hUV).hom
  let : Module Γ(Y, V.1)
      Γ((pullback Y.isoSpec.hom).obj ((tilde.functor Γ(Y, ⊤)).obj M), U.1) :=
    Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V.1 U.1 hUV).hom
  let a := (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).mapIso e
  let e' :
      Γ((restrictFunctor Y.isoSpec.hom).obj ((tilde.functor Γ(Y, ⊤)).obj M), U.1) ≃ₗ[Γ(Y, V.1)]
      Γ((pullback Y.isoSpec.hom).obj ((tilde.functor Γ(Y, ⊤)).obj M), U.1) :=
    { a.toLinearEquiv.toAddEquiv with
      map_smul' := fun r m ↦ a.hom.hom.map_smul _ _ }
  have : Module.Flat Γ(Y, V.1)
      Γ((pullback Y.isoSpec.hom).obj ((tilde.functor Γ(Y, ⊤)).obj M), U.1) :=
    hflat V U hUV
  exact Module.Flat.of_linearEquiv e'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The chart and section scalar actions require additional definitional-equality checks.
/-- Sheafification of a ring quasi-isomorphism to the sections of a quasi-coherent
complex supplies a quasi-isomorphism to that complex; finite projective terms give
flat, quasi-coherent and finitely presented sheaves.
Source: Stacks Project, Tag 01IB (schemes-lemma-spec-sheaves), and Tag 08EB.
(blueprint: lem-pc-affine-projective-sections-sheafification).

Proof: Use the explicit functor tilde followed by restriction along Y.isoSpec.hom.
The affine tilde functor is exact and thus preserves quasi-isomorphisms. Its counit
on every term of D is invertible because that term is quasi-coherent; naturality
makes these counits a chain isomorphism from the sheafified section complex to D.
Compose this chain isomorphism with the sheafification of q. Each finite projective
module P.X n is a retract of a finite free module. Tilde and restriction preserve
the retraction and finite sums, giving a retract of a finite free structure-module
on Y. Such a retract is quasi-coherent and finitely presented. On an affine open U
its sections are finite projective over Gamma(U,O), hence flat. For affine U inside
affine V, Gamma(U,O) is flat over Gamma(V,O) by flatness of open immersions.
Transitivity of flatness gives exactly the sectionwise IsFlatOver identity predicate,
with its restriction-of-scalars action. These arguments include rank zero and the zero ring.
No boundedness or perfectness is assumed in this sheafification step. -/
theorem affine_projective_sections_sheafification
    (Y : Scheme.{u}) [IsAffine Y]
    (D : CochainComplex Y.Modules ℤ)
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (P : CochainComplex (ModuleCat.{u} (Γ(Y, ⊤) : Type u)) ℤ)
    (hfinite : ∀ n : ℤ, Module.Finite (Γ(Y, ⊤) : Type u) (P.X n))
    (hprojective : ∀ n : ℤ, Module.Projective (Γ(Y, ⊤) : Type u) (P.X n))
    (q : P ⟶ ((@Functor.mapHomologicalComplex ℤ Y.Modules
      (ModuleCat.{u} (Γ(Y, ⊤) : Type u)) _ _ _ _
      (SheafOfModules.evaluation.{u} Y.ringCatSheaf (op ⊤))
      ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)).obj D))
    (hq : QuasiIso q) :
    let C := ((tilde.functor Γ(Y, ⊤) ⋙ restrictFunctor Y.isoSpec.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P
    (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 Y)) ∧
    (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
    (∀ n : ℤ, (C.X n).IsFinitePresentation) ∧
    ∃ e : C ⟶ D, QuasiIso e := by
  let F := tilde.functor Γ(Y, ⊤) ⋙ restrictFunctor Y.isoSpec.hom
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have := hprojective n
    exact affine_restrictTilde_flat Y (P.X n)
  · intro n
    change ((restrictFunctor Y.isoSpec.hom).obj
      ((tilde.functor Γ(Y, ⊤)).obj (P.X n))).IsQuasicoherent
    have : ((tilde.functor Γ(Y, ⊤)).obj (P.X n)).IsQuasicoherent := by
      change (tilde.{u} (P.X n)).IsQuasicoherent
      infer_instance
    exact isQuasicoherent_restrictFunctor _ _
  · intro n
    have := hfinite n
    have := hprojective n
    have hp := Module.finitePresentation_of_projective Γ(Y, ⊤) (P.X n)
    obtain ⟨s, hs, t, ht⟩ := hp.out
    let pres := presentationTilde (P.X n) (s : Set (P.X n)) hs (t : Set _) ht
    have : pres.IsFinite :=
      { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set (P.X n)))⟩
        isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ Γ(Y, ⊤))))⟩ }
    have : ((tilde.functor Γ(Y, ⊤)).obj (P.X n)).IsFinitePresentation :=
      pres.isFinitePresentation
    change ((restrictFunctor Y.isoSpec.hom).obj
      ((tilde.functor Γ(Y, ⊤)).obj (P.X n))).IsFinitePresentation
    infer_instance
  · have : PreservesFiniteLimits (tilde.functor Γ(Y, ⊤)) :=
      tilde_preservesFiniteLimits (Γ(Y, ⊤) : Type u)
    have : QuasiIso q := hq
    have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
      infer_instance
    let E := SheafOfModules.evaluation.{u} Y.ringCatSheaf (op ⊤)
    let : E.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    let B := restrictFunctor Y.isoSpec.inv
    let R := restrictFunctor Y.isoSpec.hom
    let α : E ≅ B ⋙ moduleSpecΓFunctor := by
      simpa only [IsAffineOpen.fromSpec_top] using (affineSectionsIso Y).symm
    let γ : B ⋙ R ≅ 𝟭 Y.Modules :=
      (restrictFunctorComp Y.isoSpec.hom Y.isoSpec.inv).symm ≪≫
        restrictFunctorCongr Y.isoSpec.hom_inv_id ≪≫ restrictFunctorId
    let ε : E ⋙ F ⟶ 𝟭 Y.Modules :=
      Functor.whiskerRight α.hom F ≫
        Functor.whiskerLeft B (Functor.whiskerRight
          (fromTildeΓNatTrans (R := Γ(Y, ⊤))) R) ≫ γ.hom
    let : (𝟭 Y.Modules).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    let c : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj D) ⟶ D :=
      (ε.mapHomologicalComplex (ComplexShape.up ℤ)).app D ≫
        (Functor.mapHomologicalComplexIdIso Y.Modules (ComplexShape.up ℤ)).hom.app D
    have hε (n : ℤ) : IsIso (ε.app (D.X n)) := by
      have := hDqc n
      have : (B.obj (D.X n)).IsQuasicoherent := isQuasicoherent_restrictFunctor _ _
      have : IsIso (fromTildeΓ (B.obj (D.X n))) :=
        isIso_fromTildeΓ_of_isQuasicoherent _
      have : IsIso (F.map (α.hom.app (D.X n))) := inferInstance
      have : IsIso (R.map (fromTildeΓNatTrans.app (B.obj (D.X n)))) := by
        change IsIso (R.map (fromTildeΓ (B.obj (D.X n))))
        infer_instance
      change IsIso (F.map (α.hom.app (D.X n)) ≫
        R.map (fromTildeΓNatTrans.app (B.obj (D.X n))) ≫ γ.hom.app (D.X n))
      infer_instance
    have : IsIso c := by
      let : ∀ n : ℤ, IsIso (c.f n) := fun n ↦ by
        change IsIso (ε.app (D.X n) ≫ 𝟙 _)
        have := hε n
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components c
    exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ c, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
