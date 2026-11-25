/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

import WeilConjectures.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine derived unit induces an isomorphism on every cohomology object.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, module-unit calculation.
(blueprint: new-affine-derived-unit-homology-isIso).

Proof: The quasi-coherent kernel of a map of associated sheaves has an invertible
ordinary counit. Lift its kernel fork through fully faithful tilde and reflect
its limit property, proving exactness of tilde. Form the canonical adjunction
between derived tilde and right-derived affine sections. On Qh(K), its unit
factors through the canonical sections comparison, which is invertible by
affineTildeDerivedSectionsUnit_isIso. Cancel the exact-functor comparison and
use essential surjectivity of Qh and naturality to obtain an invertible unit
on every derived module. Descend hF through Q and restrict this adjunction along
the fully faithful inclusion of D_QCoh, using hG. The restriction unit formula
and uniqueness of right adjoints transport invertibility to the given adjunction.
Homology preserves that isomorphism, in every integer degree. The argument
includes arbitrary unbounded complexes, the zero ring and the zero complex.
-/
theorem affineDerivedUnit_homology_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A))
    (adj : F ⊣ G)
    (hF : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q))
    (hG : Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor))
    (M : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      (adj.unit.app M)) := by
  let T : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
    tilde.functor (.of A)
  let S := RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom
  let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let : ∀ {P Q : ModuleCat.{u} A} (f : P ⟶ Q),
      Limits.PreservesLimit (Limits.parallelPair f 0) T := by
    intro M N f
    let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
    let : T.Full := ff.full
    let : T.Faithful := ff.faithful
    have : (T.obj M).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) M).IsQuasicoherent
      infer_instance
    have : (T.obj N).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) N).IsQuasicoherent
      infer_instance
    let k := Limits.kernel (T.map f)
    have : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
    let e : T.obj ((moduleSpecΓFunctor (R := .of A)).obj k) ≅ k :=
      asIso (Scheme.Modules.fromTildeΓ (R := .of A) k)
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
  let : Limits.PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesKernels T
  have : S.Additive := by
    dsimp only [S]
    infer_instance
  let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
  let : T.Full := ff.full
  let : T.Faithful := ff.faithful
  let b : T ⊣ S := tilde.adjunction (R := .of A)
  let a := b.mapDerivedCategoryRightDerivedAdjunction
  have hu (K : HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ)) :
      IsIso (a.unit.app (DerivedCategory.Qh.obj K)) := by
    have hr := affineTildeDerivedSectionsUnit_isIso A K
    have hfac := (b.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
        (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
        T.mapDerivedCategoryFactorsh.hom S.rightDerivedFunctorUnit K
    change a.unit.app (DerivedCategory.Qh.obj K) ≫
      S.rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.hom.app K) =
        DerivedCategory.Qh.map
          ((b.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K) ≫
          S.rightDerivedFunctorUnit.app ((T.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
      at hfac
    exact IsIso.of_isIso_fac_right hfac
  have hunit (P : DerivedCategory (ModuleCat.{u} A)) : IsIso (a.unit.app P) := by
    let e := DerivedCategory.Qh.objObjPreimageIso P
    have := hu (DerivedCategory.Qh.objPreimage P)
    exact IsIso.of_isIso_fac_left (a.unit.naturality e.hom)
  obtain ⟨α⟩ := hF
  let ι := (schemeDerivedQCohProperty (Spec (.of A))).ι
  let eF : F ⋙ ι ≅ T.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (DerivedCategory.Q ⋙ F ⋙ ι)
      (T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F ⋙ ι) T.mapDerivedCategory α
  obtain ⟨eG⟩ := hG
  let a' : F ⊣ G := a.restrictFullyFaithful
    (Functor.FullyFaithful.id _) (Functor.FullyFaithful.ofFullyFaithful ι)
    ((Functor.leftUnitor _ ) ≪≫ eF.symm)
    (eG.symm ≪≫ (Functor.rightUnitor _).symm)
  have hu' : IsIso (a'.unit.app M) := by
    have := hunit M
    have h := a.map_restrictFullyFaithful_unit_app
      (Functor.FullyFaithful.id _) (Functor.FullyFaithful.ofFullyFaithful ι)
      ((Functor.leftUnitor _) ≪≫ eF.symm)
      (eG.symm ≪≫ (Functor.rightUnitor _).symm) M
    change a'.unit.app M = _ at h
    rw [h]
    infer_instance
  have : IsIso (adj.unit.app M) := by
    rw [← a'.unit_rightAdjointUniq_hom_app adj M]
    infer_instance
  infer_instance

end AlgebraicGeometry
