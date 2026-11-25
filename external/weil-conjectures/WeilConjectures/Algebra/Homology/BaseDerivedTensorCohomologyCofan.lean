/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.DerivedModuleHomologyCoproduct
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Coproducts of universal base-derived tensor cohomology models

Source: Stacks Project, Tags 06Y6, 07D9 and 0DJA(1).
(blueprint: lem-pc-base-derived-tensor-cohomology-canonical-cofan). -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

/-- Derived scalar extension preserves coproducts by its derived adjunction.
Source: Stacks Project, Tag 06Y6, and the source library's derived adjunction. -/
private theorem derivedExtension_preservesCoproducts
    (R B : Type u) [CommRing R] [CommRing B] (f : R →+* B)
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) L := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  have (N : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  have : (extendScalars f).PreservesKFlatQuasiIso :=
    ⟨fun hK hN a ↦ CochainComplex.scalarExtension_quasiIso_of_kFlat f a
      (show QuasiIso a from inferInstance) hK hN⟩
  have : L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) := hL
  let e := Functor.leftDerivedNatIso (extendScalars f).leftDerivedFunctor L
    (extendScalars f).leftDerivedFunctorCounit ε
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  let adj := (extendRestrictScalarsAdj f).derivedAdjunction
  have : (extendScalars f).leftDerivedFunctor.IsLeftAdjoint := adj.isLeftAdjoint
  exact preservesColimitsOfShape_of_natIso e

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- Canonical model maps out of a complex coproduct give a cohomology coproduct
before any further extension of scalars.
Source: Stacks Project, Tags 06Y6, 07D9 and 0DJA(1).

Proof: restriction preserves the given complex coproduct. The derived direct-sum
lemma shows that Q preserves this coproduct, and quotientCompQhIso transports
it to the quotient followed by Qh. Scalar extension preserves quasi-isomorphisms
between K-flat complexes, by the existing mixed-tensor calculation with B in
degree zero. The source library's derived adjunction makes its standard total
left derived functor a left adjoint, hence coproduct-preserving. Uniqueness of
universal left derived functors transfers preservation to mS.derived. Apply this
functor to the restricted derived coproduct, then apply the derived homology
coproduct theorem. Each counit-compatible δ_j is the canonical natural
isomorphism by leftDerived_ext. Its naturality at s_j, followed by homology
and the equations hg, identifies the legs after transport through cohomologyIso.
This makes the B-module cofan colimiting. Restriction from A tensor_R B to B
preserves colimits and reflects isomorphisms, so it reflects this colimit.
No nonempty-index assumption, boundedness, or flatness of B is used.
(blueprint: lem-pc-base-derived-tensor-cohomology-canonical-cofan). -/
theorem baseDerivedTensorCohomology_canonical_cofan
    {I : Type u} (M : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (S : CochainComplex (ModuleCat.{u} A) ℤ) (s : ∀ j, M j ⟶ S)
    (hs : IsColimit (Cofan.mk S s))
    (m : ∀ j, BaseDerivedTensorCohomologyModel R A B (M j) C)
    (mS : BaseDerivedTensorCohomologyModel R A B S C) (i : ℤ)
    (δ : ∀ j, (m j).derived ⟶ mS.derived)
    (g : ∀ j, (m j).cohomology i ⟶ mS.cohomology i)
    (hδ : ∀ j, Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) (δ j) ≫
      mS.counit = (m j).counit)
    (hg : ∀ j, (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map (g j) ≫
          (mS.cohomologyIso i).hom =
      ((m j).cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          ((m j).derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex
                (.up ℤ)).map (s j))))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          ((δ j).app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj S))))) :
    Nonempty (IsColimit (Cofan.mk (mS.cohomology i) g)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  let F := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
  let K := fun j ↦ F.obj (M j)
  let T := F.obj S
  let t := fun j ↦ F.map (s j)
  have ht : IsColimit (Cofan.mk T t) :=
    isColimitCofanMkObjOfIsColimit F M s hs
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  have : PreservesColimit (Discrete.functor K) Q := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    exact (Cofan.isColimitMapCoconeEquiv Q K _).symm
      (derivedModuleDirectSums R _ K).some
  have : PreservesColimit (Discrete.functor K) q :=
    preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso _).symm
  have hq : IsColimit (Cofan.mk (q.obj T) (fun j ↦ q.map (t j))) :=
    isColimitCofanMkObjOfIsColimit q K t ht
  let L := mS.derived
  have : PreservesColimitsOfShape (Discrete I) L :=
    derivedExtension_preservesCoproducts R B (algebraMap R B) L mS.counit mS.universal I
  have hL : IsColimit (Cofan.mk (L.obj (q.obj T))
      (fun j ↦ L.map (q.map (t j)))) :=
    isColimitCofanMkObjOfIsColimit L _ _ hq
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let d := Cofan.mk (H.obj (L.obj (q.obj T)))
    (fun j ↦ H.map (L.map (q.map (t j))))
  have hd : IsColimit d :=
    (AlgebraicGeometry.derivedModuleHomology_coproduct B i I _ _ _ hL).some
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
  have : mS.derived.IsLeftDerivedFunctor mS.counit W := mS.universal
  have hδiso (j : I) : IsIso (δ j) := by
    have : (m j).derived.IsLeftDerivedFunctor (m j).counit W := (m j).universal
    let e := Functor.leftDerivedNatIso (m j).derived mS.derived
      (m j).counit mS.counit W (Iso.refl _)
    have he : δ j = e.hom := by
      apply Functor.leftDerived_ext mS.derived mS.counit W
      rw [hδ j]
      simp only [e, Functor.leftDerivedNatIso_hom, Functor.leftDerivedNatTrans_fac,
        Iso.refl_hom, Category.comp_id]
    rw [he]
    infer_instance
  have (j : I) : IsIso ((δ j).app (q.obj (K j))) := by
    have := hδiso j
    infer_instance
  let U := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let a : Discrete.functor (fun j ↦ U.obj ((m j).cohomology i)) ≅
      Discrete.functor (fun j ↦ H.obj (L.obj (q.obj (K j)))) :=
    Discrete.natIso (fun j ↦ (m j.as).cohomologyIso i ≪≫
      H.mapIso (asIso ((δ j.as).app (q.obj (K j.as)))))
  have ha : IsColimit ((Cocone.precompose a.hom).obj d) :=
    (IsColimit.precomposeHomEquiv a d).symm hd
  have hcomm (j : I) :
      (a.app ⟨j⟩).hom ≫ H.map (L.map (q.map (t j))) =
        U.map (g j) ≫ (mS.cohomologyIso i).hom := by
    have hn := congrArg H.map ((δ j).naturality (q.map (t j)))
    simp only [Functor.map_comp] at hn
    change (((m j).cohomologyIso i).hom ≫ H.map ((δ j).app (q.obj (K j)))) ≫
      H.map (L.map (q.map (t j))) = _
    rw [Category.assoc, ← hn, ← Category.assoc]
    exact (hg j).symm
  have hU : IsColimit (Cofan.mk (U.obj (mS.cohomology i))
      (fun j ↦ U.map (g j))) := by
    apply IsColimit.ofIsoColimit ha
    refine Cocone.ext (mS.cohomologyIso i).symm ?_
    intro j
    change (a.app j).hom ≫ H.map (L.map (q.map (t j.as))) ≫
      (mS.cohomologyIso i).inv = U.map (g j.as)
    rw [← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : ReflectsColimit (Discrete.functor (fun j ↦ (m j).cohomology i)) U :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact ⟨isColimitOfIsColimitCofanMkObj U _ g hU⟩

end ModuleCat
