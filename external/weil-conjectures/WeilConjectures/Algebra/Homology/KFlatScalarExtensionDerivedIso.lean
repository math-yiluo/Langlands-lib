/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Scalar extension homology is invariant among K-flat derived models

Source: Stacks Project, More on Algebra, Tags 064L and 06Y0.
(blueprint: lem-sc-kflat-scalar-extension-derived-iso).
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CochainComplex

private theorem kFlat_of_acyclic_tensor
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (mapBifunctor L P (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (mapBifunctor N P (curriedTensor _))).2 (hP N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr


private theorem scalarExtension_quasiIso_of_kFlat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (a : P ⟶ Q)
    (ha : QuasiIso a)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat Q) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map a) := by
  let N := (HomologicalComplex.single (ModuleCat.{u} S) (.up ℤ) 0).obj (𝟙_ (ModuleCat S))
  let F := (ModuleCat.mixedTensor f).flip
  have h := (mixedTensor_kFlat_quasiIso f).1 N P Q a ha hP hQ
  let unit : (ModuleCat.mixedTensor f).obj (𝟙_ (ModuleCat S)) ≅
      ModuleCat.extendScalars f :=
    isoWhiskerLeft (ModuleCat.extendScalars f) (leftUnitorNatIso (ModuleCat S)) ≪≫
      Functor.rightUnitor _
  let e (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      ((F.map₂CochainComplex).obj K).obj N ≅
        ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K :=
    mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) K ≪≫
      (NatIso.mapHomologicalComplex unit (.up ℤ)).app K
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e P) (e Q) (by
      change (e P).hom ≫ _ = _ ≫ (e Q).hom
      change ((mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) P).hom ≫
        ((NatIso.mapHomologicalComplex unit (.up ℤ)).app P).hom) ≫ _ =
        HomologicalComplex.mapBifunctorMap a (𝟙 N) F (.up ℤ) ≫
          ((mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) Q).hom ≫
            ((NatIso.mapHomologicalComplex unit (.up ℤ)).app Q).hom)
      rw [← Category.assoc, mapBifunctorSingle₂Iso_hom_naturality]
      simp only [Category.assoc]
      exact congrArg (fun t ↦ (mapBifunctorSingle₂Iso F (𝟙_ (ModuleCat S)) P).hom ≫ t)
        ((NatIso.mapHomologicalComplex unit (.up ℤ)).hom.naturality a).symm))).1 h

/-- Termwise scalar extension of K-flat models respects derived isomorphisms.
Source: Stacks Project, More on Algebra, Tags 064L and 06Y0.
(blueprint: lem-sc-kflat-scalar-extension-derived-iso).

Proof: Represent e by a roof P <- L -> Q, with the left leg a quasi-isomorphism.
Since e is invertible, its right leg is also a quasi-isomorphism: apply Q to both
legs, use the roof equality and invertibility of e, and reflect quasi-isomorphisms
through Q. Replace L by a K-flat resolution L' -> L. Both composites are then
quasi-isomorphisms between K-flat complexes. Extension of scalars along f preserves
such quasi-isomorphisms (Tag 064L): its cone is acyclic and K-flat, and its tensor
with S is acyclic by replacing S with a K-flat resolution and using K-flatness in
both factors. This also follows from mixed total tensor with the complex S in
degree zero, whose total complex is termwise extension of scalars. The two tensor
legs therefore induce invertible S-linear homology maps. Compose the inverse of
the left homology map with the right one. This proves existence independently of
the selected roof. The hypotheses impose no upper or lower bound and no flatness
on S over R. Zero complexes, identity maps and zero coefficient rings satisfy the
same argument. Only the source derived category is needed, so its morphism universe
can differ from that used for sheaves. -/
theorem nonempty_kFlat_scalarExtension_homology_linearEquiv
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic)
    (hQ : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (mapBifunctor L Q (MonoidalCategory.curriedTensor _)).Acyclic)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    Nonempty ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P).homology i
      ≃ₗ[S]
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q).homology i) :=
  by
    classical
    have (M : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
        ((curriedTensor (ModuleCat.{u} R)).flip.obj M) :=
      inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight M))
    have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
        (AsSmall.equiv (C := ℤ)).symm
    obtain ⟨L, s, hs, t, he⟩ := DerivedCategory.right_fac e.hom
    have : IsIso (DerivedCategory.Q.map s) := hs
    have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
    have ht : IsIso (DerivedCategory.Q.map t) := by
      have he' : DerivedCategory.Q.map t = DerivedCategory.Q.map s ≫ e.hom := by
        rw [he, IsIso.hom_inv_id_assoc]
      rw [he']
      infer_instance
    have ht' : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 ht
    let Λ := (Classical.choice (inferInstance :
      Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
    let L' := Λ.resolutionFunctor.obj L
    let r := Λ.resolutionNatTrans.app L
    have hr : QuasiIso r := inferInstance
    have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le L
    have : QuasiIso s := hs'
    have : QuasiIso t := ht'
    have : QuasiIso r := hr
    have hsr : QuasiIso (r ≫ s) := inferInstance
    have htr : QuasiIso (r ≫ t) := inferInstance
    let C := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
    have : QuasiIso (C.map (r ≫ s)) :=
      scalarExtension_quasiIso_of_kFlat f (r ≫ s) hsr hk (kFlat_of_acyclic_tensor P hP)
    have : QuasiIso (C.map (r ≫ t)) :=
      scalarExtension_quasiIso_of_kFlat f (r ≫ t) htr hk (kFlat_of_acyclic_tensor Q hQ)
    let left : (C.obj L').homology i ≅ (C.obj P).homology i :=
      asIso (HomologicalComplex.homologyMap (C.map (r ≫ s)) i)
    let right : (C.obj L').homology i ≅ (C.obj Q).homology i :=
      asIso (HomologicalComplex.homologyMap (C.map (r ≫ t)) i)
    exact ⟨(left.symm ≪≫ right).toLinearEquiv⟩

end CochainComplex
