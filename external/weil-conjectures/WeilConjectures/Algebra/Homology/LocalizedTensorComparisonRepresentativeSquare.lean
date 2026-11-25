/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Transport of tensor comparison squares between K-flat representatives

Source: Stacks Project, Tags 0DJA(1), 064L, 06Y1 and 06Y6.

(blueprint: lem-pc-localized-tensor-comparison-representative-square)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Limits
open CategoryTheory.Functor
open CochainComplex

namespace ModuleCat

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

private theorem acyclic_tensor_of_kFlat
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.Acyclic) :
    (mapBifunctor L P (curriedTensor _)).Acyclic := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hP
  have hL' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hL
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (mapBifunctor L P (curriedTensor _))).1 (hP _ hL').2

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

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The localized tensor comparison square is invariant under a derived isomorphism.

Source: Stacks Project, Tags 0DJA(1) and 0BYJ, invariance of derived tensor
products under change of K-flat representative.

Proof: represent the given derived isomorphism by a roof and replace its apex
by an A-K-flat resolution. Both roof legs are quasi-isomorphisms between
K-flat complexes. Tensor with Q preserves those quasi-isomorphisms. Apply
universality of the R-to-B derived tensor counits and cohomology to obtain
isomorphisms of the base-derived models. Naturality for multiplication by a
in A makes these B-linear isomorphisms A tensor_R B-linear. Extending these
isomorphisms to C gives the source isomorphism e. Extension of scalars sends
K-flat complexes and their quasi-isomorphisms to K-flat complexes and
quasi-isomorphisms over C. Their cones are acyclic and K-flat, so tensoring
with arbitrary N preserves acyclicity, giving the target isomorphism d.
Naturality of the monoidal tensorator and of the universal counit gives the
comparison square for each roof leg, using comparison_eq and localized_eq.
Compose one square with the inverse of the other to obtain the stated square.
No flatness of C or N is required, since only isomorphisms are extended.
The argument includes unbounded complexes and zero rings.
(blueprint: lem-pc-localized-tensor-comparison-representative-square). -/
theorem exists_localizedTensorComparison_representative_square
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (U V : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : ∀ W : CochainComplex (ModuleCat.{u} A) ℤ, W.Acyclic →
      (CochainComplex.mapBifunctor W U (curriedTensor _)).Acyclic)
    (hV : ∀ W : CochainComplex (ModuleCat.{u} A) ℤ, W.Acyclic →
      (CochainComplex.mapBifunctor W V (curriedTensor _)).Acyclic)
    (eUV : DerivedCategory.Q.obj U ≅ DerivedCategory.Q.obj V)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
    (mV : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∃ (e : (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mU.cohomology i) ≅
        (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mV.cohomology i))
      (d : (F.obj U ⊗ N).homology i ≅ (F.obj V ⊗ N).homology i),
      (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) ≫ d.hom =
      e.hom ≫ mV.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) i := by
  classical
  have (M : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  let E := extendScalars (algebraMap (A ⊗[R] B) C)
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
  let WC := HomologicalComplex.quasiIso (ModuleCat.{u} C) (.up ℤ)
  let α (P : CochainComplex (ModuleCat.{u} A) ℤ)
      (mP : BaseDerivedTensorCohomologyModel R A B (P ⊗ Q) C) :=
    mP.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F P Q).inv ≫ (F.obj P ◁ t)) i
  have hleg {P G : CochainComplex (ModuleCat.{u} A) ℤ}
      (s : P ⟶ G) (hs : QuasiIso s) (hP : W.kFlat P) (hG : W.kFlat G)
      (mP : BaseDerivedTensorCohomologyModel R A B (P ⊗ Q) C)
      (mG : BaseDerivedTensorCohomologyModel R A B (G ⊗ Q) C) :
      ∃ (e : E.obj (mP.cohomology i) ≅ E.obj (mG.cohomology i))
        (d : (F.obj P ⊗ N).homology i ≅ (F.obj G ⊗ N).homology i),
        α P mP ≫ d.hom = e.hom ≫ α G mG := by
    have hsq : QuasiIso (s ▷ Q) :=
      (kFlat_of_acyclic_tensor Q hQ).whiskerRight hs
    obtain ⟨e, he⟩ := exists_baseDerivedTensorModel_quasiIso_comparison
      R A B C (s ▷ Q) hsq mP mG i
    have hFs : QuasiIso (F.map s) :=
      scalarExtension_quasiIso_of_kFlat _ s hs hP hG
    have hFP : WC.kFlat (F.obj P) := kFlat_of_acyclic_tensor _
      (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat _ P
        (acyclic_tensor_of_kFlat P hP))
    have hFG : WC.kFlat (F.obj G) := kFlat_of_acyclic_tensor _
      (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat _ G
        (acyclic_tensor_of_kFlat G hG))
    have ht : QuasiIso (F.map s ▷ N) :=
      WC.whiskerRight_of_kFlat _ hFs hFP hFG N
    have : QuasiIso (F.map s ▷ N) := ht
    let d := asIso (HomologicalComplex.homologyMap (F.map s ▷ N) i)
    refine ⟨E.mapIso e, d, ?_⟩
    have hc : ((Functor.Monoidal.μIso F P Q).inv ≫ (F.obj P ◁ t)) ≫
        (F.map s ▷ N) = F.map (s ▷ Q) ≫
        ((Functor.Monoidal.μIso F G Q).inv ≫ (F.obj G ◁ t)) := by
      rw [Category.assoc, whisker_exchange, ← Category.assoc]
      change (Functor.OplaxMonoidal.δ F P Q ≫ F.map s ▷ F.obj Q) ≫ _ = _
      rw [Functor.OplaxMonoidal.δ_natural_left]
      rfl
    change α P mP ≫ HomologicalComplex.homologyMap (F.map s ▷ N) i =
      E.map e.hom ≫ α G mG
    dsimp only [α]
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, hc,
      HomologicalComplex.homologyMap_comp, ← Category.assoc, he, Category.assoc]
  obtain ⟨L, s, hs, r, he⟩ := DerivedCategory.right_fac eUV.hom
  have : IsIso (DerivedCategory.Q.map s) := hs
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
  have hr : IsIso (DerivedCategory.Q.map r) := by
    have hr' : DerivedCategory.Q.map r = DerivedCategory.Q.map s ≫ eUV.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [hr']
    infer_instance
  have hr' : QuasiIso r := (DerivedCategory.isIso_Q_map_iff_quasiIso _ r).1 hr
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} A))).reduced
  let L' := Λ.resolutionFunctor.obj L
  let a := Λ.resolutionNatTrans.app L
  have : QuasiIso a := inferInstance
  have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le L
  have : QuasiIso s := hs'
  have : QuasiIso r := hr'
  have hsa : QuasiIso (a ≫ s) := inferInstance
  have hra : QuasiIso (a ≫ r) := inferInstance
  obtain ⟨mL⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (L' ⊗ Q) C
  obtain ⟨el, dl, hl⟩ := hleg (a ≫ s) hsa hk (kFlat_of_acyclic_tensor U hU) mL mU
  obtain ⟨er, dr, hr⟩ := hleg (a ≫ r) hra hk (kFlat_of_acyclic_tensor V hV) mL mV
  refine ⟨el.symm ≪≫ er, dl.symm ≪≫ dr, ?_⟩
  change α U mU ≫ dl.inv ≫ dr.hom = el.inv ≫ er.hom ≫ α V mV
  have hl' : α U mU ≫ dl.inv = el.inv ≫ α L' mL := by
    rw [← cancel_epi el.hom]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hl]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [← Category.assoc, hl', Category.assoc, hr]

end ModuleCat
