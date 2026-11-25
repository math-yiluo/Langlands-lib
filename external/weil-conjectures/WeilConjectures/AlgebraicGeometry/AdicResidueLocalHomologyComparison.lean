/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.FlatScalarRealizationFlat
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import all WeilConjectures.AlgebraicGeometry.ConstantDerivedNormalizationUniversal
import WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalScalarDerivedIso
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Residue homology of a specified local completed model

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify

attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  Functor.leftAdjoint

private def modelScalarExtensionIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : proEtaleRingModules X R) :
    (completedAdicChange X φ).obj M ≅
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M := by
  refine eqToIso ((completedAdicChangeData X φ).choose_spec.choose M) ≪≫ ?_
  apply (PresheafOfModules.sheafification (𝟙 _)).mapIso
  exact PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s x =>
      exact (Classical.choose_spec
        (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1} φ M i) s x).trans
        (SheafOfModules.changeOfRingsMap_tmulOfUniverses φ M i s x).symm)

private def modelConstantModuleIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) :
    (adicLisseConstantModules X A).obj M ≅
      (commutativeSiteConstantModuleFunctor (ProEt.topology X) A).obj M := Iso.refl _

private theorem modelCompleted_flat (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u + 1} A) [Module.Projective A M] :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := adicLisseCompletedRing X I)
      ((completedAdicChange X (CompletedConstantReduction.base X I)).obj
        ((adicLisseConstantModules X A).obj M)) := by
  let φ := CompletedConstantReduction.base X I
  let E := SheafOfModules.flatScalarExtension (ProEt.topology X) φ
  let c := modelScalarExtensionIso X φ ((adicLisseConstantModules X A).obj M) ≪≫
    E.mapIso (modelConstantModuleIso X A M)
  have h := SheafOfModules.flatScalarRealization_flat (ProEt.topology X) φ M
    (inferInstanceAs (Module.Flat A M))
  let R := adicLisseCompletedRing X I
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have hc := SheafOfModules.flat_to_cat R _ h
  have hm := (ObjectProperty.flat (A := proEtaleRingModules X R)).prop_of_iso c.symm hc
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm hm.2

private theorem modelScalarKFlatIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (C : CochainComplex (proEtaleRingModules X R) ℤ)
    (hk : C.IsKFlatIndependentCoefficients) :
    Nonempty ((completedAdicDerivedChange X φ).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj C)) := by
  have := pbcExtensionCounit_isIso φ C hk
  have : IsIso (pbcComplexCounit φ C) := by
    unfold pbcComplexCounit
    infer_instance
  exact ⟨asIso (pbcComplexCounit φ C)⟩

private def scalarChangeComp {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ T) :
    completedAdicChange X f ⋙ completedAdicChange X g ≅ completedAdicChange X (f ≫ g) :=
  Adjunction.leftAdjointUniq
    (((pbcScalarAdjunction f).comp (pbcScalarAdjunction g)).ofNatIsoRight
      (pbcRestrictComp f g (f ≫ g) rfl))
    (pbcScalarAdjunction (f ≫ g))

private def constantChangeIso (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    completedAdicChange X
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom f)) ≅
      ConstantScalarRealization.extension (ProEt.topology X) f :=
  Adjunction.leftAdjointUniq (pbcScalarAdjunction _)
    (ConstantScalarRealization.adjunction (ProEt.topology X) f)

private def modelOrdinaryResidueIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    ((completedAdicChange X (limit.π (adicLisseRingSystem X I) (op 0))).mapHomologicalComplex
      (.up ℤ)).obj
      (((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
        (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P)) ≅
      ((commutativeSiteConstantModuleFunctor
        (ProEt.topology X) (A ⧸ I ^ (0 + 1))).mapHomologicalComplex (.up ℤ)).obj
        (AdicPerfectModel.algebraicResidue I P) := by
  let J := ProEt.topology X
  let f := CompletedConstantReduction.base X I
  let g := limit.π (adicLisseRingSystem X I) (op 0)
  let q := Ideal.Quotient.mk (I ^ (0 + 1))
  have hfg : f ≫ g = (constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom q) :=
    (CompletedConstantReduction.base_exists X I).choose_spec.1 0
  let e := scalarChangeComp f g ≪≫
    eqToIso (congrArg (completedAdicChange X) hfg) ≪≫ constantChangeIso X q
  letI := ConstantScalarRealization.extension_additive J q
  let c := ConstantScalarRealization.complexComparison J q P
  have : ∀ n, IsIso (c.f n) := fun n ↦
    (ConstantScalarRealization.moduleComparison_tensor J q (P.X n)).1
  have : IsIso c := HomologicalComplex.Hom.isIso_of_components c
  exact (Functor.mapHomologicalComplexCompIso e (.up ℤ)).app
    ((CompletedConstantReduction.constantComplex X A).obj P) ≪≫ asIso c

private def fixedRestrictionIso (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    sfbFixedScalarRestriction X k ≅
      ConstantNormalizationComparison.restriction (ProEt.topology X) k := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun V ↦ ?_) ?_
    · refine
        { hom := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} k)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intros
                exact (ConstantNormalizationComparison.restriction_smul
                  (ProEt.topology X) k M V _ _).symm }
          inv := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} k)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intros
                exact ConstantNormalizationComparison.restriction_smul
                  (ProEt.topology X) k M V _ _ }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
    · intros; ext x; rfl
  · intros; ext V x; rfl

private def fixedConstantIso (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    commutativeSiteConstantModuleFunctor (ProEt.topology X) k ⋙ sfbFixedScalarRestriction X k ≅
      constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} k) :=
  Functor.isoWhiskerLeft _ (fixedRestrictionIso X k) ≪≫
    (ConstantNormalizationComparison.constantIso (ProEt.topology X) k).symm

private def modelGlobalResidueIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ)
    (hb : ∀ q : ℤ, b < q → IsZero (P.X q))
    (hP : ∀ q : ℤ, Module.Projective A (P.X q)) :
    DerivedCategory.Q.obj (sfbResidueComplex X I (sfbCompletedModel X I P)) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))).mapHomologicalComplex (.up ℤ)).obj
          (AdicPerfectModel.algebraicResidue I P)) := by
  let R := adicLisseCompletedRing X I
  let φ := limit.π (adicLisseRingSystem X I) (op 0)
  let C : CochainComplex (proEtaleRingModules X R) ℤ :=
    ((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
      (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P)
  let := CompletedConstantReduction.constant_additive X A
  have hC : C.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff C b).mpr (fun n hn ↦
    (completedAdicChange X (CompletedConstantReduction.base X I)).map_isZero
      ((adicLisseConstantModules X A).map_isZero (hb n hn)))
  have hf (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := R) (C.X n) := by
    let := hP n
    exact modelCompleted_flat X I (P.X n)
  let := hC
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R C b hf
  let F := sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))
  have : F.IsEquivalence :=
    Functor.isEquivalence_of_iso (fixedRestrictionIso X _).symm
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  let L := completedAdicDerivedChange X φ
  let c : DerivedCategory.Q.obj (sfbResidueComplex X I (sfbCompletedModel X I P)) ≅
      F.mapDerivedCategory.obj (L.obj (DerivedCategory.Q.obj C)) :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage (L.obj _))).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso (L.obj _))
  exact c ≪≫ F.mapDerivedCategory.mapIso (modelScalarKFlatIso X φ C hk).some ≪≫
    F.mapDerivedCategoryFactors.app _ ≪≫
    (by
      simpa only [Functor.comp_obj] using DerivedCategory.Q.mapIso
        ((F.mapHomologicalComplex (.up ℤ)).mapIso (modelOrdinaryResidueIso X I P) ≪≫
          (Functor.mapHomologicalComplexCompIso (fixedConstantIso X _) (.up ℤ)).app
            (AdicPerfectModel.algebraicResidue I P)))

/-- A specified local completed-model isomorphism identifies the derived residue on that
localized stratum with the constant algebraic residue complex. This is only a local
calculation; it asserts neither constructibility nor etale descent nor finiteness.

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Lemma 6.3.13;
Stacks Tags 093M, 099Q and 09AK.
(auxiliary; not a blueprint node).

Proof: inverse image along the immersion is exact and preserves limits. Apply its
canonical limit comparison to the completed coefficient sheaf and its finite projection.
The resulting coefficient isomorphisms respect constant sections and hence the residue
scalar action. Restriction to U is exact. Derived change of rings commutes with these
restrictions by the canonical tensor base-change comparison; calculate it on a K-flat
representative. Apply this comparison to the given local isomorphism. The bounded
projective complex P has a K-flat completed constant realization. Its residue is therefore
computed by ordinary tensor. The canonical associative tensor comparison identifies
this tensor with the constant realization of k tensor_A P, including on the slice over U.
This is precisely the residue and slice comparison of adicPerfectModel_complete_reduction.
The constant module functor is exact, so this identification also identifies all
cohomology sheaves. Exact fixed-scalar restriction and the equivalent small-site functors
commute with this cohomology. Their constant-section units identify the result with the
constant fixed-scalar module sheaf displayed below. No finite residue-field assumption is
used. The same construction sends the zero complex to zero and remains valid on an empty
slice. -/
theorem adicResidue_localModelComparison
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal) [IsAdicComplete I A]
    (K : DerivedCategory.{u + 2, u + 1, u + 2} (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (U : S.ProEt) (P : CochainComplex (ModuleCat.{u + 1, u + 1} A) ℤ) (a b : ℤ)
    (hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q))
    (hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q))
    (e : Nonempty (sfbLocalRestriction.{u} i (adicLisseCompletedRing X I) U K ≅
      sfbLocalRestriction.{u} i (adicLisseCompletedRing X I) U (sfbCompletedModel.{u} X I P)))
    :
    let L := ProEtale.upperStar (ModuleCat.{u + 1, u + 1} (A ⧸ I ^ (0 + 1))) i ⋙
      (ProEt.topology S).overPullback (ModuleCat.{u + 1, u + 1} (A ⧸ I ^ (0 + 1))) U
    letI : L.Additive := Functor.additive_of_preserves_binary_products L
    let C := constantSheaf ((ProEt.topology S).over U)
      (ModuleCat.{u + 1, u + 1} (A ⧸ I ^ (0 + 1)))
    letI : C.Additive := Functor.additive_of_preserves_binary_products C
    Nonempty (L.mapDerivedCategory.obj
      (DerivedCategory.Q.obj (sfbResidueComplex.{u} X I K)) ≅
      DerivedCategory.Q.obj
        ((C.mapHomologicalComplex (.up ℤ)).obj (AdicPerfectModel.algebraicResidue I P))) := by
  have _hI := hI
  dsimp only
  let k := A ⧸ I ^ (0 + 1)
  let L := ProEtale.upperStar (ModuleCat.{u + 1} k) i ⋙
    (ProEt.topology S).overPullback (ModuleCat.{u + 1} k) U
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  let CX := constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} k)
  let : CX.Additive := Functor.additive_of_preserves_binary_products CX
  let CS := constantSheaf ((ProEt.topology S).over U) (ModuleCat.{u + 1} k)
  let : CS.Additive := Functor.additive_of_preserves_binary_products CS
  let c : CX ⋙ L ≅ CS :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ProEtale.constantSheafCompUpperStarIso
        (ModuleCat.{u + 1} k) i) _ ≪≫
      (ProEt.topology S).overPullbackConstantSheafIso (ModuleCat.{u + 1} k) U
  obtain ⟨d⟩ := proEtaleLocalScalarDerivedIso i k
    (limit.π (adicLisseRingSystem X I) (op 0)) U K (sfbCompletedModel X I P) e.some
  exact ⟨d ≪≫ L.mapDerivedCategory.mapIso
      (modelGlobalResidueIso X I P b (fun q hq ↦ hbounded q (Or.inr hq))
        (fun q ↦ (hP q).2)) ≪≫
    L.mapDerivedCategoryFactors.app _ ≪≫
    (by
      simpa only [Functor.comp_obj] using DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).app
          (AdicPerfectModel.algebraicResidue I P)))⟩

end AlgebraicGeometry.Scheme
