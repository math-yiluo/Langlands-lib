/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.FlatScalarRealizationFlat
import all WeilConjectures.AlgebraicGeometry.AdicConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalScalarHomologyIso
import Mathlib.Algebra.Module.Projective

/-! # The residue interval on one perfect-model chart

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication;
Stacks Project, Tags 03EL, 06YY and 0E8K.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

private instance localBoundsWEquals (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} (ProEt.topology X)

attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard

private def scalarExtensionIso (X : Scheme.{u})
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

private def constantModuleIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) :
    (adicLisseConstantModules X A).obj M ≅
      (commutativeSiteConstantModuleFunctor (ProEt.topology X) A).obj M := Iso.refl _

private theorem completedModel_flat (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (M : ModuleCat.{u + 1} A) [Module.Projective A M] :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := adicLisseCompletedRing X I)
      ((completedAdicChange X (CompletedConstantReduction.base X I)).obj
        ((adicLisseConstantModules X A).obj M)) := by
  let φ := CompletedConstantReduction.base X I
  let E := SheafOfModules.flatScalarExtension (ProEt.topology X) φ
  let c := scalarExtensionIso X φ ((adicLisseConstantModules X A).obj M) ≪≫
    E.mapIso (constantModuleIso X A M)
  have h := SheafOfModules.flatScalarRealization_flat (ProEt.topology X) φ M
    (inferInstanceAs (Module.Flat A M))
  let R := adicLisseCompletedRing X I
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have hc := SheafOfModules.flat_to_cat R _ h
  have hm := (ObjectProperty.flat (A := proEtaleRingModules X R)).prop_of_iso c.symm hc
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm hm.2

private theorem scalarKFlatIso (X : Scheme.{u})
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

private theorem modelResidue_zero (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ)
    (hb : P.IsStrictlyLE b) (hP : ∀ q : ℤ, Module.Projective A (P.X q))
    (q : ℤ) (hq : IsZero (P.X q)) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (DerivedCategory.Q.obj (sfbResidueComplex X I (sfbCompletedModel X I P)))) := by
  let R := adicLisseCompletedRing X I
  let φ := limit.π (adicLisseRingSystem X I) (op 0)
  let C : CochainComplex (proEtaleRingModules X R) ℤ :=
    ((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
      (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P)
  let := CompletedConstantReduction.constant_additive X A
  let := hb
  have hC : C.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff C b).mpr (fun n hn ↦
    (completedAdicChange X (CompletedConstantReduction.base X I)).map_isZero
      ((adicLisseConstantModules X A).map_isZero (P.isZero_of_isStrictlyLE b n hn)))
  have hf (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) (C.X n) := by
    let := hP n
    exact completedModel_flat X I (P.X n)
  let := hC
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R C b hf
  let F := sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))
  have : PreservesFiniteLimits F := (fixedScalar_exact X _).1
  have : PreservesFiniteColimits F := (fixedScalar_exact X _).2
  let L := completedAdicDerivedChange X φ
  let c : DerivedCategory.Q.obj (sfbResidueComplex X I (sfbCompletedModel X I P)) ≅
      F.mapDerivedCategory.obj (L.obj (DerivedCategory.Q.obj C)) :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage (L.obj _))).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso (L.obj _))
  let V := ((F.mapHomologicalComplex (.up ℤ)).obj
    (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj C))
  let e : DerivedCategory.Q.obj (sfbResidueComplex X I (sfbCompletedModel X I P)) ≅
      DerivedCategory.Q.obj V :=
    c ≪≫ F.mapDerivedCategory.mapIso (scalarKFlatIso X φ C hk).some ≪≫
      F.mapDerivedCategoryFactors.app _
  have hz : IsZero (V.X q) := F.map_isZero ((completedAdicChange X φ).map_isZero
    ((completedAdicChange X (CompletedConstantReduction.base X I)).map_isZero
      ((adicLisseConstantModules X A).map_isZero hq)))
  have hh : IsZero (V.homology q) := (V.sc q).isZero_homology_of_isZero_X₂ hz
  exact (hh.of_iso ((DerivedCategory.homologyFunctorFactors _ q).app V)).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso e)

private def residueHomologyIso (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (q : ℤ) :
    (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.homologyFunctor _ q).obj
          (DerivedCategory.Q.obj (sfbResidueComplex X I K))) ≅
      (SheafOfModules.toSheaf ((adicLisseForget X).obj
        (adicLisseConstantRing X (A ⧸ I ^ (0 + 1))))).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((completedAdicDerivedChange X
              (limit.π (adicLisseRingSystem X I) (op 0))).obj K)) := by
  let F := sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))
  let T := sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits F := (fixedScalar_exact X _).1
  have : PreservesFiniteColimits F := (fixedScalar_exact X _).2
  let L := completedAdicDerivedChange X (limit.π (adicLisseRingSystem X I) (op 0))
  let c : DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅ F.mapDerivedCategory.obj (L.obj K) :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage (L.obj K))).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso (L.obj K))
  exact T.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso c ≪≫
    (F.mapDerivedCategoryHomologyFunctorIso q).symm.app (L.obj K))

/-- The residue of a complex with a specified perfect model on one covering slice
has that model's interval on the same slice. This is a local calculation, with
no stratification, covering hypothesis, compactness or global boundedness assertion.

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Stacks Project,
Tags 03EL, 06YY and 0E8K.
(auxiliary; not a blueprint node).

Proof: put B=adicLisseCompletedRing X I and k=adicLisseConstantRing X (A/I).
The actual inverse-image functor along i is exact, as is restriction to the slice U.
Their tensor comparisons identify the derived inverse image of extension of scalars
along B to k with extension along the inverse image of this map. To see this on
unbounded complexes, choose a flat-term K-flat resolution. Exact inverse image and
slice restriction preserve its quasi-isomorphism and K-flatness. The ordinary
sectionwise tensor comparison gives the identification on these resolutions, and
its compatibility with the derived counits gives it on every derived object.
The local isomorphism e therefore identifies the restricted residue of K with
that of the specified completed realization of P.
Each term of P is projective, hence flat. Constant realization preserves flatness,
and scalar extension of a flat module is flat. The completed realization is bounded
above and termwise flat, hence K-flat, also after restriction. Consequently its
derived residue is computed termwise. A zero term of P stays zero under each
additive realization, tensor and restriction. Thus this residue complex has zero
terms outside [a,b], hence zero homology there. Finally exact fixed-scalar
restriction retains the underlying additive sheaf and commutes with homology.
Transport through the representative isomorphism used in sfbResidueComplex to
obtain precisely the displayed local vanishing. No comparison is chosen as data
and no bound or completeness of K is presupposed. The zero complex, empty slice
and unordered a,b cases use the same termwise argument. -/
theorem adicPerfectModel_localResidueBounds {X S : Scheme.{u}} (i : S ⟶ X)
    [IsImmersion i] {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal)
    (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q))
    (e : sfbLocalRestriction i (adicLisseCompletedRing X I) U K ≅
      sfbLocalRestriction i (adicLisseCompletedRing X I) U (sfbCompletedModel X I P)) :
    ∀ q : ℤ, q < a ∨ b < q →
      IsZero (((ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U).obj
        ((proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) AddCommGrpCat.{u + 1})).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                (DerivedCategory.Q.obj (sfbResidueComplex X I K)))))) := by
  have _ : I.IsMaximal := hI
  intro q hq
  have hz : IsZero (P.X q) := by
    rcases hq with hq | hq
    · let := ha
      exact P.isZero_of_isStrictlyGE a q hq
    · let := hb
      exact P.isZero_of_isStrictlyLE b q hq
  let M := sfbCompletedModel X I P
  let T := sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) AddCommGrpCat.{u + 1})
  let F := proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}
  let G := (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U
  let : (proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}).Additive := ⟨by
    intros
    ext W
    rfl⟩
  let : F.Additive := (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).left_adjoint_additive
  let c := G.mapIso (F.mapIso (residueHomologyIso X I K q)) ≪≫
    (proEtaleLocalScalarHomologyIso i
      (limit.π (adicLisseRingSystem X I) (op 0)) U K M e q).some ≪≫
    G.mapIso (F.mapIso (residueHomologyIso X I M q).symm)
  exact (G.map_isZero (F.map_isZero (T.map_isZero
    (modelResidue_zero X I P b hb (fun n ↦ (hP n).1) q hz)))).of_iso c

end AlgebraicGeometry.Scheme
