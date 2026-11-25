/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelComplexes
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction

/-! # Compatible reductions of constant perfect models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

-- Keep the site and localization models folded while elaborating comparisons.
attribute [local irreducible] HasDerivedCategory.standard completed
  adicResidueLocalReductionStep
  adicResidueConstantPerfect adicResidueRestriction
  adicPerfectLocalComplex derivedExtension extend change
  adicPerfectQuotientStep

private theorem counit_naturality
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {R S V : Sheaf T CommRingCat} (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V)
    (e : extend f ⋙ extend g ≅ extend h) {Z K : D R} (s : Z ⟶ K)
    {L : D S} {M : D V} (a : (extend f).obj K ⟶ L)
    (b : (extend g).obj L ⟶ M) (c : (extend h).obj K ⟶ M)
    (hc : e.hom.app K ≫ c = (extend g).map a ≫ b) :
    (extend g).map ((extend f).map s ≫ a) ≫ b =
      e.hom.app Z ≫ ((extend h).map s ≫ c) := by
  have hn := e.hom.naturality s
  change (extend g).map ((extend f).map s) ≫ e.hom.app K =
    e.hom.app Z ≫ (extend h).map s at hn
  rw [Functor.map_comp, Category.assoc, ← hc, ← Category.assoc, hn, Category.assoc]

private theorem derived_transport
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {R V : Sheaf T CommRingCat} {i j : R ⟶ V} (e : i = j) (K : Cx R) :
    (eqToIso (congrArg extend e)).hom.app ((Q R).obj K) ≫
      (extendComparison j).app K =
        (extendComparison i).app K ≫
          (Q V).map ((eqToIso
            (congrArg
              (fun t : R ⟶ V ↦ (change t).mapHomologicalComplex (.up ℤ)) e)).hom.app K) := by
  subst j
  simp

private theorem ordinary_transport
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {R S V : Sheaf T CommRingCat} {i j : R ⟶ V} (e : i = j)
    (F : Mod R ⥤ Mod S) (G : Mod S ⥤ Mod V) [F.Additive] [G.Additive]
    (a : F ⋙ G ≅ change i) (K : Cx R) :
    (Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app K ≫
      (eqToIso (congrArg
        (fun t : R ⟶ V ↦ (change t).mapHomologicalComplex (.up ℤ)) e)).hom.app K =
        (Functor.mapHomologicalComplexCompIso
          (a ≪≫ eqToIso (congrArg change e)) (.up ℤ)).hom.app K := by
  subst j
  simp

private theorem reduction_counit_comp
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {R S V : Sheaf T CommRingCat} (f : R ⟶ S) (g : S ⟶ V)
    (h : R ⟶ V) (e : h = f ≫ g) (K : Cx R)
    (hk : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    (adicFiniteExtendComp f g h e).hom.app ((Q R).obj K) ≫
        (extendComparison h).app K =
      (extend g).map ((extendComparison f).app K) ≫
        (extendComparison g).app (((change f).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (Q V).map ((Functor.mapHomologicalComplexCompIso
          (adicFiniteChangeComp f g ≪≫ eqToIso (congrArg change e.symm))
          (.up ℤ)).hom.app K) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := HasDerivedCategory.standard (Mod V)
  have ht := derived_transport e.symm K
  have hn :
      (adicFiniteExtendComp_existsUnique f g).exists.choose.hom.app ((Q R).obj K) ≫
          (extendComparison (f ≫ g)).app K =
        (extend g).map ((extendComparison f).app K) ≫
          (extendComparison g).app (((change f).mapHomologicalComplex (.up ℤ)).obj K) ≫
          (Q V).map ((Functor.mapHomologicalComplexCompIso
            (adicFiniteChangeComp f g) (.up ℤ)).hom.app K) :=
    (adicFiniteExtendComp_existsUnique f g).exists.choose_spec K hk
  dsimp only [adicFiniteExtendComp, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, ht, ← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [ordinary_transport e.symm (change f) (change g) (adicFiniteChangeComp f g) K]

private def local_model_iso (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    adicPerfectLocalComplex.{u, v} X J U P ≅
      (AdicPerfectModel.overComplex
        (completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
          (AdicPerfectModel.model (coefficientProEtaleModelTopology.{u, v} X) J P) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := completed T A J
  let F := SheafOfModules.strictPerfectConstantSheaf T A ⋙
    SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv ⋙
    change (coefficientMap T A J)
  let G := SheafOfModules.overFunctor (siteModuleRings B) U
  let pres : (SheafOfModules.strictPerfectConstantSheaf T A ⋙
      SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv) ≅
      commutativeSiteConstantModuleFunctor T A :=
    AdicPerfectModel.constantPresentationIso
  let ep : (F.mapHomologicalComplex (.up ℤ)).obj P ≅
      AdicPerfectModel.model T J P :=
    (Functor.mapHomologicalComplexCompIso
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight pres
        (change (coefficientMap T A J))) (.up ℤ)).app P
  unfold adicPerfectLocalComplex
  exact ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
    (.up ℤ)).app P).symm ≪≫ (G.mapHomologicalComplex (.up ℤ)).mapIso ep

attribute [local irreducible] local_model_iso

private theorem local_model_kflat (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (b : ℤ) (hb : P.IsStrictlyLE b)
    (hp : ∀ i : ℤ, Module.Projective A (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)
      (adicPerfectLocalComplex.{u, v} X J U P) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := completed T A J
  let K := AdicPerfectModel.model T J P
  have hk : CochainComplex.IsKFlatTensor (R := B) K :=
    AdicPerfectModel.model_kflat J P b (fun i hi ↦ (P.isStrictlyLE_iff b).1 hb i hi) hp
  have hku := (SheafOfModules.ringedSite_restriction_exact_kflat T B U).2.2 K
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).mpr hk)
  let e := local_model_iso X J U P
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B.over U)
  let := SheafOfModules.monoidalCategory (B.over U)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (B.over U)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (B.over U)
  intro N hN
  let F := ((MonoidalCategory.curriedTensor (Mod (B.over U))).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).obj N
  exact (hku N hN).of_iso (F.mapIso e.symm)

private def local_derived_model_iso (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    (adicResidueRestriction (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      U).obj (adicResidueConstantPerfect.{u, v} X J P) ≅
      (Q ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)).obj
        (adicPerfectLocalComplex.{u, v} X J U P) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := completed T A J
  let F := SheafOfModules.strictPerfectConstantSheaf T A ⋙
    SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv ⋙
    change (coefficientMap T A J)
  let G := SheafOfModules.overFunctor (siteModuleRings B) U
  let := HasDerivedCategory.standard (Mod B)
  let := HasDerivedCategory.standard (Mod (B.over U))
  let : HasDerivedCategory.{max v (u + 1) + 1}
      (SheafOfModules.{max v (u + 1)} ((siteModuleRings B).over U)) :=
    HasDerivedCategory.standard _
  unfold adicResidueRestriction adicResidueConstantPerfect adicPerfectLocalComplex
  exact G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    (Q (B.over U)).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app P)

attribute [local irreducible] local_derived_model_iso
  adicFiniteExtendComp adicFiniteChangeComp

private theorem quotient_step_eq (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (n : ℕ) :
    adicPerfectQuotientStep.{u, v} X J U P n =
      (Functor.mapHomologicalComplexCompIso
        (adicFiniteChangeComp (adicResidueLocalProjection.{u, v} X J U (n + 1))
          (adicPerfectQuotientScalarStep.{u, v} X J U n) ≪≫
            eqToIso (congrArg change (adicPerfectQuotientScalarStep_comp X J U n)))
        (.up ℤ)).app (adicPerfectLocalComplex.{u, v} X J U P) := by
  unfold adicPerfectQuotientStep
  rfl

private theorem derived_step_eq (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicPerfectDerivedQuotientStep.{u, v} X J U n =
      adicFiniteExtendComp (adicResidueLocalProjection.{u, v} X J U (n + 1))
        (adicPerfectQuotientScalarStep.{u, v} X J U n)
        (adicResidueLocalProjection.{u, v} X J U n)
        (adicPerfectQuotientScalarStep_comp X J U n).symm := by
  unfold adicPerfectDerivedQuotientStep adicResidueLocalReductionStep
  rfl

private theorem compatibility_of_kflat_model
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {B : Sheaf T CommRingCat} (R : ℕ → Sheaf T CommRingCat)
    (π : ∀ n, B ⟶ R n) (τ : ∀ n, R (n + 1) ⟶ R n)
    (he : ∀ n, π n = π (n + 1) ≫ τ n)
    (K : Cx B) (Z : D B)
    (hk : CochainComplex.IsKFlatIndependentCoefficients (R := B) K)
    (E : Z ≅ (Q B).obj K) :
    ∃ r : ∀ n, (extend (π n)).obj Z ≅
        (Q (R n)).obj (((change (π n)).mapHomologicalComplex (.up ℤ)).obj K),
      ∀ n,
        (extend (τ n)).map (r (n + 1)).hom ≫
          (extendComparison (τ n)).app
            (((change (π (n + 1))).mapHomologicalComplex (.up ℤ)).obj K) ≫
          (Q (R n)).map
            ((Functor.mapHomologicalComplexCompIso
              (adicFiniteChangeComp (π (n + 1)) (τ n) ≪≫
                eqToIso (congrArg change (he n).symm)) (.up ℤ)).app K).hom =
          (adicFiniteExtendComp (π (n + 1)) (τ n) (π n) (he n)).hom.app Z ≫
            (r n).hom := by
  have hi (n : ℕ) : IsIso ((extendComparison (π n)).app K) := by
    unfold extendComparison extend
    exact (derivedExtension (π n)).computation K
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).mp hk)
  let r (n : ℕ) := (extend (π n)).mapIso E ≪≫ asIso ((extendComparison (π n)).app K)
  refine ⟨r, ?_⟩
  intro n
  dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  exact counit_naturality (π (n + 1)) (τ n) (π n)
    (adicFiniteExtendComp (π (n + 1)) (τ n) (π n) (he n)) E.hom _ _ _
    (reduction_counit_comp (π (n + 1)) (τ n) (π n) (he n) K hk)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Compatible object comparisons for the actual constant perfect model.
Source: Stacks Project, Tags 09C6 and 06YY; the normalized derived extension
composition comparison of Tag 099M.
(auxiliary; not a blueprint node).

Proof: split the finite projective terms as retracts of finite free modules.
The constant realization, completion and slice restriction preserve the
splittings. Therefore the local complex and all its ordinary quotient complexes
are bounded complexes of flat modules and hence K-flat. Compute derived scalar
extension by these complexes, using the K-flat counit. Exact slice restriction
identifies this computation with the restriction of the constant perfect object;
compose the two comparisons to define r at each n. The normalization of
adicFiniteExtendComp is the counit square for successive derived scalar extension
and ordinary scalar reassociation. Evaluate that square on the local K-flat
complex. Naturality of the exact restriction comparison identifies its two sides
with the displayed equation. Both reassociation maps multiply adjacent scalar
factors, so their restriction comparisons agree. This also handles zero complexes,
zero rings, the unit ideal and empty slices, where the same counit identities hold. -/
theorem adicPerfectReductionModels_compatibility (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) :
    let R := fun n : ℕ ↦
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U
    let C : (n : ℕ) → Cx (R n) := fun n ↦ adicPerfectQuotientComplex.{u, v} X J U P n
    let R₀ := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let ρ : (n : ℕ) → D R₀ ⥤ D (R n) := fun n ↦ adicResidueLocalReduction.{u, v} X J U n
    let T : D R₀ := (adicResidueRestriction
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
        (adicResidueConstantPerfect.{u, v} X J P)
    ∃ r : ∀ n : ℕ, (ρ n).obj T ≅ (Q (R n)).obj (C n),
      ∀ n : ℕ,
        (extend (adicPerfectQuotientScalarStep.{u, v} X J U n)).map (r (n + 1)).hom ≫
            (extendComparison (adicPerfectQuotientScalarStep.{u, v} X J U n)).app
              (C (n + 1)) ≫
            (Q (R n)).map (adicPerfectQuotientStep.{u, v} X J U P n).hom =
          (adicPerfectDerivedQuotientStep.{u, v} X J U n).hom.app T ≫ (r n).hom := by
  dsimp only [adicPerfectQuotientComplex]
  simp only [quotient_step_eq, derived_step_eq, adicResidueLocalReduction]
  exact compatibility_of_kflat_model
    (fun n ↦ (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U)
    (fun n ↦ adicResidueLocalProjection.{u, v} X J U n)
    (fun n ↦ adicPerfectQuotientScalarStep.{u, v} X J U n)
    (fun n ↦ (adicPerfectQuotientScalarStep_comp X J U n).symm)
    (adicPerfectLocalComplex.{u, v} X J U P)
    ((adicResidueRestriction
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
        (adicResidueConstantPerfect.{u, v} X J P))
    (local_model_kflat X J U P b _hb (fun i ↦ (_hP i).2))
    (local_derived_model_iso X J U P)

end AlgebraicGeometry.Scheme
