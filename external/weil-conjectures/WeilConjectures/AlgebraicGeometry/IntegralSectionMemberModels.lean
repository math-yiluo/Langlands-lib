/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalIsomorphisms
import WeilConjectures.AlgebraicGeometry.IntegralSectionScalarModels

/-! # Integral local models on one pro-etale member

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar upperStar lowerStar
  CategoryTheory.Sheaf.monoidalCategory upperStarFromPointComp
  Mod.extendScalarsIsoComapInv laxBraided_upperStarFromPoint monoidal_upperStarFromPoint
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule continuousScalarFunctor

/-- Pullback to a member admits a finite point model, before any coefficient comparison.
Source: finite constant local models (auxiliary; not a blueprint node). -/
def sectionPointModelAlong
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {Y : Scheme.{u}} (f : Y ⟶ S) : Prop :=
  ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
    Mod.IsFinitelyPresented Λ Q ∧
      Nonempty ((CondensedRing.upperStar Λ (f ≫ g)).obj M ≅
        ((upperStarFromPoint Y).mapMod Λ).obj Q)

/-- The explicit scalar model in the localized module category.
Source: the completed scalar model (auxiliary; not a blueprint node). -/
def integralSectionMemberModel (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt)
    (M : AdicCompletion.Modules l E X) : Prop :=
  ∃ N : ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E),
    Module.FinitePresentation (Scheme.PbcIntegralRing l E) N ∧
      Nonempty ((SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj M))) ≅
          (SheafOfModules.overFunctor _ U).obj
            ((Scheme.proEtaleModuleInverseImage g
              (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
                ((Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj N)))

@[irreducible] private noncomputable def pointModelFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (upperStarFromPoint X).mapMod Λ

private theorem sectionPointModelAlong_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {Y : Scheme.{u}} (f : Y ⟶ S) :
    sectionPointModelAlong Λ g M f ↔
      ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        Mod.IsFinitelyPresented Λ Q ∧
        Nonempty ((CondensedRing.upperStar Λ (f ≫ g)).obj M ≅
          (pointModelFunctor Λ Y).obj Q) := by
  unfold pointModelFunctor
  rfl

private theorem pointModelPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      ((pointModelFunctor Λ X).obj Q) ≅
      (pointModelFunctor Λ Y).obj Q) := by
  let fixedAbSheafify (T : Scheme.{u}) :
      HasSheafify (Scheme.ProEt.topology T) Ab.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, u} T
  let fixedSiteSmall (T : Scheme.{u}) :
      EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let c : (upperStarFromPoint X).mapMod Λ ⋙ CondensedRing.upperStar Λ f ≅
      (upperStarFromPoint Y).mapMod Λ := by
    unfold CondensedRing.upperStar
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapModCompIso (upperStarFromPoint X) (ProEtale.upperStar Ab.{u + 1} f)
          (upperStarFromPointComp f).hom Λ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) ≪≫
          (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).unitIso.symm) ≪≫
      Functor.rightUnitor _
  unfold pointModelFunctor
  exact ⟨c.app Q⟩

@[irreducible] private noncomputable def integralMemberPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    AdicCompletion.Modules l E X ⥤ AdicCompletion.Modules l E Y :=
  CondensedRing.upperStar (DerivedNakayama.integerRing l E) f

@[irreducible] private noncomputable def integralPointModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E) ⥤ AdicCompletion.Modules l E X :=
  pointModelFunctor (DerivedNakayama.integerRing l E) X

private theorem nativePointModel_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S Y : Scheme.{u}} (g : S ⟶ X) (f : Y ⟶ S)
    (M : AdicCompletion.Modules l E X) :
    sectionPointModelAlong (DerivedNakayama.integerRing l E) g M f ↔
      ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E),
        Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) Q ∧
        Nonempty ((integralMemberPullback l E (f ≫ g)).obj M ≅
          (integralPointModel l E Y).obj Q) := by
  unfold integralMemberPullback integralPointModel
  exact sectionPointModelAlong_iff (DerivedNakayama.integerRing l E) g M f

private theorem nativePointModelPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E)) :
    Nonempty ((integralMemberPullback l E f).obj
      ((integralPointModel l E X).obj Q) ≅ (integralPointModel l E Y).obj Q) := by
  unfold integralMemberPullback integralPointModel
  exact pointModelPullback (DerivedNakayama.integerRing l E) f Q

private theorem nativeLocalIsomorphisms (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt)
    (M N : AdicCompletion.Modules l E X) :
    Nonempty ((integralMemberPullback l E
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)).obj M ≅
      (integralMemberPullback l E
        (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)).obj N) ↔
    Nonempty ((SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj M))) ≅
      (SheafOfModules.overFunctor _ U).obj
        ((Scheme.proEtaleModuleInverseImage g
          (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
            ((SheafOfModules.restrictScalars.{u + 1}
              (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
                ((integralSectionFunctor l E X).obj N)))) := by
  unfold integralMemberPullback
  exact integralSectionLocalIsomorphisms l E g U M N

private theorem finitePresentation_restrict
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (N : ModuleCat.{u + 1} S)
    (hN : Module.FinitePresentation S N) :
    Module.FinitePresentation R ((ModuleCat.restrictScalars e.toRingHom).obj N) := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have hbij : Function.Bijective (Algebra.linearMap R S) := e.bijective
  let : Module.FinitePresentation R S := Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective (Algebra.linearMap R S) hbij)
  let N' := (ModuleCat.restrictScalars e.toRingHom).obj N
  let : Module S N' := N.isModule
  let : Module.FinitePresentation S N' := hN
  let : IsScalarTower R S N' :=
    { smul_assoc := fun r s x ↦ by
        change (e r * s) • x = e r • (s • x)
        exact mul_smul (e r) s x }
  exact Module.FinitePresentation.trans R N' S

@[irreducible] private noncomputable def integralPointScalarFunctor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E) :=
  let A := Padic.coefficientExtensionIntegers l E
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  continuousScalarFunctor A

private theorem integerClassification (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∀ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E),
      Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) Q ↔
      ∃ N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E),
        Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) N ∧
        Nonempty (Q ≅ (integralPointScalarFunctor l E).obj N) := by
  unfold integralPointScalarFunctor
  let A := Padic.coefficientExtensionIntegers l E
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact continuousScalarFinitePresentation A

private theorem scalarModelComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (hN : Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) N) :
    Nonempty ((SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
      ((integralSectionFunctor l E X).obj
        ((integralPointModel l E X).obj
          ((integralPointScalarFunctor l E).obj N))) ≅
      (Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj
        ((ModuleCat.restrictScalars
          (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
            Padic.coefficientExtensionIntegers l E).toRingHom).obj N)) := by
  unfold integralPointScalarFunctor integralPointModel pointModelFunctor
  exact integralSectionScalarModels l E X N hN

private theorem mapNonemptyIso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N : C} (h : Nonempty (M ≅ N)) :
    Nonempty (F.obj M ≅ F.obj N) := by
  obtain ⟨a⟩ := h
  exact ⟨F.mapIso a⟩

private theorem transNonemptyIso {C : Type*} [Category C] {M N P : C}
    (h : Nonempty (M ≅ N)) (k : Nonempty (N ≅ P)) : Nonempty (M ≅ P) := by
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := k
  exact ⟨a ≪≫ b⟩

private theorem symmNonemptyIso {C : Type*} [Category C] {M N : C}
    (h : Nonempty (M ≅ N)) : Nonempty (N ≅ M) := by
  obtain ⟨a⟩ := h
  exact ⟨a.symm⟩

/-- On a single member, the fixed section comparison preserves finite scalar models.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), scalar comparison
in step 7 of the integral constructibility bridge.
(auxiliary; not a blueprint node).

Proof: write a finite presentation of the point module as a matrix between finite sums
of the regular module. Evaluation of continuous scalar functions at the singleton
identifies the matrix entries with the valuation ring underlying PbcIntegralRing.
Form the ordinary cokernel N of this matrix. Pullback from the point, the section-action
equivalence, and restriction along the coefficient isomorphism preserve finite sums and
cokernels. On every positive quotient the normalized coefficient comparisons send each
entry to the same constant scalar section; joint monicity of the limit projections
identifies the completed entries. Naturality of those projections also identifies the
coefficient maps after inverse image along g and restriction to U. Hence the localized
finite cokernel is the completed constant realization of N. Conversely choose a finite
presentation of N and form its matrix cokernel of regular modules on the condensed point.
It is finitely presented by construction. The same comparison and full faithfulness of
the section-action and localized-site equivalences reflect the local isomorphism to
that point model. This is one member only: no cover, stratification or Noetherianity
occurs. Empty matrices, torsion and empty schemes are allowed. -/
theorem integralSectionMemberModels (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (g : S ⟶ X) (U : S.ProEt)
    (M : AdicCompletion.Modules l E X) :
    sectionPointModelAlong (DerivedNakayama.integerRing l E) g M U.hom ↔
      integralSectionMemberModel l E g U M := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let e : Scheme.PbcIntegralRing l E ≃+* A := ULift.ringEquiv
  constructor
  · intro h
    obtain ⟨Q, hQ, b⟩ := (nativePointModel_iff l E g U.hom M).mp h
    obtain ⟨N, hN, c⟩ := (integerClassification l E Q).mp hQ
    have d := transNonemptyIso b
      (transNonemptyIso
        (mapNonemptyIso
          (integralPointModel l E ((𝟭 Scheme).obj U.left)) c)
        (symmNonemptyIso (nativePointModelPullback l E
          (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)
          ((integralPointScalarFunctor l E).obj N))))
    have d' := (nativeLocalIsomorphisms l E g U M
      ((integralPointModel l E X).obj ((integralPointScalarFunctor l E).obj N))).mp d
    have a := scalarModelComparison l E X N hN
    have a' := mapNonemptyIso (SheafOfModules.overFunctor _ U)
      (mapNonemptyIso (Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))) a)
    refine ⟨(ModuleCat.restrictScalars
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom).obj N, ?_,
      transNonemptyIso d' a'⟩
    exact finitePresentation_restrict e N hN
  · rintro ⟨N, hN, b⟩
    let N' := (ModuleCat.restrictScalars e.symm.toRingHom).obj N
    have hN' : Module.FinitePresentation A N' :=
      finitePresentation_restrict e.symm N hN
    have a := scalarModelComparison l E X N' hN'
    have a' := mapNonemptyIso (SheafOfModules.overFunctor _ U)
      (mapNonemptyIso (Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))) a)
    have roundtrip : (ModuleCat.restrictScalars
        (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
          Padic.coefficientExtensionIntegers l E).toRingHom).obj N' ≅ N :=
      (ModuleCat.restrictScalarsComp'App e.toRingHom e.symm.toRingHom
        (RingHom.id _) e.symm_toRingHom_comp_toRingHom.symm N).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl N
    have r := mapNonemptyIso (SheafOfModules.overFunctor _ U)
      (mapNonemptyIso (Scheme.proEtaleModuleInverseImage g
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)))
          (mapNonemptyIso
            (Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E))
            ⟨roundtrip.symm⟩))
    have d := transNonemptyIso (transNonemptyIso b r) (symmNonemptyIso a')
    have d' := (nativeLocalIsomorphisms l E g U M
      ((integralPointModel l E X).obj ((integralPointScalarFunctor l E).obj N'))).mpr d
    apply (nativePointModel_iff l E g U.hom M).mpr
    refine ⟨(integralPointScalarFunctor l E).obj N', ?_, transNonemptyIso d'
      (nativePointModelPullback l E
          (@CategoryStruct.comp Scheme _ ((𝟭 Scheme).obj U.left) S X U.hom g)
          ((integralPointScalarFunctor l E).obj N'))⟩
    exact (integerClassification l E ((integralPointScalarFunctor l E).obj N')).mpr
      ⟨N', hN', ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale
