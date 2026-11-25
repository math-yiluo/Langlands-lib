/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Sf.SfAffineChartFactorizationGluing
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import all WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AffineSpaceRationalInduction
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ClosedAdjointConstructibleYoneda
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalClosedSupportConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# Local factorization of the exceptional inverse image

On affine charts, the exceptional inverse image `f^!` factors through the exceptional inverse
images of a projection and a closed immersion, and preserves bounded constructibility
(`AlgebraicGeometry.ProEtale.restrictionLocal`).

## Implementation details

The exceptional inverse images are arbitrary right adjoints of the corresponding
`localizingLowerShriek` (for arbitrary boundary compactifications), taken as arguments, so the
factorization holds for every choice; the pullbacks are the canonical derived pullback lifts.
No second exceptional inverse image or pullback is introduced.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso
  AlgebraicGeometry.ProEtale.CondensedRing.mateOpenTrivialLowerShriek
  AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency.types true

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

open CondensedRing

private def adjunctionRight {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (_ : L ⊣ R) : D ⥤ C := R

private theorem composition_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A B C : Scheme.{u}}
    [A.Over (Spec (.of k))] [B.Over (Spec (.of k))] [C.Over (Spec (.of k))]
    [IsSeparated (A ↘ Spec (.of k))] [LocallyOfFiniteType (A ↘ Spec (.of k))]
    [QuasiCompact (A ↘ Spec (.of k))]
    [IsSeparated (B ↘ Spec (.of k))] [LocallyOfFiniteType (B ↘ Spec (.of k))]
    [QuasiCompact (B ↘ Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))] [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    [a.IsOver (Spec (.of k))] [b.IsOver (Spec (.of k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (w : a ≫ b = c)
    (ca : Compactification.BoundaryCompactification a)
    (cb : Compactification.BoundaryCompactification b)
    (cc : Compactification.BoundaryCompactification c)
    (ha : ∀ K, localizingClosureProEtale Λ A K → localizingClosureProEtale Λ B
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ ca.obj.obj).obj K))
    (hb : ∀ K, localizingClosureProEtale Λ B K → localizingClosureProEtale Λ C
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cb.obj.obj).obj K))
    (hc : ∀ K, localizingClosureProEtale Λ A K → localizingClosureProEtale Λ C
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cc.obj.obj).obj K)) :
    Nonempty (localizingLowerShriek Λ ca.obj.obj ha ⋙
      localizingLowerShriek Λ cb.obj.obj hb ≅ localizingLowerShriek Λ cc.obj.obj hc) := by
  subst c
  obtain ⟨_, _, _, e, _⟩ := exists_localizingLowerShriekComposition Λ ℓ E hΛ k a b
  exact ⟨e ca cb cc⟩

private theorem preserves_of_adjunctions
    {A B : Type*} [Category A] [Category B]
    (S S' : ObjectProperty A) (T T' : ObjectProperty B)
    (hS : S = S') (hT : T = T')
    (W : ObjectProperty B) (R : ObjectProperty A) [R.IsClosedUnderIsomorphisms]
    (L : S.FullSubcategory ⥤ T.FullSubcategory)
    (G : T.FullSubcategory ⥤ S.FullSubcategory) (a : L ⊣ G)
    (F : S'.FullSubcategory ⥤ T'.FullSubcategory)
    (P : T'.FullSubcategory ⥤ S'.FullSubcategory) (b : F ⊣ P)
    (C : A ⥤ B) (hL : L ⋙ T.ι ≅ S.ι ⋙ C)
    (hF : F ⋙ T'.ι ≅ S'.ι ⋙ C)
    (hP : ∀ K : T'.FullSubcategory, W K.obj → R (P.obj K).obj) :
    ∀ K : T.FullSubcategory, W K.obj → R (G.obj K).obj := by
  subst S'
  subst T'
  let e : L ≅ F := T.fullyFaithfulι.whiskeringRight _ |>.preimageIso (hL ≪≫ hF.symm)
  let r := a.rightAdjointUniq (b.ofNatIsoLeft e.symm)
  intro K hK
  exact R.prop_of_iso (S.ι.mapIso (r.app K)).symm (hP K hK)

private theorem chart_comparison
    {A B C D E : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E]
    {Li : A ⥤ B} {Lp : B ⥤ C} {Lv : C ⥤ D} {Lu : A ⥤ E} {Lf : E ⥤ D}
    {Fi : B ⥤ A} {Fp : C ⥤ B} {Sv : D ⥤ C} {Su : E ⥤ A} {Ff : D ⥤ E}
    (ai : Li ⊣ Fi) (ap : Lp ⊣ Fp) (av : Lv ⊣ Sv) (au : Lu ⊣ Su) (af : Lf ⊣ Ff)
    {Q : A ⥤ C} {H : A ⥤ D}
    (eip : Li ⋙ Lp ≅ Q) (eipv : Q ⋙ Lv ≅ H) (euf : Lu ⋙ Lf ≅ H) :
    Nonempty (Ff ⋙ Su ≅ Sv ⋙ Fp ⋙ Fi) := by
  let ec : (Li ⋙ Lp) ⋙ Lv ≅ Lu ⋙ Lf :=
    Functor.isoWhiskerRight eip Lv ≪≫ eipv ≪≫ euf.symm
  exact ⟨(au.comp af).rightAdjointUniq (((ai.comp ap).comp av).ofNatIsoLeft ec)⟩

private theorem comparison_preserves
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (F : C ⥤ H) (T : C ⥤ D) (P : D ⥤ E) (I : E ⥤ H)
    (e : F ≅ T ⋙ P ⋙ I)
    (W : ObjectProperty C) (R : ObjectProperty D) (Q : ObjectProperty E)
    (Z : ObjectProperty H) [Z.IsClosedUnderIsomorphisms]
    (hT : ∀ K, W K → R (T.obj K))
    (hP : ∀ K, R K → Q (P.obj K))
    (hI : ∀ K, Q K → Z (I.obj K)) :
    ∀ K, W K → Z (F.obj K) := by
  intro K hK
  exact Z.prop_of_iso (e.app K).symm (hI _ (hP _ (hT _ hK)))

private theorem inverseImage_localizing
    {A B : Type v} [Category A] [Category B]
    [HasZeroObject A] [HasZeroObject B] [HasShift A ℤ] [HasShift B ℤ]
    [Preadditive A] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated A] [Pretriangulated B]
    (F : A ⥤ B) [F.CommShift ℤ] [F.IsTriangulated] [F.IsEquivalence]
    (P : ObjectProperty B) (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I D hD hobj
  let := hD
  have : PreservesColimitsOfShape (Discrete I) F :=
    F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : HasColimit (D ⋙ F) := Adjunction.hasColimit_comp_equivalence D F
  have hcol : P (colimit (D ⋙ F)) := hP.prop_colimit (I := I) (D ⋙ F) inferInstance hobj
  exact P.prop_of_iso (preservesColimitIso F D).symm hcol

-- Keep the open adjunction's large normalization clause outside the chart calculation.
private theorem open_adjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    ∃ (hs : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
        localizingClosureProEtale Λ U
          (((localizingClosureProEtale Λ X).ι ⋙
            (CondensedRing.upperStar Λ j).leftDerivedFunctor).obj K))
      (ht : ∀ K, localizingClosureProEtale Λ U K → localizingClosureProEtale Λ X
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ
          (Compactification.ofIsOpenImmersion j)).obj K)),
      Nonempty (localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht ⊣
        (localizingClosureProEtale Λ U).lift
          ((localizingClosureProEtale Λ X).ι ⋙
            (CondensedRing.upperStar Λ j).leftDerivedFunctor) hs) := by
  obtain ⟨he, hs, ht, adj, _⟩ := mateOpenImmersion Λ ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) hΛ j
  have hs' : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U
        (((localizingClosureProEtale Λ X).ι ⋙
          (CondensedRing.upperStar Λ j).leftDerivedFunctor).obj K) := by
    intro K P hP hS
    let := hP.2.1
    exact P.prop_of_iso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).app K.obj).symm
      (hs K P hP hS)
  let L := localizingLowerShriek Λ (Compactification.ofIsOpenImmersion j) ht
  let S := (localizingClosureProEtale Λ U).lift
    ((localizingClosureProEtale Λ X).ι ⋙ (CondensedRing.upperStar Λ j).leftDerivedFunctor) hs'
  let t : L ≅ mateOpenExtension Λ j he := NatIso.ofComponents
    (fun K ↦ (localizingClosureProEtale Λ X).isoMk
      ((mateOpenTrivialLowerShriek Λ j).app K.obj))
    (by intro K N a; ext; exact (mateOpenTrivialLowerShriek Λ j).hom.naturality a.hom)
  let r : S ≅ mateOpenPullback Λ j hs := NatIso.ofComponents
    (fun K ↦ (localizingClosureProEtale Λ U).isoMk
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).app K.obj))
    (by intro K N a; ext;
        exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.naturality a.hom)
  exact ⟨hs', ht, ⟨(adj.ofNatIsoLeft t.symm).ofNatIsoRight r.symm⟩⟩

private noncomputable def coefficientDerived
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    DerivedCategory (FormalSupportModules Λ T) ⥤
      DerivedCategory (FormalSupportModules Λ' T) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.inv.hom T)).mapDerivedCategory

private def coefficientGenerators (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (FormalSupportModules Λ T)) :=
  constantModelBoundedConstructible Λ T ⊓ _root_.DerivedCategory.finiteTorAmplitude _

private theorem localizing_replete (T : Scheme.{u}) :
    (localizingClosureProEtale Λ T).IsClosedUnderIsomorphisms := by
  constructor
  intro K L e hK P hP hS
  let := hP.2.1
  exact P.prop_of_iso e (hK P hP hS)

-- The coefficient and derived-category comparisons require explicit instance transport.
set_option backward.isDefEq.respectTransparency true in
private theorem coefficient_localizing
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u})
    (K : (localizingClosureProEtale Λ T).FullSubcategory) :
    localizingClosureProEtale Λ' T
      ((coefficientDerived e T).obj K.obj) := by
  let R := coefficientDerived e T
  obtain ⟨_, _, _, hL, hgen, _⟩ :=
    localizingClosure_exists Λ' T (coefficientGenerators Λ' T)
  have : (localizingClosureProEtale Λ' T).IsTriangulated := hL.1
  have : (localizingClosureProEtale Λ' T).IsClosedUnderIsomorphisms := hL.2.1
  have : R.IsEquivalence := (shriekCoefficientIso_transport e T).1
  have : PreservesColimitsOfSize.{u + 2, u + 2} R :=
    R.asEquivalence.toAdjunction.leftAdjoint_preservesColimits
  let : R.CommShift ℤ := (inferInstance :
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (coefficientMap e.inv.hom T)).mapDerivedCategory.CommShift ℤ)
  have : R.IsTriangulated := inferInstanceAs
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (coefficientMap e.inv.hom T)).mapDerivedCategory.IsTriangulated
  exact K.property ((localizingClosureProEtale Λ' T).inverseImage R)
    (inverseImage_localizing R _ hL)
    (fun C hC ↦ hgen _ (constantModelCtf_coefficientIso e T ⟨C, hC⟩))

set_option backward.isDefEq.respectTransparency true in
private theorem coefficient_localizing_iff
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u})
    (K : DerivedCategory (FormalSupportModules Λ T)) :
    localizingClosureProEtale Λ' T
        ((coefficientDerived e T).obj K) ↔
      localizingClosureProEtale Λ T K := by
  constructor
  · intro hK
    have h := coefficient_localizing e.symm T ⟨_, hK⟩
    let := localizing_replete Λ T
    exact (localizingClosureProEtale Λ T).prop_of_iso ((transportCompIso e T).app K) h
  · intro hK
    exact coefficient_localizing e T ⟨K, hK⟩

set_option backward.isDefEq.respectTransparency true in
private noncomputable def coefficientEquiv
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (localizingClosureProEtale Λ T).FullSubcategory ≌
      (localizingClosureProEtale Λ' T).FullSubcategory := by
  let F := coefficientDerived e T
  have : F.IsEquivalence := (shriekCoefficientIso_transport e T).1
  let E := F.asEquivalence
  let := localizing_replete Λ' T
  exact E.congrFullSubcategory (funext fun K ↦ propext (coefficient_localizing_iff e T K))

private theorem conjugate_preservation
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (EA : A ≌ A') (EB : B ≌ B')
    (L : A ⥤ B) (L' : A' ⥤ B') (G : B ⥤ A) (adj : L ⊣ G)
    (q : L ⋙ EB.functor ≅ EA.functor ⋙ L')
    (P : ObjectProperty B') (Q : ObjectProperty A') [Q.IsClosedUnderIsomorphisms]
    (h : ∀ (H : B' ⥤ A'), (L' ⊣ H) → ∀ K, P K → Q (H.obj K)) :
    ∀ K, P (EB.functor.obj K) → Q (EA.functor.obj (G.obj K)) := by
  let lc : EA.inverse ⋙ L ⋙ EB.functor ≅ L' :=
    Functor.isoWhiskerLeft EA.inverse q ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EA.counitIso L' ≪≫ L'.leftUnitor
  let adjC := ((EA.symm.toAdjunction.comp adj).comp EB.toAdjunction).ofNatIsoLeft lc
  intro K hK
  exact Q.prop_of_iso (EA.functor.mapIso (G.mapIso (EB.unitIso.app K).symm))
    (h _ adjC _ hK)

-- This conjugates derived adjunctions through two full-subcategory equivalences.
set_option backward.isDefEq.respectTransparency true in
private theorem coefficient_preservation
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (h' : ∀ K, localizingClosureProEtale Λ' X K → localizingClosureProEtale Λ' Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (hpres : ∀ (H : (localizingClosureProEtale Λ' Y).FullSubcategory ⥤
        (localizingClosureProEtale Λ' X).FullSubcategory),
      (localizingLowerShriek Λ' c.obj.obj h' ⊣ H) →
      ∀ K : (localizingClosureProEtale Λ' Y).FullSubcategory,
        constantModelBoundedConstructible Λ' Y K.obj →
        constantModelBoundedConstructible Λ' X (H.obj K).obj) :
    ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      constantModelBoundedConstructible Λ Y K.obj →
      constantModelBoundedConstructible Λ X (G.obj K).obj := by
  let EX := coefficientEquiv e X
  let EY := coefficientEquiv e Y
  let L := localizingLowerShriek Λ c.obj.obj h
  let L' := localizingLowerShriek Λ' c.obj.obj h'
  let q : L ⋙ EY.functor ≅ EX.functor ⋙ L' := NatIso.ofComponents
    (fun K ↦ (localizingClosureProEtale Λ' Y).isoMk
      ((shriekCoefficientCompactificationIso e c).app K.obj))
    (by intro K N b; ext; exact (shriekCoefficientCompactificationIso e c).hom.naturality b.hom)
  let P : ObjectProperty (localizingClosureProEtale Λ' Y).FullSubcategory :=
    fun K ↦ constantModelBoundedConstructible Λ' Y K.obj
  let Q : ObjectProperty (localizingClosureProEtale Λ' X).FullSubcategory :=
    fun K ↦ constantModelBoundedConstructible Λ' X K.obj
  let := (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.1
  have : Q.IsClosedUnderIsomorphisms :=
    inferInstanceAs ((constantModelBoundedConstructible Λ' X).inverseImage
      (localizingClosureProEtale Λ' X).ι).IsClosedUnderIsomorphisms
  have hconj := conjugate_preservation EX EY L L' G adj q P Q hpres
  intro K hK
  apply (CondensedRing.bounded_comap_iff e.inv.hom X (G.obj K).obj).mp
  exact hconj K ((CondensedRing.bounded_comap_iff e.inv.hom Y K.obj).mpr hK)

-- Compare the localizing categories and their compactification-defined adjunctions.
set_option backward.isDefEq.respectTransparency true in
private theorem affine_preserves_canonical
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] [IsAffine V] (d : ℕ)
    (twist : DerivedCategory (FormalSupportModules Λ (AffineSpace (ULift.{u} (Fin d)) V)) ⥤
      DerivedCategory (FormalSupportModules Λ (AffineSpace (ULift.{u} (Fin d)) V)))
    (hassert : affineSpaceRationalAssertion Λ V d (affineSpaceChosenCompactification k V d)
      twist)
    (c : Compactification.BoundaryCompactification
      ((AffineSpace.over (ULift.{u} (Fin d)) V).hom))
    (h : ∀ K, localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V) K →
      localizingClosureProEtale Λ V
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ V).FullSubcategory ⥤
      (localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    ∀ K : (localizingClosureProEtale Λ V).FullSubcategory,
      constantModelBoundedConstructible Λ V K.obj →
      constantModelBoundedConstructible Λ (AffineSpace (ULift.{u} (Fin d)) V)
        (G.obj K).obj := by
  let : (AffineSpace (ULift.{u} (Fin d)) V).Over (Spec (.of k)) :=
    ⟨(AffineSpace.over (ULift.{u} (Fin d)) V).hom ≫ V ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ V) := inferInstance
  have : LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin d)) V ↘ V) ≫ V ↘ Spec (.of k)))
  have : QuasiCompact (AffineSpace (ULift.{u} (Fin d)) V ↘ Spec (.of k)) :=
    inferInstance
  have : IsSeparated (AffineSpace (ULift.{u} (Fin d)) V ↘ Spec (.of k)) :=
    inferInstance
  have : LocallyOfFiniteType (AffineSpace.over (ULift.{u} (Fin d)) V).hom :=
    inferInstanceAs (LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
  have : QuasiCompact (AffineSpace.over (ULift.{u} (Fin d)) V).hom := inferInstance
  have : IsSeparated (AffineSpace.over (ULift.{u} (Fin d)) V).hom := inferInstance
  have : ((AffineSpace.over (ULift.{u} (Fin d)) V).hom).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : CompactSpace V := inferInstance
  have : QuasiSeparatedSpace V := inferInstance
  have : CompactSpace (AffineSpace (ULift.{u} (Fin d)) V) := inferInstance
  have : QuasiSeparatedSpace (AffineSpace (ULift.{u} (Fin d)) V) := inferInstance
  let A := AffineSpace (ULift.{u} (Fin d)) V
  have hA := (localizingClosure_ctf_equals_bc ℓ A Λ hcoeff).1.2.2.2.1
  have hV := (localizingClosure_ctf_equals_bc ℓ V Λ hcoeff).1.2.2.2.1
  obtain ⟨⟨F, P, hF, hP, adjP, _⟩, hpres⟩ := hassert
  have : QuasiSeparatedSpace (affineSpaceChosenCompactification k V d).Z :=
    quasiSeparatedSpace_of_quasiSeparated (affineSpaceChosenCompactification k V d).g
  let c₀ : Compactification.BoundaryCompactification
      ((AffineSpace.over (ULift.{u} (Fin d)) V).hom) :=
    ⟨⟨affineSpaceChosenCompactification k V d, inferInstance⟩⟩
  have hpft : LocallyOfFiniteType (AffineSpace.over (ULift.{u} (Fin d)) V).hom :=
    inferInstanceAs (LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
  obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ ℓ hΛ k
    (AffineSpace.over (ULift.{u} (Fin d)) V).hom
  have eC : localizingLowerShriek Λ c.obj.obj h ⋙ (localizingClosureProEtale Λ V).ι ≅
      (localizingClosureProEtale Λ A).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ
          (affineSpaceChosenCompactification k V d) :=
    φ c c₀
  have hi := (constantModelConstructibleFiniteTor_wellDefined Λ A).2.1
  let := hi
  apply preserves_of_adjunctions (localizingClosureProEtale Λ A)
    (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ A))
    (localizingClosureProEtale Λ V)
    (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ V))
    hA hV (constantModelBoundedConstructible Λ V) (constantModelBoundedConstructible Λ A)
    _ G adj F P adjP _ eC hF
  intro K hK
  exact (constantModelBoundedConstructible Λ A).prop_of_iso (hP.app K).symm
    (hpres K.obj hK)

-- The coefficient and derived-category comparisons require explicit instance transport.
set_option backward.isDefEq.respectTransparency true in
private theorem affine_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] [IsAffine V] (d : ℕ)
    (c : Compactification.BoundaryCompactification
      ((AffineSpace.over (ULift.{u} (Fin d)) V).hom))
    (h : ∀ K, localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V) K →
      localizingClosureProEtale Λ V
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ V).FullSubcategory ⥤
      (localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    ∀ K : (localizingClosureProEtale Λ V).FullSubcategory,
      constantModelBoundedConstructible Λ V K.obj →
      constantModelBoundedConstructible Λ (AffineSpace (ULift.{u} (Fin d)) V)
        (G.obj K).obj := by
  let : (AffineSpace (ULift.{u} (Fin d)) V).Over (Spec (.of k)) :=
    ⟨(AffineSpace.over (ULift.{u} (Fin d)) V).hom ≫ V ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ V) := inferInstance
  have : LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin d)) V ↘ V) ≫ V ↘ Spec (.of k)))
  have : QuasiCompact (AffineSpace (ULift.{u} (Fin d)) V ↘ Spec (.of k)) :=
    inferInstance
  have : IsSeparated (AffineSpace (ULift.{u} (Fin d)) V ↘ Spec (.of k)) :=
    inferInstance
  have : LocallyOfFiniteType (AffineSpace.over (ULift.{u} (Fin d)) V).hom :=
    inferInstanceAs (LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
  have : QuasiCompact (AffineSpace.over (ULift.{u} (Fin d)) V).hom := inferInstance
  have : IsSeparated (AffineSpace.over (ULift.{u} (Fin d)) V).hom := inferInstance
  have : ((AffineSpace.over (ULift.{u} (Fin d)) V).hom).IsOver (Spec (.of k)) := ⟨rfl⟩
  rcases hΛ with he | he
  · obtain ⟨e⟩ := he
    have hadm : IsLocalizingAdmissibleCoefficient ℓ (Profinite.continuousMapRingObj E) :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
    have h' := (compactification_localizing (Profinite.continuousMapRingObj E) ℓ k
      (AffineSpace.over (ULift.{u} (Fin d)) V).hom c hadm).1
    apply coefficient_preservation e c h h' G adj
    intro H a
    exact affine_preserves_canonical _ ℓ k hadm
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))) V d _
      ((affineSpace_rational_induction ℓ k V d).1 E) c h' H a
  · obtain ⟨e⟩ := he
    have hadm : IsLocalizingAdmissibleCoefficient ℓ (Profinite.padicAlgClRingObj ℓ) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
    have h' := (compactification_localizing (Profinite.padicAlgClRingObj ℓ) ℓ k
      (AffineSpace.over (ULift.{u} (Fin d)) V).hom c hadm).1
    apply coefficient_preservation e c h h' G adj
    intro H a
    exact affine_preserves_canonical _ ℓ k hadm
      (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))) V d _
      (affineSpace_rational_induction ℓ k V d).2 c h' H a

-- The coefficient and derived-category comparisons require explicit instance transport.
private theorem closed_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (hadm : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {Z X : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification i)
    (h : ∀ K, localizingClosureProEtale Λ Z K → localizingClosureProEtale Λ X
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Z).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      constantModelBoundedConstructible Λ X K.obj →
      constantModelBoundedConstructible Λ Z (G.obj K).obj := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let O : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range O.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact compl_compl _ |>.symm
  have : QuasiCompact O.ι := inferInstance
  let := closedSupport_lowerStarExact Λ i O.ι hij
  let c₀ : Compactification.BoundaryCompactification i :=
    ⟨⟨Compactification.ofIsProper i, by change QuasiCompact (𝟙 Z); infer_instance⟩⟩
  obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ ℓ hadm k i
  let norm : CondensedRing.rightDerivedLowerShriekOfCompactification Λ c₀.obj.obj ≅
      (CondensedRing.lowerStar Λ i).mapDerivedCategory :=
    Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ Z)
      (CondensedRing.lowerStar Λ i).rightDerivedFunctor ≪≫
      (CondensedRing.lowerStar Λ i).rightDerivedFunctor.leftUnitor ≪≫
      (CondensedRing.lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  let closed : localizingLowerShriek Λ c.obj.obj h ⋙ (localizingClosureProEtale Λ X).ι ≅
      (localizingClosureProEtale Λ Z).ι ⋙ (CondensedRing.lowerStar Λ i).mapDerivedCategory :=
    φ c c₀ ≪≫ Functor.isoWhiskerLeft (localizingClosureProEtale Λ Z).ι norm
  obtain ⟨support⟩ := formalClosedSupportAssertions Λ ℓ k (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) i O.ι hij
  obtain ⟨hK, hS, e, _⟩ := closedAdjointConstructibleYoneda Λ ℓ k (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) i O.ι hij E hΛ c h G adj closed support
  have hpres : ∀ K, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ Z
        ((formalClosedSupport Λ i O.ι).rightDerivedFunctor.obj K) := by
    rcases hΛ with he | he
    · obtain ⟨e⟩ := he
      exact CondensedRing.support_preserved_of_coefficientIso e.symm i O.ι hij
        ((rationalClosedSupportConstructible ℓ k (ringChar k)
          (Fact.out : ringChar k ≠ ℓ) i O.ι hij).1 E)
    · obtain ⟨e⟩ := he
      exact CondensedRing.support_preserved_of_coefficientIso e.symm i O.ι hij
        (rationalClosedSupportConstructible ℓ k (ringChar k)
          (Fact.out : ringChar k ≠ ℓ) i O.ι hij).2
  let := (constantModelConstructibleFiniteTor_wellDefined Λ Z).2.1
  intro K hbc
  exact (constantModelBoundedConstructible Λ Z).prop_of_iso
    ((localizingClosureProEtale Λ Z).ι.mapIso (e.app ⟨K.obj, hbc⟩)).symm
    (hpres K.obj hbc)

set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false in
-- Composite adjunctions and full-subcategory comparisons require explicit elaboration.
/-- Local factorization of `f^!` on affine charts, together with bounded constructibility.
Here `Ff`, `Fp`, `Fi` are right adjoints of `localizingLowerShriek` for `f`, the projection `p`
and the closed immersion `i`, and `huStar`, `hvStar` are the derived pullback lifts. -/
theorem restrictionLocal
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (cf : Compactification.BoundaryCompactification f)
    (hf : ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
        localizingClosureProEtale Λ Y
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cf.obj.obj).obj K))
    (Ff : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (_adjf : CondensedRing.localizingLowerShriek Λ cf.obj.obj hf ⊣ Ff) :
    (∀ {V U : Scheme.{u}} (v : V ⟶ Y) (u : U ⟶ X)
        (hV : IsAffine V) (hU : IsAffine U)
        (hv : IsOpenImmersion v) (hu : IsOpenImmersion u)
        (d : ℕ)
        (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
        (hi : IsClosedImmersion i)
        (q : U ⟶ V)
        (hqi : i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q)
        (hq : q ≫ v = u ≫ f)
        (cp : Compactification.BoundaryCompactification
          ((AffineSpace.over (ULift.{u} (Fin d)) V).hom))
        (hp : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology (AffineSpace
              (ULift.{u} (Fin d)) V)) Ab.{u + 1})
              (condensedRingObj Λ (AffineSpace (ULift.{u} (Fin d)) V))),
          localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V) K →
            localizingClosureProEtale Λ V
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cp.obj.obj).obj K))
        (Fp : (localizingClosureProEtale Λ V).FullSubcategory ⥤
          (localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)).FullSubcategory)
        (adjp : CondensedRing.localizingLowerShriek Λ cp.obj.obj hp ⊣ Fp)
        (ci : Compactification.BoundaryCompactification i)
        (hi' : ∀ K : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
              (condensedRingObj Λ U)),
          localizingClosureProEtale Λ U K →
            localizingClosureProEtale Λ (AffineSpace (ULift.{u} (Fin d)) V)
              ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ ci.obj.obj).obj K))
        (Fi : (localizingClosureProEtale Λ (AffineSpace
            (ULift.{u} (Fin d)) V)).FullSubcategory ⥤
          (localizingClosureProEtale Λ U).FullSubcategory)
        (adji : CondensedRing.localizingLowerShriek Λ ci.obj.obj hi' ⊣ Fi),
        ∃ (huStar : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            localizingClosureProEtale Λ U
              (((localizingClosureProEtale Λ X).ι ⋙
                (CondensedRing.upperStar Λ u).leftDerivedFunctor).obj K))
          (hvStar : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
            localizingClosureProEtale Λ V
              (((localizingClosureProEtale Λ Y).ι ⋙
                (CondensedRing.upperStar Λ v).leftDerivedFunctor).obj K)),
          Nonempty
            ((Ff ⋙
                (localizingClosureProEtale Λ U).lift
                  ((localizingClosureProEtale Λ X).ι ⋙
                    (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar) ≅
              ((localizingClosureProEtale Λ V).lift
                  ((localizingClosureProEtale Λ Y).ι ⋙
                    (CondensedRing.upperStar Λ v).leftDerivedFunctor) hvStar ⋙
                Fp ⋙ Fi)) ∧
          (∀ K : DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
                (condensedRingObj Λ Y)),
            constantModelBoundedConstructible Λ Y K →
              ∃ hK : localizingClosureProEtale Λ Y K,
                constantModelBoundedConstructible Λ U
                  (((localizingClosureProEtale Λ U).lift
                      ((localizingClosureProEtale Λ X).ι ⋙
                        (CondensedRing.upperStar Λ u).leftDerivedFunctor) huStar).obj
                    (Ff.obj ⟨K, hK⟩)).obj)) ∧
      ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (u : ∀ a, U a ⟶ X),
        (∀ a, IsAffine (U a) ∧ IsOpenImmersion (u a)) ∧
        (∀ x : X, ∃ a : Fin n, ∃ y : U a, (u a).base y = x) ∧
        (∀ a, ∃ (V : Scheme.{u}) (v : V ⟶ Y),
          IsAffine V ∧ IsOpenImmersion v ∧
          ∃ (d : ℕ) (i : U a ⟶ AffineSpace (ULift.{u} (Fin d)) V)
            (hi : IsClosedImmersion i) (q : U a ⟶ V),
            i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q ∧ q ≫ v = u a ≫ f) := by
  set_option backward.isDefEq.respectTransparency.types true in
  set_option backward.isDefEq.respectTransparency true in
    classical
    have hcoeff : IsLocalizingAdmissibleCoefficient ℓ Λ := by
      rcases hΛ with ⟨E, hE⟩ | hQ
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ))))
    obtain ⟨E, hE⟩ : ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
      rcases hΛ with ⟨E, hE⟩ | hQ
      · exact ⟨E, Or.inl hE⟩
      · exact ⟨⟨⊥, inferInstance⟩, Or.inr hQ⟩
    have : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    have : IsNoetherian X := ⟨⟩
    have : IsNoetherian Y := ⟨⟩
    constructor
    · intro V U v u hV hU hv hu d i hi q hqi hq cp hp Fp adjp ci hi' Fi adji
      let : V.Over (Spec (.of k)) := ⟨v ≫ Y ↘ Spec (.of k)⟩
      let : U.Over (Spec (.of k)) := ⟨u ≫ X ↘ Spec (.of k)⟩
      have : v.IsOver (Spec (.of k)) := ⟨rfl⟩
      have : u.IsOver (Spec (.of k)) := ⟨rfl⟩
      have : QuasiCompact v := inferInstance
      have : QuasiCompact u := inferInstance
      have : LocallyOfFiniteType (V ↘ Spec (.of k)) :=
        inferInstanceAs (LocallyOfFiniteType (v ≫ Y ↘ Spec (.of k)))
      have : QuasiCompact (V ↘ Spec (.of k)) :=
        inferInstanceAs (QuasiCompact (v ≫ Y ↘ Spec (.of k)))
      have : IsSeparated (V ↘ Spec (.of k)) :=
        inferInstanceAs (IsSeparated (v ≫ Y ↘ Spec (.of k)))
      have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
        inferInstanceAs (LocallyOfFiniteType (u ≫ X ↘ Spec (.of k)))
      have : QuasiCompact (U ↘ Spec (.of k)) :=
        inferInstanceAs (QuasiCompact (u ≫ X ↘ Spec (.of k)))
      have : IsSeparated (U ↘ Spec (.of k)) :=
        inferInstanceAs (IsSeparated (u ≫ X ↘ Spec (.of k)))
      have : q.IsOver (Spec (.of k)) := by
        constructor
        change q ≫ (v ≫ Y ↘ Spec (.of k)) = u ≫ X ↘ Spec (.of k)
        rw [← Category.assoc, hq, Category.assoc, comp_over f]
      have : i.IsOver (Spec (.of k)) := by
        constructor
        change i ≫ ((AffineSpace.over (ULift.{u} (Fin d)) V).hom ≫
          V ↘ Spec (.of k)) = U ↘ Spec (.of k)
        rw [← Category.assoc, hqi, comp_over q]
      let p := (AffineSpace.over (ULift.{u} (Fin d)) V).hom
      have : LocallyOfFiniteType p := inferInstanceAs
        (LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
      have : LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin d)) V) ↘ Spec (.of k)) :=
        inferInstanceAs (LocallyOfFiniteType
          ((AffineSpace.over (ULift.{u} (Fin d)) V).hom ≫ V ↘ Spec (.of k)))
      have : QuasiCompact ((AffineSpace (ULift.{u} (Fin d)) V) ↘ Spec (.of k)) :=
        inferInstance
      have : IsSeparated ((AffineSpace (ULift.{u} (Fin d)) V) ↘ Spec (.of k)) :=
        inferInstance
      obtain ⟨huStar, htu, ⟨au⟩⟩ := open_adjunction Λ ℓ k hcoeff u
      obtain ⟨hvStar, htv, ⟨av⟩⟩ := open_adjunction Λ ℓ k hcoeff v
      let Sv := adjunctionRight av
      let cu : Compactification.BoundaryCompactification u :=
        ⟨⟨Compactification.ofIsOpenImmersion u, by exact ‹QuasiCompact u›⟩⟩
      let cv : Compactification.BoundaryCompactification v :=
        ⟨⟨Compactification.ofIsOpenImmersion v, by exact ‹QuasiCompact v›⟩⟩
      have : ((AffineSpace.over (ULift.{u} (Fin d)) V).hom).IsOver (Spec (.of k)) :=
        ⟨rfl⟩
      have : (i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom).IsOver
          (Spec (.of k)) := ⟨by rw [hqi, comp_over q]⟩
      let cip : Compactification.BoundaryCompactification
          (i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom) := compactificationOverField k
        (i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom)
      let cuf := compactificationOverField k (u ≫ f)
      have hip := (compactification_localizing Λ ℓ k _ cip hcoeff).1
      have huf := (compactification_localizing Λ ℓ k _ cuf hcoeff).1
      have : IsSeparated i := inferInstance
      have : LocallyOfFiniteType i := inferInstance
      have : QuasiCompact i := inferInstance
      have : IsSeparated p := inferInstance
      have : QuasiCompact p := inferInstance
      obtain ⟨eip⟩ := composition_iso Λ ℓ E hE k
        (A := U) (B := AffineSpace (ULift.{u} (Fin d)) V) (C := V)
        i p (i ≫ p) rfl ci cp cip hi' hp hip
      obtain ⟨eipv⟩ := composition_iso Λ ℓ E hE k (A := U) (B := V) (C := Y)
        (i ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom) v (u ≫ f)
        (by rw [hqi, hq]) cip cv cuf hip htv huf
      obtain ⟨euf⟩ := composition_iso Λ ℓ E hE k (A := U) (B := X) (C := Y)
        u f (u ≫ f) rfl cu cf cuf htu hf huf
      obtain ⟨e⟩ := chart_comparison adji adjp av au _adjf eip eipv euf
      refine ⟨huStar, hvStar, ⟨e⟩, ?_⟩
      set_option backward.isDefEq.respectTransparency true in
        have hclosed := closed_preserves Λ ℓ k E hE hcoeff i ci hi' Fi adji
        have haffine := affine_preserves Λ ℓ k E hE V d cp hp Fp adjp
        have hcoeff' : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
            (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
              Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
              Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
            Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
          rcases hE with hE | hQ
          · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
          · exact Or.inr (Or.inr (Or.inr hQ))
        have heqY := (localizingClosure_ctf_equals_bc ℓ Y Λ hcoeff').1.2.2.1
        let := (constantModelConstructibleFiniteTor_wellDefined Λ U).2.1
        intro K hK
        have hctf : coefficientGenerators Λ Y K := (congrFun heqY K).mpr hK
        have hmem : localizingClosureProEtale Λ Y K := fun P _ hP ↦ hP K hctf
        refine ⟨hmem, ?_⟩
        let Z : ObjectProperty (localizingClosureProEtale Λ U).FullSubcategory :=
          fun M ↦ constantModelBoundedConstructible Λ U M.obj
        have : Z.IsClosedUnderIsomorphisms := inferInstanceAs
          ((constantModelBoundedConstructible Λ U).inverseImage
            (localizingClosureProEtale Λ U).ι).IsClosedUnderIsomorphisms
        apply comparison_preserves _ Sv Fp Fi e
          (fun M ↦ constantModelBoundedConstructible Λ Y M.obj)
          (fun M ↦ constantModelBoundedConstructible Λ V M.obj)
          (fun M ↦ constantModelBoundedConstructible Λ
            (AffineSpace (ULift.{u} (Fin d)) V) M.obj) Z ?_ haffine hclosed ⟨K, hmem⟩ hK
        intro M hM
        exact pullback_bounded_constructible Λ v (pullback_constructible Λ v) M.obj hM
    · obtain ⟨n, V, N, U, hUV, m, c, hV, hcovV, hU, hcovU, hc, -⟩ :=
        exists_sf_affine_chart_factorization_gluing k X Y f
      let I := Σ a : Fin n, Fin (N a)
      let e := Fintype.equivFin I
      refine ⟨Fintype.card I, fun a ↦ (U (e.symm a).1 (e.symm a).2).toScheme,
        fun a ↦ (U (e.symm a).1 (e.symm a).2).ι, ?_, ?_, ?_⟩
      · intro a
        exact ⟨hU _ _, inferInstance⟩
      · intro x
        obtain ⟨a, ha⟩ := hcovV (f x)
        obtain ⟨b, hb⟩ := hcovU a x ha
        refine ⟨e ⟨a, b⟩, ?_⟩
        change ∃ y : (U (e.symm (e ⟨a, b⟩)).1 (e.symm (e ⟨a, b⟩)).2).toScheme,
          (U (e.symm (e ⟨a, b⟩)).1 (e.symm (e ⟨a, b⟩)).2).ι.base y = x
        rw [e.symm_apply_apply]
        exact (show ∃ y : (U a b).toScheme, (U a b).ι.base y = x from
          ⟨⟨x, hb⟩, rfl⟩)
      · intro a
        let ab := e.symm a
        refine ⟨(V ab.1).toScheme, (V ab.1).ι, hV _, inferInstance,
          m ab.1 ab.2, c ab.1 ab.2, (hc _ _).1,
          f.resLE (V ab.1) (U ab.1 ab.2) (hUV _ _), (hc _ _).2.1, ?_⟩
        exact f.resLE_comp_ι _

end AlgebraicGeometry.ProEtale
