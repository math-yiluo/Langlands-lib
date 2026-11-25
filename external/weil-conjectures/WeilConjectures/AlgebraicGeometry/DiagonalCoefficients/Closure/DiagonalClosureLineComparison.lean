/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerScalarFrame
import WeilConjectures.CategoryTheory.Right.RightDerivedExactRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureLineEndpoint
import WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison

/-! # Bounded scalar comparison on a rational root line

Source: diagonal coefficient changes, paragraph (2).
(blueprint: lem-diagonal-closure-line-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
universe u

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private lemma canonicalUnit_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor)
    (h : ∀ P : CochainComplex C ℤ,
      η.app P ≫ (eqToIso (rfl : F.rightDerivedFunctor = F.rightDerivedFunctor)).hom.app
        (DerivedCategory.Q.obj P) = F.rightDerivedFunctorUnitQ P) :
    η = canonicalDiagonalUnit F := by
  ext P
  have hh := h P
  change η.app P ≫ 𝟙 _ = _ at hh
  erw [Category.comp_id] at hh
  exact hh

universe a v w wc

private theorem canonicalSquare_mate
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : F ⋙ V ≅ U ⋙ G)
    (t : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅
      U.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hn : ∀ P : CochainComplex A ℤ,
      V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫
          t.hom.app (DerivedCategory.Q.obj P) ≫
          G.rightDerivedFunctor.map (U.mapDerivedCategoryFactors.hom.app P) =
        V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
          G.rightDerivedFunctorUnitQ ((U.mapHomologicalComplex (.up ℤ)).obj P))
    {L : DerivedCategory C ⥤ DerivedCategory A}
    {L' : DerivedCategory D ⥤ DerivedCategory B}
    (adjX : L ⊣ U.mapDerivedCategory) (adjS : L' ⊣ V.mapDerivedCategory)
    (RG : DiagonalRightDerived G) (hR : RG.R = G.rightDerivedFunctor)
    (hunit : IsCanonicalRightDerived G RG hR) (K : DerivedCategory C)
    (h : IsIso ((Adjunction.pushHomOfComapIso adjX adjS t).app K)) :
    ∃ s : DiagonalTrace.ExactSquareOfUniverses F G U V
        (canonicalDiagonalRightDerived F) RG e,
      IsIso ((Adjunction.pushHomOfComapIso
        (L₁ := RG.R) (L₂ := (canonicalDiagonalRightDerived F).R)
        adjX adjS s.iso).app K) := by
  rcases RG with @⟨RF, η, universal, computation, shift, triangulated⟩
  dsimp only [DiagonalRightDerived.R] at hR
  subst RF
  have hη := canonicalUnit_eq G η hunit
  clear hunit
  subst η
  exact ⟨{ iso := t, normalization := hn }, h⟩

attribute [local irreducible] canonicalDiagonalRightDerived RestrictionSquare.mate
  Mod.derivedExtendMapDerivedCategoryAdjunction
  spRationalTwist spQbarTwist closureLineMap HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Mod.extendScalars AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.upperStar
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

private theorem closureSquare_mate
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} E.1) f))
    (hR : R.R =
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} E.1) f).rightDerivedFunctor)
    (hunit : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} E.1) f) R hR)
    (K : DerivedCategory (Modules (Profinite.continuousMapRingObj.{u} E.1) X))
    (hpush : IsIso ((CondensedRing.derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E) f).app K)) :
    ∃ square : RestrictionSquare (Profinite.padicSubfieldRingObjToPadicAlgCl l E) f R
        (scalarRightDerived (Profinite.padicAlgClRingObj.{u} l) f),
      IsIso ((square.mate (Profinite.padicSubfieldRingObjToPadicAlgCl l E)).app K) := by
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
  let Λ := Profinite.continuousMapRingObj.{u} E.1
  let Λ' := Profinite.padicAlgClRingObj.{u} l
  let F := CondensedRing.lowerStar Λ' f
  let G := CondensedRing.lowerStar Λ f
  let U : Modules Λ' X ⥤ Modules Λ X := Mod.comap (coefficientMap a X)
  let V : Modules Λ' S ⥤ Modules Λ S := Mod.comap (coefficientMap a S)
  let t := CondensedRing.derivedComapLowerStarIso a f
  have hn (P : CochainComplex (Modules Λ' X) ℤ) :
      V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫
          t.hom.app (DerivedCategory.Q.obj P) ≫
          G.rightDerivedFunctor.map (U.mapDerivedCategoryFactors.hom.app P) =
        V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (CondensedRing.comapLowerStarIso a f).hom (.up ℤ)).app P) ≫
          G.rightDerivedFunctorUnitQ ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
    exact rightDerivedExactRestriction_normalization F G U V
      (CondensedRing.comapLowerStarIso a f) P
  delta RestrictionSquare.mate
  change ∃ square : RestrictionSquare a f R (scalarRightDerived Λ' f),
    IsIso ((Adjunction.pushHomOfComapIso
      (L₁ := R.R) (L₂ := (scalarRightDerived Λ' f).R)
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S)) square.iso).app K)
  apply canonicalSquare_mate
    (A := Modules Λ' X) (B := Modules Λ' S)
    (C := Modules Λ X) (D := Modules Λ S)
    F G U V (CondensedRing.comapLowerStarIso a f) t hn
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    R hR hunit K
  exact hpush

set_option linter.unusedVariables false in
/-- A single rational root line extends to the prescribed closure line, and
its shifted scalar/direct-image mate is invertible for a qcqs morphism.
This statement contains no diagonal class, trace, supported source or integration identity.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), common bounded-below colimits.
(blueprint: lem-diagonal-closure-line-comparison).

Proof: Restrict the finite-subextension index to fields containing E; it is filtered
and cofinal. Finite extension of the rational root line is scalar extension:
finite freeness permits scalar extension through the integral root limit, and
localization gives the rational comparison. Take the filtered colimit. The
coefficient colimit is the prescribed condensed algebraic closure and the line
colimit is spQbarTwist; the composite of the scalar unit with the line comparison
is exactly closureLineMap, by the colimit-leg equations. The rational line is
locally free of rank one and hence flat. Apply the K-flat single-complex endpoint
comparison and transport through this ordinary line comparison; adjunction
injectivity gives the required normalization.

Derive the ordinary restriction/direct-image comparison using exact coefficient
restriction and direct-image-acyclic resolutions. Equivalently, derive its
adjoint scalar/inverse-image comparison and take the conjugate. Transport from
the canonical source model to R using hR and its full-unit equation hunit. This
gives the normalized RestrictionSquare, including its equation on every complex.
On the root line shifted by two the scalar mate is the filtered colimit of the
finite-free projection comparisons. All single root-line complexes shifted by
two vanish below -2. Bounded continuity for the qcqs morphism identifies direct
image of the colimit with the colimit of direct images, and exactness of filtered
colimits identifies the derived coefficient endpoints. The finite comparisons
and their colimit are isomorphisms, so this mate component is invertible. No
continuity claim is made on arbitrary unbounded complexes. The proof includes
identity morphisms and the bottom field, and is valid on empty schemes. -/
theorem diagonalClosure_lineComparison
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (hX : IsUnit (l : Γ(X, ⊤)))
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} E.1) f))
    (hR : R.R =
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} E.1) f).rightDerivedFunctor)
    (hunit : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} E.1) f) R hR) :
    ∃ line : Endpoint (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
        (spRationalTwist X l E) (spQbarTwist X l) (closureLineMap l E X),
      ∃ square : RestrictionSquare (Profinite.padicSubfieldRingObjToPadicAlgCl l E) f R
          (scalarRightDerived (Profinite.padicAlgClRingObj.{u} l) f),
        IsIso ((square.mate (Profinite.padicSubfieldRingObjToPadicAlgCl l E)).app
          (((DerivedCategory.singleFunctor _ 0).obj (spRationalTwist X l E))⟦(2 : ℤ)⟧)) := by
  obtain ⟨line⟩ := diagonalClosure_lineEndpoint l E X hX
  let Λ := Profinite.continuousMapRingObj.{u} E.1
  let K : DerivedCategory (Modules Λ X) :=
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj
      (spRationalTwist X l E))⟦(2 : ℤ)⟧
  have h0 : ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj
      (spRationalTwist X l E)).IsGE 0 := by infer_instance
  have hK : K.IsGE (-2) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by omega)
  let C : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X l E)) := ⟨K, ⟨-2, hK⟩⟩
  have hpush := CondensedRing.isIso_derivedPushHom_padicAlgCl_of_boundedBelow l E f C
  exact ⟨line, closureSquare_mate l E f R hR hunit K hpush⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
