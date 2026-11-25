/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Coherence of a normalized Brown level realization

This module isolates the section, localization, and mate equations for supplied
realization data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

private def brownCoherenceGenericRestriction (W : Scheme.{u})
    (A B : CommRingCat.{u + 1}) (f : A ⟶ B) :
    SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose W.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map f)) ⋙
      Etale.SystemProjection.constantModule W A ≅
    Etale.SystemProjection.constantModule W B ⋙
      Sheaf.restrictScalars W.smallEtaleTopology f.hom := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)) ?_)) ?_
  · ext x
    have hn := congrArg (fun g ↦ g.app U a)
      (toSheafify_naturality W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).map f))
    exact congrArg (fun b ↦ b • (show M.val.obj U from x)) hn
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

-- State the section equation over arbitrary rings: specializing its proof does not
-- require the kernel to check the expanded quotient-ring section expression again.
private theorem brownCoherenceGenericSections (W : Scheme.{u})
    (A B : CommRingCat.{u + 1}) (f : A ⟶ B)
    (e : SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose W.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map f)) ⋙
      Etale.SystemProjection.constantModule W A ≅
    Etale.SystemProjection.constantModule W B ⋙
      Sheaf.restrictScalars W.smallEtaleTopology f.hom)
    (he : e = brownCoherenceGenericRestriction W A B f)
    (M : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} W.smallEtaleTopology
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).obj B))
    (U : W.Etaleᵒᵖ) (x : M.val.obj U) :
    HEq ((e.hom.app M).hom.app U x) x := by
  subst e
  exact HEq.rfl

-- The mate equation is categorical; checking it here avoids unfolding the concrete
-- derived adjunctions when checking the realization theorem.
private theorem brownCoherenceInverseMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D} [F.IsEquivalence] [G.IsEquivalence]
    (a : L ⊣ R) (b : L' ⊣ R') (e : R ⋙ F ≅ G ⋙ R') :
    ∃ s : L ⋙ G ≅ F ⋙ L', (mateEquiv a b (.mk _ _ _ _ s.inv)) = e.hom := by
  have := isIso_inverseMate_of_equivalences a b e
  refine ⟨(asIso ((mateEquiv a b).symm (.mk _ _ _ _ e.hom))).symm, ?_⟩
  exact (mateEquiv a b).apply_symm_apply (.mk _ _ _ _ e.hom)

variable (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})

set_option maxHeartbeats 2000000 in
-- Checking section identities unfolds the two constant-scalar restriction constructions.
private def ordinaryRestrictionIso {m n : ℕ} (h : m ≤ n) :
    coefficientRestriction (J := W.smallEtaleTopology) O t h ⋙
      strictEtaleBrownConstant O t W n ≅
    strictEtaleBrownConstant O t W m ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
      ext x
      change ((M.val.obj U).smul
          ((toSheafify W.smallEtaleTopology
            ((Functor.const W.Etaleᵒᵖ).obj
              (CommRingCat.of (strictEtaleBrownRing O t m)))).app U
                (strictEtaleBrownRingMap O t h a))).asHom.hom x =
        ((M.val.obj U).smul
          ((coefficientQuotientMap (J := W.smallEtaleTopology) O t h).hom.app U
            ((toSheafify W.smallEtaleTopology
              ((Functor.const W.Etaleᵒᵖ).obj
                (CommRingCat.of (strictEtaleBrownRing O t n)))).app U a))).asHom.hom x
      have hu := congrArg (fun f ↦ f.app U a)
        (toSheafify_naturality W.smallEtaleTopology
          ((Functor.const W.Etaleᵒᵖ).map
            (CommRingCat.ofHom (strictEtaleBrownRingMap O t h))))
      exact congrArg (fun r ↦ ((M.val.obj U).smul r).asHom.hom x) hu)
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem brownCoherenceDerivedRestriction
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealizationData O t W P)
    {m n : ℕ} (h : m ≤ n) :
    letI := R.ordinaryAdditive
    ∃ δ : (P.scalar h).restriction ⋙ R.derived n ≅ R.derived m ⋙
        Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h),
      ∀ K : CochainComplex (strictEtaleLevel W O t m) ℤ,
        δ.hom.app (DerivedCategory.Q.obj K) ≫
          (Sheaf.derivedRestrictScalars W.smallEtaleTopology
            (strictEtaleBrownRingMap O t h)).map ((R.factors m).hom.app K) ≫
          (Sheaf.restrictScalars W.smallEtaleTopology
            (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors.hom.app
              (((strictEtaleBrownConstant O t W m).mapHomologicalComplex (.up ℤ)).obj K) =
        (R.derived n).map ((P.scalar h).restrictionFactors.hom.app K) ≫
          (R.factors n).hom.app
            (((coefficientRestriction (J := W.smallEtaleTopology) O t h).mapHomologicalComplex
              (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (ordinaryRestrictionIso O t W h)
              (.up ℤ)).hom.app K) := by
  let := R.ordinaryAdditive
  exact exists_derivedSquare_independentUniverses
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (strictEtaleBrownConstant O t W m) (strictEtaleBrownConstant O t W n)
    (Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (P.scalar h).restriction (R.derived m) (R.derived n)
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (P.scalar h).restrictionFactors (R.factors m) (R.factors n)
    (Sheaf.restrictScalars W.smallEtaleTopology
      (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors
    (ordinaryRestrictionIso O t W h)

-- The normalization transports adjunctions between two concrete derived-category universes.
/-- Normalize the comparison maps while retaining the supplied derived functors and
factorizations. Arbitrary comparison isomorphisms are not automatically normalized.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-level-realization-coherence).

Proof: naturality of the constant-ring sheafification unit makes the identity on
sections linear for scalar restriction. Lift that square through localization,
using the supplied factorization maps. The inverse mate is invertible because
both realization functors are equivalences. Use its inverse as the scalar
comparison. Its mate equation is the inverse law of the mate equivalence.
All arguments include identity quotient maps and the zero quotient ring. -/
theorem etaleBrownLevelRealizationCoherence_exists
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    (R : StrictEtaleBrownRealizationData O t W P) :
    Nonempty (StrictEtaleBrownRealization O t W P) := by
  let := R.ordinaryAdditive
  let := R.equivalence
  have hd {m n : ℕ} (h : m ≤ n) := brownCoherenceDerivedRestriction O t W P R h
  choose restriction hrestriction using @hd
  have hs {m n : ℕ} (h : m ≤ n) := brownCoherenceInverseMate (P.scalar h).derivedAdj
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
      (strictEtaleBrownRingMap O t h))) (restriction h)
  choose scalar hscalar using @hs
  let R' : StrictEtaleBrownRealizationData O t W P :=
    { ordinaryAdditive := R.ordinaryAdditive
      derived := R.derived
      factors := R.factors
      equivalence := R.equivalence
      ordinaryRestriction := ordinaryRestrictionIso O t W
      restriction := restriction
      scalar := scalar }
  refine ⟨⟨R', ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m n h
    exact brownCoherenceGenericSections W _ _
      (CommRingCat.ofHom (strictEtaleBrownRingMap O t h))
      (ordinaryRestrictionIso O t W h) rfl
  · exact hrestriction
  · exact hscalar

end AlgebraicGeometry
