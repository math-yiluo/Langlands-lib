import Langlands.AlgebraicGeometry.Picard.PoincareDirectImageLocal
import Langlands.AlgebraicGeometry.Picard.PoincareDirectImageSupport
import Langlands.AlgebraicGeometry.Picard.PoincareDirectImageAffineVanishing
import Langlands.AlgebraicGeometry.Modules.AffineHigherDirectImageSections
import Langlands.AlgebraicGeometry.Modules.PointSupportedPushforward
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareDirectImageStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareTangentSectionsProof
import Langlands.CommutativeAlgebra.RegularLocalPunctualComplexProof

/-! # Assembly of the higher direct images of the Poincaré bundle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PoincareDirectImage

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency.types false in
/-- The higher direct images of the Poincaré bundle, assuming the three prerequisite
propositions and the support of the perfect model at the origin. -/
theorem algClosedFieldPoincareDirectImage_of
    (hAL : Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement.{u})
    (hGEO : AlgClosedFieldDualSchemeRelativeDimensionStatement.{u})
    (hTAN : AlgClosedFieldPoincareTangentSectionsStatement.{u})
    (hS : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
      [LocallyOfFiniteType (dualScheme A hA).hom]
      {V : (dualScheme A hA).left.Opens} (hV : IsAffineOpen V) (hx : originPoint hA ∈ V)
      (Kc : CochainComplex (ModuleCat.{u} Γ((dualScheme A hA).left, V)) ℤ),
      IsStrictlyPerfect Kc →
      (∀ (T : CommRingCat.{u}) (φ : Γ((dualScheme A hA).left, V) ⟶ T),
        Nonempty (DerivedCategory.Q.obj ((Cohomology.ModuleComplex.baseChange φ.hom).obj Kc) ≅
          DerivedCategory.Plus.ι.obj
            ((Cohomology.DerivedPlus.derivedComplex (relativeGlobalSections
              (pullback.snd (affineFamily hV) (Spec.map φ)))).obj
                ((Scheme.Modules.pullback (pullback.fst (affineFamily hV) (Spec.map φ))).obj
                  (affinePoincare hV).obj)))) →
      ∀ f ∈ originIdeal hV hx, ∀ n : ℤ,
        IsZero (((Cohomology.ModuleComplex.baseChange
          (algebraMap Γ((dualScheme A hA).left, V) (Localization.Away f))).obj Kc).homology n)) :
    AlgClosedFieldPoincareDirectImageStatement.{u} := by
  intro K _ _ A hA g hg
  have hsm := hGEO K A hA g hg
  have : Smooth (dualScheme A hA).hom := SmoothOfRelativeDimension.smooth g _
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := originPoint hA)
    (U := (⊤ : (dualScheme A hA).left.Opens)) trivial
  have : SmoothOfRelativeDimension g (affineFamily hV) :=
    smoothOfRelativeDimension_affineFamily hV g hg
  have : Smooth (affineFamily hV) := SmoothOfRelativeDimension.smooth g _
  have : IsProper (affineFamily hV) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  obtain ⟨Kc, hKc, ⟨e0⟩, hbc⟩ := universalPerfectSections Γ((dualScheme A hA).left, V) _
    (affineFamily hV) inferInstance inferInstance (affinePoincare hV)
  have hsupp := hS K A hA hV hx Kc hKc hbc
  obtain ⟨hvan, ⟨hgiso⟩⟩ := homology_of_perfectModel hV hAL hTAN g hg hsm hx Kc hKc hbc hsupp
  have hfin := poincareDirectImage_hasFiniteClosedSupport K A hA
  have hpb : IsPullback (pullback.fst (poincareProjection hA) hV.fromSpec) (affineFamily hV)
      (poincareProjection hA) hV.fromSpec := IsPullback.of_hasPullback _ _
  have hsec : ∀ n : ℕ, Nonempty (affineSections hV
      ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom n).obj
        (poincareLineBundle A hA).obj) ≅ Kc.homology n) := fun n =>
    nonempty_affineSections_higherDirectImage_iso_homology _ _ hV hfin hpb Kc e0 n
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨i⟩ := hsec n
    exact isZero_of_isZero_affineSections hV hx (isClosed_originPoint hA) _
      (poincareDirectImage_stalkSupport_subset K A hA n)
      (IsZero.of_iso (hvan n (by exact_mod_cast hn)) i)
  · obtain ⟨i⟩ := hsec g
    exact nonempty_iso_pushforward_of_affineSections_iso (IsLocalRing.closedPoint K)
      (dualOrigin A hA).left (dualScheme A hA).hom (Over.w (dualOrigin A hA)) hV hx _
      (isClosed_originPoint hA) (poincareDirectImage_stalkSupport_subset K A hA g) (i ≪≫ hgiso)

/-- The higher direct images of the Poincaré bundle, assuming the three prerequisite
propositions. -/
theorem algClosedFieldPoincareDirectImage_of_prerequisites
    (hAL : Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement.{u})
    (hGEO : AlgClosedFieldDualSchemeRelativeDimensionStatement.{u})
    (hTAN : AlgClosedFieldPoincareTangentSectionsStatement.{u}) :
    AlgClosedFieldPoincareDirectImageStatement.{u} :=
  algClosedFieldPoincareDirectImage_of hAL hGEO hTAN (by
    intro K _ _ A hA _ V hV hx Kc _ hbc f hf n
    exact poincare_isZero_homology_localization_of_mem_originIdeal K A hA hV hx Kc hbc f hf n)

/-- The higher direct images of the Poincaré bundle, assuming only that the dual is smooth of
relative dimension `g`. The algebraic and tangent prerequisites are the Library's proofs. -/
theorem algClosedFieldPoincareDirectImage_of_relativeDimension
    (hGEO : AlgClosedFieldDualSchemeRelativeDimensionStatement.{u}) :
    AlgClosedFieldPoincareDirectImageStatement.{u} :=
  algClosedFieldPoincareDirectImage_of_prerequisites
    Langlands.CommutativeAlgebra.regularLocalPunctualComplex hGEO
    algClosedFieldPoincareTangentSections

end Langlands.AbelianScheme.PoincareDirectImage
