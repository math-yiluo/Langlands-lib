/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology

/-! # Invertibility of the strict-local cohomology comparison

Source: Stacks Project, Tag 03Q9.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

-- Keep projection reduction behind an equality proved with abstract categorical data.
private noncomputable def mappedMate
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    {G : C ⥤ E} {H : D ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ A} {R₂ : A ⥤ E}
    (P : E ⥤ B) (Q : B ⥤ T) (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (sq : TwoSquare G L₁ L₂ H) (K : D) :
    Q.obj (P.obj ((R₁ ⋙ G).obj K)) ⟶ Q.obj (P.obj ((H ⋙ R₂).obj K)) :=
  Q.map (P.map ((mateEquiv a b sq).app K))

private theorem map_mate_eq_mappedMate
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    {G : C ⥤ E} {H : D ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ A} {R₂ : A ⥤ E}
    (P : E ⥤ B) (Q : B ⥤ T) (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (sq : TwoSquare G L₁ L₂ H) (K : D) :
    Q.map (P.map ((mateEquiv a b sq).app K)) =
      mappedMate P Q a b sq K := rfl

-- Transport at the level of the square, before projecting the derived mate.
private theorem isIso_globalHomology_of_data
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}))
    (n : ℤ)
    (E : Sheaf (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{w + 1} ⥤ AddCommGrpCat.{w + 1})
    (H : DerivedCategory.Plus
      (Sheaf (Scheme.strictLocalization s).smallEtaleTopology AddCommGrpCat.{w + 1}) ⥤
        Sheaf (Scheme.strictLocalization s).smallEtaleTopology AddCommGrpCat.{w + 1})
    (a : (upperStar AddCommGrpCat.{w + 1} f).mapDerivedCategoryPlus ⊣
      (lowerStar AddCommGrpCat.{w + 1} f).rightDerivedFunctorPlus)
    (b : (upperStar AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictLocalizationToBase s))).mapDerivedCategoryPlus ⊣
      (lowerStar AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictLocalizationToBase s))).rightDerivedFunctorPlus)
    (t : TwoSquare
        (upperStar AddCommGrpCat.{w + 1}
          (Scheme.strictLocalizationToBase s)).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1} f).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1}
          (pullback.snd f (Scheme.strictLocalizationToBase s))).mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{w + 1}
          (pullback.fst f (Scheme.strictLocalizationToBase s))).mapDerivedCategoryPlus)
    (hE : E = Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{w + 1})
    (hH : H = DerivedCategory.Plus.homologyFunctor _ n)
    (ha : a = (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1} f).derivedPlus)
    (hb : b = (upperStarLowerStarAdjunction AddCommGrpCat.{w + 1}
        (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus)
    (ht : t = TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{w + 1}
        (IsPullback.of_hasPullback f (Scheme.strictLocalizationToBase s)).toCommSq).hom) :
    IsIso (mappedMate H E a b t K) := by
  subst E H a b t
  delta mappedMate
  exact isIso_strictHenselization_baseChange_globalHomology f s K n

/-- The cohomology comparison in the unrestricted stalk formula is invertible.
Source: Stacks Project, Tag 03Q9; this intermediate packages the compatibility of the
strict-local base-change mate, Leray comparison, and exact inverse-image identifications.
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison).

Proof: apply strict-local base-change on global homology to the single complex F[0].
The displayed comparison is the composite of four maps: global sections of the exact
inverse-image/homology isomorphism; global sections of the homology of the derived
base-change mate; the strict-local Leray homology isomorphism; and cohomology of the
inverse-image/single-complex isomorphism. The second factor is invertible by the
strict-local base-change theorem; the other three are images of isomorphisms under
functors. Thus their composite is invertible. This holds for q = 0 and higher q,
including zero sheaves and empty X, and requires no torsion hypothesis.
-/
theorem isIso_strictHenselizationCohomologyComparison
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    IsIso (strictHenselizationCohomologyComparison xbar f F q) := by
  delta strictHenselizationCohomologyComparison
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_))
  · infer_instance
  · rw [map_mate_eq_mappedMate]
    apply isIso_globalHomology_of_data
    · rfl
    · rfl
    · rfl
    · rfl
    · apply congrArg (fun e : _ ≅ _ ↦ TwoSquare.mk _ _ _ _ e.hom)
      apply congrArg (pullbackSquareComparison AddCommGrpCat.{w + 1})
      exact Subsingleton.elim _ _
  · infer_instance
  · infer_instance

end AlgebraicGeometry.Etale
