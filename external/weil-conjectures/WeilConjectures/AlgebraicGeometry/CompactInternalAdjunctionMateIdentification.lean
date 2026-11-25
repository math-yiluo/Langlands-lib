/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationGeneral

/-! Identification of the canonical maps in compact adjunction exchange.

The mate calculus over a general coefficient category is in
`WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateCanonicalMaps` and
`WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationGeneral`
(split for compile time). -/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory MateIdentification

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

open TwoSquare

attribute [local irreducible] projectionMap _root_.DerivedCategory.monoidalClosed

section General

namespace MateIdentification

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f']
  [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
    L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))

omit [HasSmallSiteSheafify A] [IsIso (projectionMap A f')] in
/-- The left-hand side of `compactInternalAdjunctionExchange_aux` is the left-hand side of
`compactHomMonoidalCompatibility_aux` for the pullback functors. This is a definitional identity,
but the two sides differ in implicit arguments and in the form of universe levels, which makes it
slow for the kernel as a single check; it is split factor by factor. -/
theorem compactInternalAdjunctionExchange_lhs
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G)
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (L(upperStar A g)).map
          ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) ≫
        derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
        (((derivedHom A S').map (inv (B.app N)).op).app
          ((L(upperStar A g)).obj Q)) =
      letI := leftDerivedUpperStarMonoidal A g
      compactHomCompatibilityLHS A adj (L(upperStar A g')) (L(upperStar A g)) N
        (inv (B.app N)) Q := by
  rw [derivedHomUpperStarComparison_eq]
  unfold compactHomCompatibilityLHS
  -- `congr!` splits the definitional check into checks of the three factors.
  congr! (config := { closePre := false, closePost := false }) 3
  all_goals rfl

omit [HasSmallSiteSheafify A] in
/-- The identity of `compactInternalAdjunctionExchangeOfMateCompatibility` for a general
coefficient category and arbitrary right adjoints of `Rf_!`, `Rf'_!`. Stated once over `A` so
that its specialisation to `ModuleCat Λ` matches the statement syntactically (for the kernel). -/
theorem compactInternalAdjunctionExchange_aux
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (h : letI := leftDerivedUpperStarMonoidal A g
      let := leftDerivedUpperStarMonoidal A g'
      let σ := TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom
      let μ := Functor.LaxMonoidal.μTwoSquare (L(upperStar A g')) N
      let ρ := TwoSquare.mk _ _ _ _ (inv B)
      let ν := (Functor.LaxMonoidal.μTwoSquare (L(upperStar A g))
        ((rightDerivedLowerShriek A f).obj N)).whiskerRight
          ((curriedTensor _).map (inv (B.app N)))
      ν.whiskerLeft ((projectionMap A f).app N) =
        (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight
          ((projectionMap A f').app ((L(upperStar A g')).obj N)))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (L(upperStar A g)).map
          ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) ≫
        derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
        (((derivedHom A S').map (inv (B.app N)).op).app
          ((L(upperStar A g)).obj Q)) =
      (derivedBaseChangeMap A sq).app _ ≫
        (R(lowerStar A f')).map
          (derivedHomUpperStarComparison A g' N (G.obj Q)) ≫
        (R(lowerStar A f')).map
          (((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map
            ((mateEquiv adj adj' (inv B)).app Q)) ≫
        ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
          (op ((L(upperStar A g')).obj N))).app ((L(upperStar A g)).obj Q)).hom) := by
  let := leftDerivedUpperStarMonoidal A g
  let := leftDerivedUpperStarMonoidal A g'
  have result := compactHomMonoidalCompatibility_aux A adj adj'
    (L(upperStar A g')) (L(upperStar A g)) N
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom)
    (TwoSquare.mk _ _ _ _ (inv B)) (inv (B.app N))
    (by simpa only [curriedTensor_eq_derivedTensor] using h) Q
  refine (compactInternalAdjunctionExchange_lhs A B N adj Q).trans (result.trans ?_)
  rewrite [derivedHomUpperStarComparison_eq, derivedBaseChangeMap_app_eq]
  congr! (config := { closePre := false, closePost := false }) 3

end MateIdentification

end General

-- The general identity `MateIdentification.compactInternalAdjunctionExchange_aux` (also used by
-- `CompactInternalAdjunctionExchange`) is specialised to `ModuleCat Λ` below; elaborate the
-- statement with the same (generic) instances so that the specialisation matches it
-- syntactically, instead of the kernel comparing the instances found through `ModuleCat`.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f']
  [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)] [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f')]
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙ L(upperStar (ModuleCat.{u + 1} Λ) g) ⟶
    L(upperStar (ModuleCat.{u + 1} Λ) g') ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f')
  [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

end AlgebraicGeometry.Etale
