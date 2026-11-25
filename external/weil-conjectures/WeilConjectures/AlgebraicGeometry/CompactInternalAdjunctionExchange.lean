/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentification
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! Cartesian compatibility of internal compact adjunction. -/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

attribute [local instance] isIso_rightDerivedLowerShriekBaseChangeMap
attribute [local instance] isIso_projectionMap_of_finite

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

/-- The Cartesian compact-adjunction square, at generic coefficients, for arbitrary right
adjoints `G`, `G'` of `Rf_!`, `Rf'_!` (for a finite ring `Λ`: `Rf^!`, `Rf'^!`).
(auxiliary; not a blueprint node). -/
def compactInternalAdjunctionExchangeSquare
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
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
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (sq : CommSq g' f' f g)
    (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
      L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (E : G ⋙ L(upperStar A g') ⟶ L(upperStar A g) ⋙ G') : Prop :=
  (L(upperStar A g)).map
          ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) ≫
        derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
        (((derivedHom A S').map (inv (B.app N)).op).app
          ((L(upperStar A g)).obj Q)) =
      (derivedBaseChangeMap A sq).app _ ≫
        (R(lowerStar A f')).map
          (derivedHomUpperStarComparison A g' N (G.obj Q)) ≫
        (R(lowerStar A f')).map
          (((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map (E.app Q)) ≫
        ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
          (op ((L(upperStar A g')).obj N))).app ((L(upperStar A g)).obj Q)).hom)

/-- Expand the canonical compact-adjunction square through its equality API.
(auxiliary; not a blueprint node). -/
theorem compactInternalAdjunctionExchangeSquare_iff
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
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
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (sq : CommSq g' f' f g)
    (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
      L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (E : G ⋙ L(upperStar A g') ⟶ L(upperStar A g) ⋙ G') :
    compactInternalAdjunctionExchangeSquare A adj adj' sq B N Q E ↔
    (L(upperStar A g)).map
              ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) ≫
            derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
            (((derivedHom A S').map (inv (B.app N)).op).app
              ((L(upperStar A g)).obj Q)) =
          (derivedBaseChangeMap A sq).app _ ≫
            (R(lowerStar A f')).map
              (derivedHomUpperStarComparison A g' N (G.obj Q)) ≫
            (R(lowerStar A f')).map
              (((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map (E.app Q)) ≫
            ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
              (op ((L(upperStar A g')).obj N))).app ((L(upperStar A g)).obj Q)).hom)
    := Iff.rfl

section MateCalculation

open TwoSquare

attribute [local irreducible] projectionMap _root_.DerivedCategory.monoidalClosed

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
  {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
  {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
  (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
    L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))

private theorem compact_exchange_mates
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
    compactInternalAdjunctionExchangeSquare A adj adj' sq B N Q (mateEquiv adj adj' (inv B)) := by
  apply (compactInternalAdjunctionExchangeSquare_iff A adj adj' sq B N Q _).2
  exact MateIdentification.compactInternalAdjunctionExchange_aux A sq B N adj adj' h Q

private theorem compact_exchange_projection
    (hp : ∀ T : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A),
      (L(upperStar A g)).map (((projectionMap A f).app N).app T) ≫
          B.app (((derivedTensor A X).obj N).obj ((L(upperStar A f)).obj T)) ≫
          (rightDerivedLowerShriek A f').map
            (((leftDerivedUpperStarTensorComparison A g').app N).app
              ((L(upperStar A f)).obj T)) ≫
          (rightDerivedLowerShriek A f').map
            (((derivedTensor A X').obj ((L(upperStar A g')).obj N)).map
              (derivedSquareUpperStarIsoInvApp A sq T)) =
        ((leftDerivedUpperStarTensorComparison A g).app
            ((rightDerivedLowerShriek A f).obj N)).app T ≫
          (((derivedTensor A S').map (B.app N)).app ((L(upperStar A g)).obj T)) ≫
          ((projectionMap A f').app ((L(upperStar A g')).obj N)).app
            ((L(upperStar A g)).obj T))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    compactInternalAdjunctionExchangeSquare A adj adj' sq B N Q (mateEquiv adj adj' (inv B)) := by
  apply compact_exchange_mates A adj adj' sq B N _ Q
  let := leftDerivedUpperStarMonoidal A g
  let := leftDerivedUpperStarMonoidal A g'
  ext T
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, Functor.LaxMonoidal.μTwoSquare,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id,
    Category.assoc, curriedTensor_map_app, curriedTensor_obj_obj]
  have hsq : IsIso (derivedSquareUpperStarIsoInvApp A sq T) := by
    unfold derivedSquareUpperStarIsoInvApp
    infer_instance
  rw [← cancel_epi (((leftDerivedUpperStarTensorComparison A g).app
      ((rightDerivedLowerShriek A f).obj N)).app T ≫
        (((derivedTensor A S').map (B.app N)).app ((L(upperStar A g)).obj T)))]
  rw [← cancel_mono (B.app (((derivedTensor A X).obj N).obj
      ((L(upperStar A f)).obj T)) ≫
        (rightDerivedLowerShriek A f').map
          (((leftDerivedUpperStarTensorComparison A g').app N).app
            ((L(upperStar A f)).obj T)) ≫
        (rightDerivedLowerShriek A f').map
          (((derivedTensor A X').obj ((L(upperStar A g')).obj N)).map
            (derivedSquareUpperStarIsoInvApp A sq T)))]
  simp only [Category.assoc, NatIso.isIso_inv_app, Functor.comp_obj,
    derivedTensor, curriedTensor_map_app, curriedTensor_obj_obj] at *
  have δg (U V : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
      Functor.OplaxMonoidal.δ (L(upperStar A g)) U V =
        ((leftDerivedUpperStarTensorComparison A g).app U).app V := rfl
  have δg' (U V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      Functor.OplaxMonoidal.δ (L(upperStar A g')) U V =
        ((leftDerivedUpperStarTensorComparison A g').app U).app V := rfl
  simp only [← δg, ← δg']
  erw [hom_inv_whiskerRight'_assoc, Functor.Monoidal.δ_μ_assoc,
    IsIso.inv_hom_id_assoc, Functor.Monoidal.μ_δ_map_assoc]
  unfold derivedSquareUpperStarIsoInvApp
  simp only [tensorLeft]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  simpa only [Functor.map_comp, Category.assoc, δg, δg',
    derivedSquareUpperStarIsoInvApp] using hp T

end MateCalculation

/-- Internal compact adjunction commutes with Cartesian exchange.
Source: blueprint lem-asd-smooth-generic-direct-image.proof.md, final paragraph;
compact projection/exchange compatibility (auxiliary; not a blueprint node).

Proof: Write the compact-adjunction isomorphism as the conjugate of the compact
projection map through the ordinary, tensor--Hom and exceptional adjunctions. The
canonical compact projection/exchange square is projectionMap_rightDerivedLowerShriekBaseChangeMap.
Cancel its invertible compact exchange, tensor comparisons and inverse-image square
comparison to express it as equality of squares between the composite left adjoints.
Take mates of this equality. Compatibility of mates with horizontal and vertical
composition identifies the ordinary component with derivedBaseChangeMap, the tensor
components with derivedHomUpperStarComparison and precomposition by inverse compact
exchange, and the exceptional component with rightDerivedUpperShriekBaseChangeMap.
Conjugation of the two projection components gives exactly the displayed compact
adjunction isomorphisms. Evaluate at Q. No finiteness or dualizability of N or Q is
used, and empty schemes and zero complexes satisfy the same adjunction identities. -/
theorem compactInternalAdjunctionExchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (N : DerivedCategoryModule Λ X)
    (Q : DerivedCategoryModule Λ S) :
    compactInternalAdjunctionExchangeSquare (ModuleCat.{u + 1} Λ)
      (rightDerivedUpperShriekAdjunction Λ f) (rightDerivedUpperShriekAdjunction Λ f')
      sq.toCommSq (rightDerivedLowerShriekBaseChangeMap Λ sq) N Q
      (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq N
  exact compact_exchange_projection (ModuleCat.{u + 1} Λ)
    (rightDerivedUpperShriekAdjunction Λ f) (rightDerivedUpperShriekAdjunction Λ f')
    sq.toCommSq (rightDerivedLowerShriekBaseChangeMap Λ sq) N hlib Q

end AlgebraicGeometry.Etale
