/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientPullbackEncoding
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange

/-! # Finite coefficient encoding of the canonical exchange mate

This is the change of presentation of the exchange arrow. It requires neither
properness nor boundedness, and asserts no invertibility of the exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

attribute [local irreducible] coefficientEncoding Encoding.fixedDerived Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CondensedRing.upperStar CondensedRing.lowerStar ProEtale.upperStar ProEtale.lowerStar
  CondensedRing.derivedUpperStarLowerStarAdjunction ProEtale.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp ProEtale.leftDerivedUpperStarComp
  ProEtale.derivedBaseChangeMap

private theorem mappedCompositionSquare
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C₀ D₀ : C} {A' B' C' D' : D}
    (r₁ : A ≅ B) (r₂ : C₀ ≅ D₀) (e : A ≅ C₀)
    (s₁ : A' ≅ B') (s₂ : C' ≅ D') (e' : A' ≅ C')
    (a₀ : F.obj A ⟶ A') (a₁ : F.obj C₀ ⟶ C')
    (β₁ : F.obj B ⟶ B') (β₂ : F.obj D₀ ⟶ D')
    (h₁ : F.map r₁.hom ≫ β₁ = a₀ ≫ s₁.hom)
    (h₂ : F.map r₂.hom ≫ β₂ = a₁ ≫ s₂.hom)
    (he : F.map e.hom ≫ a₁ = a₀ ≫ e'.hom) :
    F.map (r₁.inv ≫ e.hom ≫ r₂.hom) ≫ β₂ =
      β₁ ≫ s₁.inv ≫ e'.hom ≫ s₂.hom := by
  have h := Adjunction.composition_square_aux (F.mapIso r₁) (F.mapIso r₂)
    (F.mapIso e) s₁ s₂ e' a₀ a₁ β₁ β₂ h₁ h₂ he
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc] using h

private theorem exchangeArrowIso
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {U : C₁ ⥤ C₂} {R₀ : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
    {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
    (a : U ⊣ R₀) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    [T₁.IsEquivalence] [T₂.IsEquivalence] [T₃.IsEquivalence] [T₄.IsEquivalence]
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He)
    (hcube : ∀ M, Adjunction.coefficientPullbackSquare
      θ θe αU αV αG.hom αH.hom M)
    (K : C₂) (B : R₀ ⋙ G ⟶ H ⋙ S) (Be : Re ⋙ Ge ⟶ He ⋙ Se)
    (hB : B = (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)))
    (hBe : Be = (mateEquiv ae be (TwoSquare.mk _ _ _ _ θe))) :
    Nonempty (Arrow.mk (T₃.map (B.app K)) ≅ Arrow.mk (Be.app (T₂.obj K))) := by
  subst B Be
  let δ := (mateEquiv a ae αU.inv)
  let δ' := (mateEquiv b be αV.inv)
  have : IsIso δ := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful a ae T₁ T₂ αU.symm
  have : IsIso δ' := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful b be T₃ T₄ αV.symm
  let source := αG.app (R₀.obj K) ≪≫ Ge.mapIso (asIso (δ.app K))
  let target := asIso (δ'.app (H.obj K)) ≪≫ Se.mapIso (αH.app K)
  refine ⟨Arrow.isoMk source target ?_⟩
  have h := Adjunction.coefficient_exchange_of_counit_at a b ae be θ θe K
    ((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).app K)
    ((mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).app (T₂.obj K))
    (mateEquiv_counit a b (TwoSquare.mk _ _ _ _ θ) K)
    (mateEquiv_counit ae be (TwoSquare.mk _ _ _ _ θe) (T₂.obj K))
    αU αV αG.hom αH.hom (δ.app K) (δ'.app (H.obj K))
    (mateEquiv_counit a ae αU.inv K) (mateEquiv_counit b be αV.inv (H.obj K)) (hcube _)
  simpa only [source, target, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    asIso_hom, Arrow.mk_hom, Category.assoc] using h

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

omit [Finite A] [DiscreteTopology A] in
private theorem encoding_congr
    (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) (P : CoefficientPullback.Family A R e E)
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))) :
    (coefficientEncoding A e X (E X)).map
        ((CondensedRing.finitePullbackCongr R w).hom.app M) ≫
      (P g).hom.app M =
    (P f).hom.app M ≫
      (ProEtale.leftDerivedUpperStarCongr
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) w).hom.app
          ((coefficientEncoding A e Y (E Y)).obj M) := by
  subst g
  simp

/-- Normalized coefficient encoding identifies the actual exchange arrows.

Source: blueprint sk-thm-sfb-proper-base-change-finite.proof.md, steps 1 and 5;
lem-sfb-finite-coefficient-derived-exchange-identification, proof steps 1--5;
Stacks Tags 03D3, 07A7 and 09C8.
(blueprint: lem-sfb-finite-coefficient-exchange-encoding).

Proof:
1. Restriction along the inverse coefficient isomorphism is exact and preserves the
underlying section groups. The normalized section-action encoding has the same property.
Both direct images evaluate a module on the same fibre product, so the resulting
underived direct-image comparison is the identity on sections and commutes with composition.
2. Conjugate the two geometric adjunctions by these exact equivalences. Uniqueness of
left adjoints gives pullback comparisons satisfying the unit and counit equations.
The identity-on-sections composition equation identifies their pullback compositors.
3. Compute total direct images on K-injective resolutions. The exact equivalences
and their exact inverses preserve K-injectives. Localization of step 1 gives derived
direct-image comparisons; localization of the adjunction equations gives the compatible
derived pullback comparisons, with the specified derived compositors.
4. Expand the internal exchange as unit, pullback square, counit. Substitute these
three comparison equations. Naturality moves the coefficient comparisons past each factor;
inverse comparisons cancel. The remaining composite is the ordinary exchange.
The source and target comparison isomorphisms therefore form the asserted arrow
isomorphism. This argument is on arbitrary schemes and unbounded complexes; no qcqs
or etale-origin hypothesis is used. -/
theorem finiteCoefficientExchangeEncoding
    (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X))) :
    Nonempty (Arrow.mk ((coefficientEncoding A e Y' (E Y')).map
        ((CondensedRing.finiteProperExchange R sq.toCommSq).app K)) ≅
      Arrow.mk ((ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app
          ((coefficientEncoding A e X (E X)).obj K))) := by
  classical
  let h₁ : (coefficientEncoding A e Y (E Y)).IsEquivalence :=
    coefficientEncoding_isEquivalence A e Y (E Y)
  let h₂ : (coefficientEncoding A e X (E X)).IsEquivalence :=
    coefficientEncoding_isEquivalence A e X (E X)
  let h₃ : (coefficientEncoding A e Y' (E Y')).IsEquivalence :=
    coefficientEncoding_isEquivalence A e Y' (E Y')
  let h₄ : (coefficientEncoding A e X' (E X')).IsEquivalence :=
    coefficientEncoding_isEquivalence A e X' (E X')
  obtain ⟨P, hP⟩ := CoefficientPullback.finiteCoefficientPullbackEncoding A R e E
  let F (T : Scheme.{u}) := coefficientEncoding A e T (E T)
  let I {U V : Scheme.{u}} (h : U ⟶ V) := CoefficientPullback.pull R h
  let O {U V : Scheme.{u}} (h : U ⟶ V) := CoefficientPullback.fixedPull A h
  let θ := (CondensedRing.finitePullbackSquare R sq.toCommSq).hom
  let θ' := (ProEtale.leftDerivedUpperStarSquareIso
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).hom
  have hcube (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))) :
      (F X').map (θ.app M) ≫ (P g').hom.app ((I p).obj M) ≫
        (O g').map ((P p).hom.app M) =
      (P p').hom.app ((I g).obj M) ≫
        (O p').map ((P g).hom.app M) ≫ θ'.app ((F Y).obj M) := by
    dsimp only [θ]
    unfold CondensedRing.finitePullbackSquare
    have hc := (@mappedCompositionSquare _ _
      (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)) (F X')
      ((CondensedRing.leftDerivedUpperStarComp R p' g).app M)
      ((CondensedRing.leftDerivedUpperStarComp R g' p).app M)
      ((CondensedRing.finitePullbackCongr R sq.toCommSq.w.symm).app M)
      ((ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p' g).app ((F Y).obj M))
      ((ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g' p).app ((F Y).obj M))
      ((ProEtale.leftDerivedUpperStarCongr
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq.w.symm).app ((F Y).obj M))
      ((P (p' ≫ g)).hom.app M) ((P (g' ≫ p)).hom.app M)
      ((P p').hom.app ((I g).obj M) ≫ (O p').map ((P g).hom.app M))
      ((P g').hom.app ((I p).obj M) ≫ (O g').map ((P p).hom.app M))
      (hP p' g M) (hP g' p M) (encoding_congr A e E P sq.toCommSq.w.symm M)
    simpa only [θ', ProEtale.leftDerivedUpperStarSquareIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Category.assoc] using hc
  apply (@exchangeArrowIso
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y)))
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1})
      (condensedRingObj R Y')))
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj R X')))
    (DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (DerivedCategory (Sheaf (Scheme.ProEt.topology Y')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X')
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _))
    (CondensedRing.derivedUpperStarLowerStarAdjunction R p)
    (CondensedRing.derivedUpperStarLowerStarAdjunction R p')
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p')
    (U := I p) (R₀ := (CondensedRing.lowerStar R p).rightDerivedFunctor)
    (V := I p') (S := (CondensedRing.lowerStar R p').rightDerivedFunctor)
    (Ue := O p) (Re := (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor)
    (Ve := O p') (Se := (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p').rightDerivedFunctor)
    (G := I g) (H := I g') (Ge := O g) (He := O g')
    (T₁ := F Y) (T₂ := F X) (T₃ := F Y') (T₄ := F X')
    θ θ' (P p) (P p') (P g) (P g') hcube K
    (CondensedRing.finiteProperExchange R sq.toCommSq)
    (ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq)
    (CondensedRing.finiteProperExchange_eq_mate R sq.toCommSq)
    (by unfold ProEtale.derivedBaseChangeMap; rfl)

/-- Invertibility can be checked after the canonical coefficient encoding.
This is a consequence of the arrow comparison and reflection by an equivalence.
(blueprint: lem-sfb-finite-coefficient-exchange-encoding). -/
theorem finiteCoefficientExchangeEncoding_isIso
    (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X))) :
    IsIso ((CondensedRing.finiteProperExchange R sq.toCommSq).app K) ↔
      IsIso ((ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app
          ((coefficientEncoding A e X (E X)).obj K)) := by
  classical
  let F := coefficientEncoding A e Y' (E Y')
  let α := (CondensedRing.finiteProperExchange R sq.toCommSq).app K
  let comparison := (finiteCoefficientExchangeEncoding A e E sq K).some
  exact (isIso_iff_of_reflects_iso α F).symm.trans
    (Arrow.isIso_iff_isIso_of_isIso comparison.hom)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
