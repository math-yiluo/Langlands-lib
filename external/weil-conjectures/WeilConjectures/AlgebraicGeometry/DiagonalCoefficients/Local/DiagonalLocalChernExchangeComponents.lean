/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRealization
import WeilConjectures.CategoryTheory.Adjunction.ExchangeTransport
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineBundleClassAdditive
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLocalChernLift
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernHorizontalRealization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernBaseFactorization

/-! # Geometric pullback of local Chern adjuncts modulo the base line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor CondensedRing.upperStar CondensedRing.lowerStar
  CompletedRealization.singleUnit CompletedRealization.shiftedLine

private theorem firstChernR_mul (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : SpTowerClasses.Chern l E T) (L M : T.Pic) :
    SpTowerClasses.firstChernR l E c (L * M) =
      SpTowerClasses.firstChernR l E c L + SpTowerClasses.firstChernR l E c M := by
  have := c.reduction.derivedAdjunction.left_adjoint_additive
  simp only [SpTowerClasses.firstChernR, SpTowerClasses.tower_lineBundleClass_mul,
    Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private theorem firstChern_mul (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : SpTowerClasses.Chern l E T) (L M : T.Pic) :
    SpTowerClasses.firstChern l E c (L * M) =
      SpTowerClasses.firstChern l E c L + SpTowerClasses.firstChern l E c M := by
  have := c.scalar.adjunction.left_adjoint_additive
  simp only [SpTowerClasses.firstChern, firstChernR_mul,
    Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private theorem localChern_add (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X)
    (z w : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧) :
    e.localChern l X (z + w) = e.localChern l X z + e.localChern l X w := by
  simp only [CompletedRealization.localChern, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

private theorem exchange_adjunct
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : B ⥤ A} {R : A ⥤ B} {L' : B' ⥤ A'} {R' : A' ⥤ B'}
    {G : B ⥤ B'} {H : A ⥤ A'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (θ : G ⋙ L' ≅ L ⋙ H) {M : B} {K : A} (a : L.obj M ⟶ K) :
    G.map (adj.homEquiv _ _ a) ≫ (Adjunction.exchangeRight adj adj' θ).app K =
      adj'.homEquiv _ _ (θ.hom.app M ≫ H.map a) := by
  let E := Adjunction.exchangeRight adj adj' θ
  have hn := E.naturality a
  change G.map (R.map a) ≫ E.app K = E.app (L.obj M) ≫ R'.map (H.map a) at hn
  rw [Adjunction.homEquiv_unit, G.map_comp, Category.assoc, hn,
    ← Category.assoc, Adjunction.map_unit_comp_exchangeRight_app]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem conjugated_exchange_adjunct
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : B ⥤ A} {R R₀ : A ⥤ B} {L' : B' ⥤ A'} {R' R₀' : A' ⥤ B'}
    {G : B ⥤ B'} {H : A ⥤ A'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (θ : G ⋙ L' ≅ L ⋙ H) (i : R₀ ≅ R) (i' : R₀' ≅ R')
    {M : B} {K : A} {T : A'} (a : L.obj M ⟶ K) (t : H.obj K ⟶ T) :
    G.map (adj.homEquiv _ _ a ≫ i.inv.app K) ≫
        (G.map (i.hom.app K) ≫ (Adjunction.exchangeRight adj adj' θ).app K ≫
          i'.inv.app (H.obj K)) ≫ R₀'.map t =
      adj'.homEquiv _ _ (θ.hom.app M ≫ H.map a ≫ t) ≫ i'.inv.app T := by
  have hi : G.map (i.inv.app K) ≫ G.map (i.hom.app K) = 𝟙 _ := by
    rw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (G.map (i.inv.app K)) (G.map (i.hom.app K)), hi,
    Category.id_comp]
  rw [← i'.inv.naturality t]
  rw [← Category.assoc, ← Category.assoc, exchange_adjunct,
    ← adj'.homEquiv_naturality_right, Category.assoc]

private theorem map_comp_factor
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B V : C} {T : D} (c : A ⟶ B) (γ : B ⟶ V)
    (v : F.obj V ⟶ T) (b : F.obj B ⟶ T)
    (h : b = F.map γ ≫ v) :
    F.map c ≫ b = F.map (c ≫ γ) ≫ v := by
  rw [h, ← Category.assoc, ← F.map_comp]

private theorem adjunct_sum_factor
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R R₀ : D ⥤ C} [L.Additive] (adj : L ⊣ R) (i : R₀ ≅ R)
    {A B V : C} {T : D} (c : A ⟶ B) (γ : B ⟶ V)
    (v : L.obj V ⟶ T) (a : L.obj B ⟶ T) :
    adj.homEquiv _ _ (L.map (c ≫ γ) ≫ v + L.map c ≫ a) ≫ i.inv.app T =
      (c ≫ γ) ≫ (adj.homEquiv _ _ v ≫ i.inv.app T) +
        c ≫ (adj.homEquiv _ _ a ≫ i.inv.app T) := by
  rw [Adjunction.homAddEquiv_add, adj.homEquiv_naturality_left,
    adj.homEquiv_naturality_left]
  simp only [Preadditive.add_comp, Category.assoc]

private theorem exchange_components_finish
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : B ⥤ A} {R R₀ : A ⥤ B} {L' : B' ⥤ A'} {R' R₀' : A' ⥤ B'}
    {G : B ⥤ B'} {H : A ⥤ A'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (θ : G ⋙ L' ≅ L ⋙ H) (i : R₀ ≅ R) (i' : R₀' ≅ R')
    {M : B} {K : A} {T : A'} (a : L.obj M ⟶ K) (t : H.obj K ⟶ T)
    [Preadditive B'] [Preadditive A']
    {B₀ V : B'} {c : G.obj M ⟶ B₀} {γ : B₀ ⟶ V}
    (v : L'.obj V ⟶ T) (a₀ : L'.obj B₀ ⟶ T)
    (hlocal : θ.hom.app M ≫ H.map a ≫ t = L'.map (c ≫ γ) ≫ v + L'.map c ≫ a₀)
    [L'.Additive] :
    G.map (adj.homEquiv _ _ a ≫ i.inv.app K) ≫
        (G.map (i.hom.app K) ≫ (Adjunction.exchangeRight adj adj' θ).app K ≫
          i'.inv.app (H.obj K)) ≫ R₀'.map t =
      (c ≫ γ) ≫ (adj'.homEquiv _ _ v ≫ i'.inv.app T) +
        c ≫ (adj'.homEquiv _ _ a₀ ≫ i'.inv.app T) := by
  rw [conjugated_exchange_adjunct]
  exact (congrArg (fun x ↦ adj'.homEquiv _ _ x ≫ i'.inv.app T) hlocal).trans
    (adjunct_sum_factor (L := L') adj' i' c γ v a₀)

/-- Addition of normalized completed classes realizes multiplication in the Picard group. -/
private theorem completedChern_mul_normalization (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (L K : X.Pic)
    (hK : K = L * Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S))
    (w z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (hw : (diagonalCompletedUnderlying l X).map w ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
        (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
        (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
      p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
        p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map
          (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX L)))
    (hz : ModelLocalChernNormalized l p z) :
    (diagonalCompletedUnderlying l X).map (w + z) ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
        (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
        (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
      p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
        p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map
          (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX K)) := by
  have : p.LX.R.Additive := by
    have := p.LX.triangulated
    infer_instance
  rw [hK, firstChern_mul]
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  exact congrArg₂ (· + ·) hw (by simpa only [ModelLocalChernNormalized] using hz)

/-- A base Picard class has a normalized completed lift factoring through the base line. -/
private theorem localChern_base_lift_factorization (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hunit : IsUnit (l : Γ(S, ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (eX : CompletedRealization l X)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) (M : S.Pic) :
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let V := ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj
      (zlLine l S))⟦(2 : ℤ)⟧
    let T := ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj
      (zlLine l X))⟦(2 : ℤ)⟧
    ∃ (w : DiagonalTrace.completedUnit l X ⟶
        (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
      (γ : unit Λ S ⟶ V) (v : (derivedUpper Λ f).obj V ⟶ T),
      ((diagonalCompletedUnderlying l X).map w ≫
        DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
          (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
          (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
        p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
          p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map
            (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
              (Scheme.Pic.map f M)))) ∧
        cF.derived ≫ eX.localChern l X w = (derivedUpper Λ f).map γ ≫ v := by
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hunit.map f.appTop.hom
  obtain ⟨w, hw, _⟩ := DiagonalTrace.diagonalCompletedLocalChern_lift l p hX
    (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX (Scheme.Pic.map f M))
  obtain ⟨γ, v, hbase⟩ := diagonalLocalChern_base_factorization l f hunit p eX cF M w hw
  exact ⟨w, γ, v, hw, hbase⟩

set_option linter.unusedVariables false in
/-- The pulled local Chern adjunct differs from the new model adjunct by a map
factoring through the shifted integral Tate line on the new base.

Source: diagonal coefficient changes (3), whole-system Kummer naturality and the
projective-line hyperplane calculation.
(blueprint: lem-diagonal-local-chern-exchange-components).

Proof: naturality of the line-bundle extension and its Kummer boundary gives
pullback of the entire Chern system, with its coefficient-one and root comparisons.
Use the supplied Picard factorization of the pulled class as
the new hyperplane plus a base Picard class. Additivity of the whole Kummer system
writes its Chern arrow as the corresponding sum. The completed local
normalizations and full faithfulness on complete objects transport that equality
to completed local arrows. The exact realizations, their underlying-sheaf
normalizations and the fixed root comparison identify the local pullback maps.
Take adjuncts. The mate identity turns the base term into its base Chern arrow
followed by the twisted unit, and turns the relative term into the new local
adjunct preceded by the normalized base-unit endpoint. Transport through the
canonical functor equalities. These operations give the asserted factorization;
no trace or invertibility of exchange is assumed or used. -/
theorem diagonalLocalChern_exchange_components (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian X'] [IsNoetherian S']
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (hunit : IsUnit (l : Γ(S, ⊤))) (hunit' : IsUnit (l : Γ(S', ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (p' : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f')
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (D' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f'))
    (canonical' : D'.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (hcanonical' : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f') D' canonical')
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (cF' : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS)
    (hPic : ∃ M : S'.Pic,
      Scheme.Pic.map hX
          (Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S)) =
        Scheme.Pic.map f' M *
          Scheme.Pic.map p'.model.model.hom (SpTowerClasses.hyperplanePic S'))
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (z' : DiagonalTrace.completedUnit l X' ⟶
      (DiagonalTrace.completedLine l X')⟦(2 : ℤ)⟧)
    (hz : ModelLocalChernNormalized l p z) (hz' : ModelLocalChernNormalized l p' z') :
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let V := ((DerivedCategory.singleFunctor (Modules Λ S') 0).obj
      (zlLine l S'))⟦(2 : ℤ)⟧
    let T := ((DerivedCategory.singleFunctor (Modules Λ X') 0).obj
      (zlLine l X'))⟦(2 : ℤ)⟧
    ∃ (β : (derivedUpper Λ hS).obj (unit Λ S) ⟶ V) (u : V ⟶ D'.R.obj T),
      (derivedUpper Λ hS).map
          (modelLocalAdjunct Λ f D canonical cF (eX.localChern l X z)) ≫
          modelExchange Λ f f' hX hS h D D' canonical canonical' _ ≫
          D'.R.map line.shift =
        β ≫ u + c.derived ≫
          modelLocalAdjunct Λ f' D' canonical' cF' (eX'.localChern l X' z') := by
  let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
  let L' := derivedUpper Λ f'
  let θ := (CondensedRing.leftDerivedUpperStarComp Λ f' hS).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr Λ h) ≪≫
    CondensedRing.leftDerivedUpperStarComp Λ hX f
  let adj := CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
  let adj' := CondensedRing.derivedUpperStarLowerStarAdjunction Λ f'
  have : L'.Additive := adj'.left_adjoint_additive
  obtain ⟨M, hM⟩ := hPic
  obtain ⟨w, γ, v, hw, hbase⟩ :=
    localChern_base_lift_factorization l f' hunit' p' eX' cF' M
  have hsum := completedChern_mul_normalization l p' _ _ hM w z' hw hz'
  have hpull := diagonalLocalChern_horizontal_realization l f f' hX hS h
    hunit hunit' p p' eX eX' cF cF' line c z (w + z') hz hsum
  have hlocal : θ.hom.app (unit Λ S) ≫
      (derivedUpper Λ hX).map (cF.derived ≫ eX.localChern l X z) ≫ line.shift =
      L'.map (c.derived ≫ γ) ≫ v +
        L'.map c.derived ≫ (cF'.derived ≫ eX'.localChern l X' z') := by
    calc
      _ = L'.map c.derived ≫ cF'.derived ≫ eX'.localChern l X' (w + z') := hpull
      _ = L'.map c.derived ≫ (cF'.derived ≫ eX'.localChern l X' w) +
          L'.map c.derived ≫ (cF'.derived ≫ eX'.localChern l X' z') := by
        rw [localChern_add]
        simp only [Preadditive.comp_add]
      _ = _ := by
        apply congrArg (fun x ↦ x + L'.map c.derived ≫
          (cF'.derived ≫ eX'.localChern l X' z'))
        exact map_comp_factor L' c.derived γ v _ hbase
  refine ⟨c.derived ≫ γ, adj'.homEquiv _ _ v ≫ (eqToIso canonical').inv.app _, ?_⟩
  unfold modelLocalAdjunct modelExchange derivedExchange
  apply exchange_components_finish (c := c.derived) (γ := γ)
    adj adj' θ (eqToIso canonical) (eqToIso canonical')
    (cF.derived ≫ eX.localChern l X z) line.shift v
    (cF'.derived ≫ eX'.localChern l X' z') hlocal

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
