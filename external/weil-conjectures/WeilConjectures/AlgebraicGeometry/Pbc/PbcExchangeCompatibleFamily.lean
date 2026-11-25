/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces
import all WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
import WeilConjectures.AlgebraicGeometry.Pbc.PbcExchangeStageSquare

/-! # Scalar compatibility of the actual finite-stage exchange
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable (X Y X' Y' : Scheme.{u})
  [IsNoetherian X]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [IsNoetherian Y]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [IsNoetherian X']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [IsNoetherian Y']
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]

@[irreducible] private def conjugateNatTrans {A B : Type*}
    [Category A] [Category B] {F F' G G' : A ⥤ B}
    (eF : F = F') (eG : G = G') (η : F' ⟶ G') : F ⟶ G :=
  eqToHom eF ≫ η ≫ eqToHom eG.symm

private theorem conjugateNatTrans_app_heq {A B : Type*}
    [Category A] [Category B] {F F' G G' : A ⥤ B}
    (eF : F = F') (eG : G = G') (η : F' ⟶ G') (K : A) :
    HEq ((conjugateNatTrans eF eG η).app K) (η.app K) := by
  subst F'
  subst G'
  unfold conjugateNatTrans
  simp

private def transportSquareNat
    (R : Type*) [CommRing R] (q : R)
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [Linear R A] [Linear R B] [Linear R C] [Linear R D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [F.Linear R] [G.Linear R] [H.Linear R] [I.Linear R]
    (η : F ⋙ G ⟶ H ⋙ I) :
    ScalarLocalization.transport R q F ⋙ ScalarLocalization.transport R q G ⟶
      ScalarLocalization.transport R q H ⋙ ScalarLocalization.transport R q I :=
  conjugateNatTrans (ScalarLocalization.transport_comp R q F G)
    (ScalarLocalization.transport_comp R q H I) (ScalarLocalization.transportNat R q η)

private theorem transportSquareNat_app
    (R : Type*) [CommRing R] (q : R)
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [Linear R A] [Linear R B] [Linear R C] [Linear R D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [F.Linear R] [G.Linear R] [H.Linear R] [I.Linear R]
    (η : F ⋙ G ⟶ H ⋙ I) (K : A) :
    HEq ((transportSquareNat R q F G H I η).app ⟨K⟩)
      ((ScalarLocalization.localization R D q).map (η.app K)) := by
  exact conjugateNatTrans_app_heq
    (ScalarLocalization.transport_comp R q F G)
    (ScalarLocalization.transport_comp R q H I)
    (ScalarLocalization.transportNat R q η) (ScalarLocalization.mk K)

private def restrictSquareNat
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : ObjectProperty A) (Q : ObjectProperty B)
    (S : ObjectProperty C) (T : ObjectProperty D)
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (hF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, T (G.obj K.obj))
    (hH : ∀ K : P.FullSubcategory, S (H.obj K.obj))
    (hI : ∀ K : S.FullSubcategory, T (I.obj K.obj))
    (η : F ⋙ G ⟶ H ⋙ I) :
    Q.lift (P.ι ⋙ F) hF ⋙ T.lift (Q.ι ⋙ G) hG ⟶
      S.lift (P.ι ⋙ H) hH ⋙ T.lift (S.ι ⋙ I) hI where
  app K := ObjectProperty.homMk (η.app K.obj)
  naturality K L m := by
    apply ObjectProperty.hom_ext
    exact η.naturality m.hom

private theorem conditionalSquareNat_exists
    {V W V' W' : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (q : A)
    (F : PbcCompletedDerived V d ⥤ PbcCompletedDerived W d)
    (G : PbcCompletedDerived W d ⥤ PbcCompletedDerived W' d)
    (H : PbcCompletedDerived V d ⥤ PbcCompletedDerived V' d)
    (I : PbcCompletedDerived V' d ⥤ PbcCompletedDerived W' d)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [F.Linear A] [G.Linear A] [H.Linear A] [I.Linear A]
    (hF : ∀ K : PbcBoundedConstructibleComplete V d,
      PbcIsBoundedConstructibleComplete W d (F.obj K.obj))
    (hG : ∀ K : PbcBoundedConstructibleComplete W d,
      PbcIsBoundedConstructibleComplete W' d (G.obj K.obj))
    (hH : ∀ K : PbcBoundedConstructibleComplete V d,
      PbcIsBoundedConstructibleComplete V' d (H.obj K.obj))
    (hI : ∀ K : PbcBoundedConstructibleComplete V' d,
      PbcIsBoundedConstructibleComplete W' d (I.obj K.obj))
    (η : F ⋙ G ⟶ H ⋙ I) :
    ∃ σ : pbcConditionalRational d F hF q ⋙ pbcConditionalRational d G hG q ⟶
      pbcConditionalRational d H hH q ⋙ pbcConditionalRational d I hI q,
      ∀ K : PbcBoundedConstructibleComplete V d,
        HEq (σ.app (ScalarLocalization.mk K))
          ((pbcRationalization W' d q).map
            (ObjectProperty.homMk
              (X := (pbcConditionalIntegral d G hG).obj
                ((pbcConditionalIntegral d F hF).obj K))
              (Y := (pbcConditionalIntegral d I hI).obj
                ((pbcConditionalIntegral d H hH).obj K)) (η.app K.obj))) := by
  let RF := pbcConditionalIntegral d F hF
  let RG := pbcConditionalIntegral d G hG
  let RH := pbcConditionalIntegral d H hH
  let RI := pbcConditionalIntegral d I hI
  let ε : RF ⋙ RG ⟶ RH ⋙ RI :=
    restrictSquareNat _ _ _ _ F G H I hF hG hH hI η
  refine ⟨transportSquareNat A q RF RG RH RI ε, ?_⟩
  intro K
  exact transportSquareNat_app A q RF RG RH RI ε K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsAlgClosure ℚ_[l] Ω]
  [IsNoetherian X] dX iX [IsNoetherian Y] dY iY
  [IsNoetherian X'] dX' iX' [IsNoetherian Y'] dY' iY' in
private theorem stageExchange_exists
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g' f' f g)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X' E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    ∃ σ : pbcDescentDirectImage l Ω f presRf E ⋙ pbcDescentPullback l Ω g presLg E ⟶
        pbcDescentPullback l Ω g' presLg' E ⋙ pbcDescentDirectImage l Ω f' presRf' E,
      ∀ K : pbcIntegralStage l Ω X E,
        HEq (σ.app (ScalarLocalization.mk K))
      ((pbcStageLocalization l Ω Y' E).map
        (ObjectProperty.homMk
          (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
              ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
          (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
              ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
          ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app K.obj))) := by
  exact conditionalSquareNat_exists
    (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E))
    (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E))
    (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E))
    (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E))
    (presRf E) (presLg E) (presLg' E) (presRf' E)
    (pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical exchange is a compatible transformation of the composite
stage families once their comparisons have the canonical normalization. This
asserts finite-stage compatibility only; it does not construct descended functors. -/
theorem pbcExchangeCompatibleFamily
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g' f' f g)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X' E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (Rf' : StageSystem.Morphism (pbcScalarSystem l Ω X' dX'.out iX'.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg' : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω X' dX'.out iX'.out))
    (hRf : ∀ E, Rf.Φ E = pbcDescentDirectImage l Ω f presRf E)
    (hRf' : ∀ E, Rf'.Φ E = pbcDescentDirectImage l Ω f' presRf' E)
    (hLg : ∀ E, Lg.Φ E = pbcDescentPullback l Ω g presLg E)
    (hLg' : ∀ E, Lg'.Φ E = pbcDescentPullback l Ω g' presLg' E)
    (bRf : PbcDirectImageBetaSpec l Ω f presRf Rf)
    (bRf' : PbcDirectImageBetaSpec l Ω f' presRf' Rf')
    (bLg : PbcPullbackBetaSpec l Ω g presLg Lg)
    (bLg' : PbcPullbackBetaSpec l Ω g' presLg' Lg') :
    ∃ Ex : StageSystem.Morphism.Hom (Rf.comp Lg)
          (Lg'.comp Rf'),
        (∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : pbcIntegralStage l Ω X E),
          HEq ((Ex.τ E).app (ScalarLocalization.mk K))
            ((pbcStageLocalization l Ω Y' E).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
                (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
                ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app
                  K.obj)))) := by
  classical
  have hσ (E : Padic.FiniteCoefficientFields l Ω) :=
    stageExchange_exists l Ω X Y X' Y' f f' g g' sq presRf presRf' presLg presLg' E
  let σ (E : Padic.FiniteCoefficientFields l Ω) := (hσ E).choose
  let τ (E : Padic.FiniteCoefficientFields l Ω) :
      (Rf.comp Lg).Φ E ⟶ (Lg'.comp Rf').Φ E :=
    conjugateNatTrans (congrArg₂ (fun a b ↦ a ⋙ b) (hRf E) (hLg E))
      (congrArg₂ (fun a b ↦ a ⋙ b) (hLg' E) (hRf' E)) (σ E)
  have hτ : ∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : pbcIntegralStage l Ω X E),
          HEq ((τ E).app (ScalarLocalization.mk K))
            ((pbcStageLocalization l Ω Y' E).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
                (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
                ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app
                  K.obj))) := by
    intro E K
    exact (conjugateNatTrans_app_heq _ _ (σ E) (ScalarLocalization.mk K)).trans
      ((hσ E).choose_spec K)
  let Ex : StageSystem.Morphism.Hom (Rf.comp Lg) (Lg'.comp Rf') :=
    { τ := τ
      comm := pbcExchangeStageSquare l Ω X Y X' Y' f f' g g' sq
        presRf presRf' presLg presLg' Rf Rf' Lg Lg'
        hRf hRf' hLg hLg' bRf bRf' bLg bLg' τ hτ }
  exact ⟨Ex, hτ⟩

end AlgebraicGeometry.Scheme
