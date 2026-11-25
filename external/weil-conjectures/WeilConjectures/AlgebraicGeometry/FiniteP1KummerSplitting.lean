/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerNaturality
import WeilConjectures.AlgebraicGeometry.FiniteP1NoetherianBase
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN

/-! # The two-component Kummer map and its arbitrary-base naturality

the universal-base argument of lem-sp-tower-p1-arbitrary-base-integrals, steps 1–4.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

private lemma mate_whiskerTop
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H : B ⥤ D}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : B) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : A ⥤ C} {H H' : B ⥤ D}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : B) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

-- Transporting either adjunction conjugates the mate by isomorphisms of right adjoints.
private lemma isIso_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    {L₁' : A ⥤ B} {R₁' : B ⥤ A} {L₂' : C ⥤ D} {R₂' : D ⥤ C}
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (eG : G' ≅ G) (eH : H ≅ H')
    (α : TwoSquare G L₁ L₂ H) (K : B) :
    IsIso ((mateEquiv adj₁' adj₂'
      ((((α.whiskerTop eG.hom).whiskerBottom eH.hom).whiskerRight e₂.inv).whiskerLeft
        e₁.hom)).app K) ↔ IsIso ((mateEquiv adj₁ adj₂ α).app K) := by
  rw [conjugateEquiv_mateEquiv_vcomp adj₁' adj₁ adj₂',
    mateEquiv_conjugateEquiv_vcomp adj₁ adj₂ adj₂']
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    isIso_comp_left_iff, isIso_comp_right_iff]
  rw [mate_whiskerBottom, mate_whiskerTop]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport projectiveLineTraceDatum

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- Only invertibility is needed, so arbitrary adjunctions on the two isomorphic left
-- adjoints suffice: the conjugate right-adjoint comparisons are automatically invertible.
private theorem finiteP1_isIso_derived_exchange_iff_exact
    (Λ : Type (u + 1)) [CommRing Λ] (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K) ↔
      IsIso ((Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K) := by
  let A := ModuleCat.{u + 1} Λ
  let α := TwoSquare.mk _ _ _ _ (Etale.exactDerivedSquareUpperStarIso A sq).hom
  have h := isIso_mate_transport
    (Etale.mapDerivedUpperStarLowerStarAdjunction A f)
    (Etale.mapDerivedUpperStarLowerStarAdjunction A f')
    (Etale.derivedUpperStarLowerStarAdjunction A f)
    (Etale.derivedUpperStarLowerStarAdjunction A f')
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f).symm
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f').symm
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g').symm α K
  have hs :
      ((((α.whiskerTop (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g).hom).whiskerBottom
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g').inv).whiskerRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f').hom).whiskerLeft
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f).inv) =
      TwoSquare.mk _ _ _ _ (Etale.derivedSquareUpperStarIso A sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [Etale.derivedSquareUpperStarIso, Etale.leftDerivedUpperStarComp,
      Etale.exactDerivedSquareUpperStarIso, Etale.squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      Etale.leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (Etale.upperStar A g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  rw [hs] at h
  exact h

-- The mate-transport proof below follows UnboundedCoefficientForgetfulAux.
private theorem finiteP1_isIso_exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (ProjectiveLine S)) :
    IsIso (C := DerivedCategoryModule A S') (ordinaryFiniteP1Exchange A f M) := by
  let sq := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f
  have hunit : N • (1 : A) = 0 := by simpa only [nsmul_eq_mul, mul_one] using hA
  have hproper : IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq) := by
    have h (K) : IsIso (C := DerivedCategoryModule A S')
        ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K) :=
      isIso_derivedBaseChangeMap_of_isIso_modN A N hunit sq
        (isIso_derivedBaseChangeMap_of_isProper_modN N hN sq) K
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (C := DerivedCategoryModule A S')
      ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M) :=
    (finiteP1_isIso_derived_exchange_iff_exact A sq.toCommSq M).mp inferInstance
  unfold ordinaryFiniteP1Exchange
  infer_instance

private theorem isIso_biprod_lift_map
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {X' Y' : D}
    (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') :
    IsIso (biprod.lift (F.map (biprod.fst : X ⊞ Y ⟶ X) ≫ e₁.hom)
      (F.map (biprod.snd : X ⊞ Y ⟶ Y) ≫ e₂.hom)) := by
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  let e := F.mapBiprod X Y ≪≫ biprod.mapIso e₁ e₂
  have he : e.hom = biprod.lift (F.map (biprod.fst : X ⊞ Y ⟶ X) ≫ e₁.hom)
      (F.map (biprod.snd : X ⊞ Y ⟶ Y) ≫ e₂.hom) := by
    apply biprod.hom_ext
    · simp only [e, Iso.trans_hom, Category.assoc, biprod.mapIso_hom,
        biprod.map_fst, Functor.mapBiprod_hom, biprod.lift_fst_assoc, biprod.lift_fst]
    · simp only [e, Iso.trans_hom, Category.assoc, biprod.mapIso_hom,
        biprod.map_snd, Functor.mapBiprod_hom, biprod.lift_snd_assoc, biprod.lift_snd]
  rw [← he]
  infer_instance

private theorem finiteP1_isIso_sourceMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (C := DerivedCategoryModule A S')
      (ordinaryFiniteP1DecompositionSourceMap A N hA t f hS) := by
  have : (ordinaryFinitePullback A (X := S') (Y := S) f).Additive := Functor.additive_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm
  unfold ordinaryFiniteP1DecompositionSourceMap
  exact isIso_biprod_lift_map (ordinaryFinitePullback A (X := S') (Y := S) f)
    (X := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
    (Y := ordinaryFiniteUnit A S)
    (ordinaryFiniteShiftedLinePullback A N hA t f hS) (ordinaryFiniteUnitPullback A f)

/-- The canonical Kummer maps are invertible and commute with every base change.
Only the two-component maps occur here; neither traces nor diagonal classes occur.
lem-sp-tower-p1-arbitrary-base-integrals, proof steps 1–4.
(auxiliary; not a blueprint node)

Proof: put U = Spec Z[1/N], using finiteP1_exists_noetherianBase. Its normalized datum
is projectiveLineTraceDatum. The hyperplane has equation t on one standard chart and
is empty on the other, so it is Cartier over every base and its ideal dual is O(1).
The scalar Kummer boundary of this line has a unique module-derived realization:
module cohomology of the constant free rank-one source equals underlying abelian
cohomology. Define c at every base by this realization. The supported Kummer pullback
formula applied to the hyperplane, followed by its constant unit, shows that c pulls
back to c at the new base. The unit component satisfies the exchange-mate unit identity;
taking adjoints of the Chern pullback equation gives the second component identity.
Biproduct extensionality gives the displayed square. Proper torsion exchange, twist
transport, and additive preservation of the biproduct source are isomorphisms. Apply
the square to S -> U: the upper two-component map is the isomorphism of the normalized
Noetherian datum, so the lower map is invertible. This applies to every S, and the
component square already holds for every map between arbitrary bases. The zero ring,
N = 1 and the empty base give the same identities of their unique arrows. -/
theorem exists_ordinaryFiniteP1SplittingMap (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ c : ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
        ordinaryFiniteUnit A (ProjectiveLine S) ⟶
          (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
      (∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ordinaryFiniteP1ChernSpec A N hA S
          ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom) (c S hS) ∧
        IsIso (C := DerivedCategoryModule A S) (ordinaryFiniteP1SplittingMap A N hA
          (projectiveLineTraceTransport N hN A hA) S hS (c S hS))) ∧
      ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
          (hS' : IsUnit (N : Γ(S', ⊤))),
        (ordinaryFinitePullback A (X := S') (Y := S) f).map (ordinaryFiniteP1SplittingMap A N hA
            (projectiveLineTraceTransport N hN A hA) S hS (c S hS)) ≫
          ordinaryFiniteP1Exchange A f
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
          (ordinaryFinitePushforward A (X := ProjectiveLine S') (Y := S')
            (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteShiftedLinePullback A N hA
              (projectiveLineTraceTransport N hN A hA)
              (X := ProjectiveLine S') (Y := ProjectiveLine S)
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
                hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
        ordinaryFiniteP1DecompositionSourceMap A N hA
            (projectiveLineTraceTransport N hN A hA) f hS ≫
          ordinaryFiniteP1SplittingMap A N hA
            (projectiveLineTraceTransport N hN A hA) S' hS' (c S' hS') := by
  classical
  obtain ⟨c, hc, hbc⟩ := exists_ordinaryFiniteP1KummerNaturality N hN A hA
  refine ⟨c, ?_, hbc⟩
  intro S hS
  refine ⟨(hc S hS).1, ?_⟩
  obtain ⟨U, hU, hNU, hmap⟩ := AlgebraicGeometry.finiteP1_exists_noetherianBase N
  let := hU
  obtain ⟨f⟩ := hmap S hS
  have hu : IsIso (C := DerivedCategoryModule A U) (ordinaryFiniteP1SplittingMap A N hA
      (projectiveLineTraceTransport N hN A hA) U hNU (c U hNU)) := by
    rw [(hc U hNU).2]
    rw [ordinaryFiniteP1SplittingMap,
      ← (projectiveLineTraceDatum N hN A hA U hNU).decomposition_hom]
    exact (projectiveLineTraceDatum N hN A hA U hNU).decomposition.isIso_hom
  have hex := finiteP1_isIso_exchange A N hN hA f
    ((ordinaryFiniteLine A N hA (ProjectiveLine U))⟦(2 : ℤ)⟧)
  have hsource := finiteP1_isIso_sourceMap A N hA
    (projectiveLineTraceTransport N hN A hA) f hNU
  have hsq := hbc f hNU hS
  have hiso : IsIso (C := DerivedCategoryModule A S)
      ((ordinaryFinitePullback A (X := S) (Y := U) f).map
      (ordinaryFiniteP1SplittingMap A N hA
        (projectiveLineTraceTransport N hN A hA) U hNU (c U hNU)) ≫
      ordinaryFiniteP1Exchange A f
        ((ordinaryFiniteLine A N hA (ProjectiveLine U))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (X := ProjectiveLine S) (Y := S)
          (ProjectiveLine S ↘ S)).map
        (ordinaryFiniteShiftedLinePullback A N hA
          (projectiveLineTraceTransport N hN A hA)
          (X := ProjectiveLine S) (Y := ProjectiveLine U)
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          ((map_natCast (ProjectiveLine U ↘ U).appTop.hom N) ▸
            hNU.map (ProjectiveLine U ↘ U).appTop.hom)).hom) := by infer_instance
  rw [hsq] at hiso
  exact (isIso_comp_left_iff _ _).mp hiso

end AlgebraicGeometry.Etale
