/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SignedSheafDualCoefficientMap
public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeCoefficientComparisons
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Finite-free affine signed dual coefficient square

Source: Stacks Project, Tag 0BQZ and Tag 01HV. -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_dual_iso_of_components
    {A : Type u} [CommRing A] {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    (T : ModuleCat.{u} A ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (hT : T.Additive)
    (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (N : ModuleCat.{u} A)
    (p : ∀ q : ℕ,
      ModuleCat.ofHom ((-1 : A) ^ (q + 1) • Linear.leftComp A N (K.d (q + 1) q)) ≫
      ModuleCat.ofHom ((-1 : A) ^ (q + 1 + 1) •
        Linear.leftComp A N (K.d (q + 1 + 1) (q + 1))) = 0)
    (O : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (e0 : ∀ q : ℕ, SheafOfModules.homObj (R := R) (T.obj (K.X q)) O ≅
      T.obj (ModuleCat.of A (K.X q ⟶ N)))
    (h0 : ∀ q : ℕ,
      SheafOfModules.homObjMap (R := R) (T.map (K.d (q + 1) q)) (𝟙 O) ≫
        (e0 (q + 1)).hom = (e0 q).hom ≫
          T.map (ModuleCat.ofHom (Linear.leftComp A N
            (K.d (q + 1) q)))) :
    let B := CochainComplex.of
      (fun q ↦ ModuleCat.of A (K.X q ⟶ N))
      (fun q ↦ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
        Linear.leftComp A N (K.d (q + 1) q))) p
    ∃ b : signedSheafDualComplex (R := R)
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat)) O ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (B.extend ComplexShape.embeddingUpNat),
      ∀ q : ℕ, b.hom.f (q : ℤ) =
        ((SheafOfModules.homFunctor R).flip.obj O).map
          (T.map (K.extendXIso ComplexShape.embeddingDownNat (i := q) rfl).inv).op ≫
        (e0 q).hom ≫
        T.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv := by
  classical
  let L := K.extend ComplexShape.embeddingDownNat
  let B := CochainComplex.of
    (fun q ↦ ModuleCat.of A (K.X q ⟶ N))
    (fun q ↦ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
      Linear.leftComp A N (K.d (q + 1) q)))
    p
  let D := B.extend ComplexShape.embeddingUpNat
  let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let F := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj D
  let H := (SheafOfModules.homFunctor R).flip.obj O
  let a (q : ℕ) : L.X (-(q : ℤ)) ≅ K.X q :=
    K.extendXIso ComplexShape.embeddingDownNat rfl
  let c (q : ℕ) : D.X (q : ℤ) ≅
      ModuleCat.of A (K.X q ⟶ N) :=
    B.extendXIso ComplexShape.embeddingUpNat rfl
  let ep (q : ℕ) : (signedSheafDualComplex (R := R)
      E O).X (q : ℤ) ≅ F.X (q : ℤ) :=
    H.mapIso (T.mapIso (a q)).symm.op ≪≫
      e0 q ≪≫ T.mapIso (c q).symm
  have hz (n : ℤ) (hn : n < 0) :
      CategoryTheory.Limits.IsZero ((signedSheafDualComplex (R := R) E O).X n) := by
    have hL : CategoryTheory.Limits.IsZero (L.X (-n)) := K.isZero_extend_X _ _ (by
      intro q
      simp only [ComplexShape.embeddingDownNat_f]
      omega)
    exact H.map_isZero ((T.map_isZero hL).op)
  have hzF (n : ℤ) (hn : n < 0) : CategoryTheory.Limits.IsZero (F.X n) := by
    exact T.map_isZero (HomologicalComplex.isZero_extend_X _ _ _ (by
      intro q
      simp only [ComplexShape.embeddingUpNat_f]
      omega))
  let e (n : ℤ) :
      (signedSheafDualComplex (R := R) E O).X n ≅ F.X n :=
    match n with
    | .ofNat q => ep q
    | .negSucc q => (hz _ (by omega)).iso (hzF _ (by omega))
  have he : ∀ n m, (ComplexShape.up ℤ).Rel n m →
      (e n).hom ≫ F.d n m = (signedSheafDualComplex (R := R) E O).d n m ≫
        (e m).hom := by
    intro n m hnm
    have hm : m = n + 1 := hnm.symm
    subst m
    cases n with
    | negSucc q => exact (hz _ (by omega)).eq_of_src _ _
    | ofNat q =>
      simp only [e]
      change (ep q).hom ≫ F.d (q : ℤ) ((q : ℤ) + 1) =
        (signedSheafDualComplex (R := R) E O).d
          (q : ℤ) ((q : ℤ) + 1) ≫ (ep (q + 1)).hom
      let δ := ModuleCat.ofHom (Linear.leftComp A N (K.d (q + 1) q))
      have hd : D.d (q : ℤ) ((q : ℤ) + 1) =
          (c q).hom ≫ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
            Linear.leftComp A N (K.d (q + 1) q)) ≫ (c (q + 1)).inv := by
        simpa only [B, CochainComplex.of_d] using
          (B.extend_d_eq ComplexShape.embeddingUpNat
            (i := q) (j := q + 1) (i' := (q : ℤ)) (j' := (q : ℤ) + 1) rfl (by simp))
      have hl : L.d (-((q : ℤ) + 1)) (-(q : ℤ)) =
          (a (q + 1)).hom ≫ K.d (q + 1) q ≫ (a q).inv := by
        exact K.extend_d_eq ComplexShape.embeddingDownNat (by simp) rfl
      have hs : ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
          Linear.leftComp A N (K.d (q + 1) q)) =
          (-(q : ℤ).negOnePow) • δ := by
        apply ModuleCat.hom_ext
        ext f x
        simp only [ConcreteCategory.hom_ofHom, LinearMap.smul_apply, Linear.leftComp_apply,
          ModuleCat.hom_smul, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
          Units.neg_smul, ModuleCat.hom_neg, LinearMap.neg_apply, δ]
        simp only [pow_succ, mul_neg_one, neg_smul, Units.smul_def]
        rw [← Int.cast_negOnePow_natCast A q, Int.cast_smul_eq_zsmul]
      have hdS : (signedSheafDualComplex (R := R) E O).d (q : ℤ) ((q : ℤ) + 1) =
          -(q : ℤ).negOnePow • SheafOfModules.homObjMap (R := R)
            (T.map (L.d (-((q : ℤ) + 1)) (-(q : ℤ)))) (𝟙 O) :=
        by
          simp only [signedSheafDualComplex, CochainComplex.of_d]
          rfl
      rw [hdS]
      change (ep q).hom ≫ T.map (D.d (q : ℤ) ((q : ℤ) + 1)) =
        (-(q : ℤ).negOnePow • SheafOfModules.homObjMap (R := R)
          (T.map (L.d (-((q : ℤ) + 1)) (-(q : ℤ)))) (𝟙 O)) ≫ (ep (q + 1)).hom
      rw [hd, hs, hl]
      dsimp only [ep, Iso.trans, Functor.mapIso, Iso.symm, Iso.op]
      simp only [Functor.map_comp, Functor.map_units_smul, Category.assoc]
      change (H.map (T.map (a q).inv).op ≫ (e0 q).hom ≫ T.map (c q).inv) ≫
          T.map (c q).hom ≫ (-(q : ℤ).negOnePow • T.map δ) ≫ T.map (c (q + 1)).inv =
        (-(q : ℤ).negOnePow • H.map
          (T.map (a (q + 1)).hom ≫ T.map (K.d (q + 1) q) ≫ T.map (a q).inv).op) ≫
          H.map (T.map (a (q + 1)).inv).op ≫ (e0 (q + 1)).hom ≫ T.map (c (q + 1)).inv
      simp only [op_comp, Functor.map_comp, Category.assoc,
        Linear.units_smul_comp, Linear.comp_units_smul, Iso.inv_hom_id_map_assoc]
      have ha : H.map (T.map (a (q + 1)).hom).op ≫
          H.map (T.map (a (q + 1)).inv).op = 𝟙 _ :=
        (H.mapIso (T.mapIso (a (q + 1))).op).hom_inv_id
      rw [← Category.assoc (H.map (T.map (a (q + 1)).hom).op)
        (H.map (T.map (a (q + 1)).inv).op) _, ha, Category.id_comp]
      have hn : H.map (T.map (K.d (q + 1) q)).op ≫ (e0 (q + 1)).hom =
          (e0 q).hom ≫ T.map δ := h0 q
      rw [← Category.assoc (H.map (T.map (K.d (q + 1) q)).op) (e0 (q + 1)).hom _, hn]
      erw [Category.assoc]
  exact ⟨HomologicalComplex.Hom.isoOfComponents e he, fun q ↦ rfl⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_dual_square_of_components
    {A : Type u} [CommRing A] {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    (T : ModuleCat.{u} A ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (hT : T.Additive)
    (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (NO NQ : ModuleCat.{u} A) (g : NO ⟶ NQ)
    (pO : ∀ q : ℕ,
      ModuleCat.ofHom ((-1 : A) ^ (q + 1) • Linear.leftComp A NO (K.d (q + 1) q)) ≫
      ModuleCat.ofHom ((-1 : A) ^ (q + 1 + 1) •
        Linear.leftComp A NO (K.d (q + 1 + 1) (q + 1))) = 0)
    (pQ : ∀ q : ℕ,
      ModuleCat.ofHom ((-1 : A) ^ (q + 1) • Linear.leftComp A NQ (K.d (q + 1) q)) ≫
      ModuleCat.ofHom ((-1 : A) ^ (q + 1 + 1) •
        Linear.leftComp A NQ (K.d (q + 1 + 1) (q + 1))) = 0)
    (eO : ∀ q : ℕ, SheafOfModules.homObj (R := R) (T.obj (K.X q)) (T.obj NO) ≅
      T.obj (ModuleCat.of A (K.X q ⟶ NO)))
    (eQ : ∀ q : ℕ, SheafOfModules.homObj (R := R) (T.obj (K.X q)) (T.obj NQ) ≅
      T.obj (ModuleCat.of A (K.X q ⟶ NQ)))
    (hO : ∀ q : ℕ,
      SheafOfModules.homObjMap (R := R) (T.map (K.d (q + 1) q)) (𝟙 (T.obj NO)) ≫
        (eO (q + 1)).hom = (eO q).hom ≫
          T.map (ModuleCat.ofHom (Linear.leftComp A NO (K.d (q + 1) q))))
    (hQ : ∀ q : ℕ,
      SheafOfModules.homObjMap (R := R) (T.map (K.d (q + 1) q)) (𝟙 (T.obj NQ)) ≫
        (eQ (q + 1)).hom = (eQ q).hom ≫
          T.map (ModuleCat.ofHom (Linear.leftComp A NQ (K.d (q + 1) q))))
    (hg : ∀ q : ℕ,
      SheafOfModules.homObjMap (R := R) (𝟙 (T.obj (K.X q))) (T.map g) ≫ (eQ q).hom =
        (eO q).hom ≫ T.map (ModuleCat.ofHom (Linear.rightComp A (K.X q) g))) :
    let BO := CochainComplex.of
      (fun q ↦ ModuleCat.of A (K.X q ⟶ NO))
      (fun q ↦ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
        Linear.leftComp A NO (K.d (q + 1) q))) pO
    let BQ := CochainComplex.of
      (fun q ↦ ModuleCat.of A (K.X q ⟶ NQ))
      (fun q ↦ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
        Linear.leftComp A NQ (K.d (q + 1) q))) pQ
    ∀ (δ : BO ⟶ BQ),
      (∀ q, δ.f q = ModuleCat.ofHom (Linear.rightComp A (K.X q) g)) →
      let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
      let E := TC.obj (K.extend ComplexShape.embeddingDownNat)
      ∃ (bO : signedSheafDualComplex (R := R) E (T.obj NO) ≅
          TC.obj (BO.extend ComplexShape.embeddingUpNat))
        (bQ : signedSheafDualComplex (R := R) E (T.obj NQ) ≅
          TC.obj (BQ.extend ComplexShape.embeddingUpNat)),
        signedSheafDualCoefficientMap E (T.map g) ≫ bQ.hom =
          bO.hom ≫ TC.map (HomologicalComplex.extendMap δ ComplexShape.embeddingUpNat) := by
  classical
  let BO := CochainComplex.of
    (fun q ↦ ModuleCat.of A (K.X q ⟶ NO))
    (fun q ↦ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
      Linear.leftComp A NO (K.d (q + 1) q))) pO
  let BQ := CochainComplex.of
    (fun q ↦ ModuleCat.of A (K.X q ⟶ NQ))
    (fun q ↦ ModuleCat.ofHom ((-1 : A) ^ (q + 1) •
      Linear.leftComp A NQ (K.d (q + 1) q))) pQ
  dsimp only
  intro δ hδ
  let L := K.extend ComplexShape.embeddingDownNat
  let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let E := TC.obj L
  obtain ⟨bO, hbO⟩ := coefficient_dual_iso_of_components
    T hT K NO pO (T.obj NO) eO hO
  obtain ⟨bQ, hbQ⟩ := coefficient_dual_iso_of_components
    T hT K NQ pQ (T.obj NQ) eQ hQ
  refine ⟨bO, bQ, ?_⟩
  apply HomologicalComplex.hom_ext
  intro k
  cases k with
  | negSucc q =>
    have hz : CategoryTheory.Limits.IsZero (L.X (-Int.negSucc q)) :=
      K.isZero_extend_X _ _ (by
        intro j
        simp only [ComplexShape.embeddingDownNat_f]
        omega)
    let H := (SheafOfModules.homFunctor R).flip.obj (T.obj NO)
    exact (H.map_isZero ((T.map_isZero hz).op)).eq_of_src _ _
  | ofNat q =>
    let a : L.X (-(q : ℤ)) ≅ K.X q :=
      K.extendXIso ComplexShape.embeddingDownNat rfl
    let cO : (BO.extend ComplexShape.embeddingUpNat).X (q : ℤ) ≅
        ModuleCat.of A (K.X q ⟶ NO) :=
      BO.extendXIso ComplexShape.embeddingUpNat rfl
    let cQ : (BQ.extend ComplexShape.embeddingUpNat).X (q : ℤ) ≅
        ModuleCat.of A (K.X q ⟶ NQ) :=
      BQ.extendXIso ComplexShape.embeddingUpNat rfl
    have hd : (HomologicalComplex.extendMap δ ComplexShape.embeddingUpNat).f (q : ℤ) =
        cO.hom ≫ δ.f q ≫ cQ.inv := by
      exact HomologicalComplex.extendMap_f _ _ rfl
    change SheafOfModules.homObjMap (R := R)
        (𝟙 (T.obj (L.X (-(q : ℤ))))) (T.map g) ≫ bQ.hom.f (q : ℤ) =
      bO.hom.f (q : ℤ) ≫ T.map
        ((HomologicalComplex.extendMap δ ComplexShape.embeddingUpNat).f (q : ℤ))
    simp only [hbO q, hbQ q, hd]
    change SheafOfModules.homObjMap (R := R)
        (𝟙 (T.obj (L.X (-(q : ℤ))))) (T.map g) ≫
        SheafOfModules.homObjMap (T.map a.inv) (𝟙 (T.obj NQ)) ≫
        (eQ q).hom ≫ T.map cQ.inv =
      (SheafOfModules.homObjMap (T.map a.inv) (𝟙 (T.obj NO)) ≫
        (eO q).hom ≫ T.map cO.inv) ≫ T.map (cO.hom ≫ δ.f q ≫ cQ.inv)
    have hc : SheafOfModules.homObjMap (R := R)
        (𝟙 (T.obj (L.X (-(q : ℤ))))) (T.map g) ≫
        SheafOfModules.homObjMap (T.map a.inv) (𝟙 (T.obj NQ)) =
      SheafOfModules.homObjMap (T.map a.inv) (𝟙 (T.obj NO)) ≫
        SheafOfModules.homObjMap (𝟙 (T.obj (K.X q))) (T.map g) := by
      simp only [SheafOfModules.homObjMap_comp_homObjMap,
        Category.id_comp, Category.comp_id]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
    rw [← Category.assoc _ (SheafOfModules.homObjMap (T.map a.inv) (𝟙 (T.obj NQ))) _, hc]
    rw [Category.assoc, ← Category.assoc _ (eQ q).hom _, hg q]
    rw [hδ q]
    simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine finite-free signed dual comparisons commute with quotient coefficients.
Source: Stacks Project, Tag 0BQZ, displayed Hom-complex map;
Tag 01HV, Lemma 26.5.4(4)-(5), localization of associated modules.
(blueprint: new-g3-affine-koszul-signed-dual-coefficient-square).

Proof: In nonnegative degree k use the exterior-power basis of the free
module A^n. On a principal open D(g), maps from its associated sheaf to
tilde(M), for M=A or A/I, are tuples of values in M_g on that finite basis.
Localization of Hom_A(K_k,M) gives exactly these tuples. Their coordinate
identifications commute with localization, so they define inverse sheaf
maps. Precomposition by the localized Koszul boundary has the same matrix
on either side; the integer sign -(-1)^k equals (-1)^(k+1). Thus the maps
commute with the signed differentials. In negative degree both terms are
zero; at the degree -1 boundary the source is zero. The degree comparisons
therefore assemble into complex isomorphisms. Postcomposition with A→A/I
reduces every basis value, which is precisely koszulCoefficientReduction.
This proves the coefficient square degreewise. The empty exterior bases,
zero ring, top ideal and empty charts are covered by the same formulas. -/
theorem affine_koszul_signed_dual_coefficient_square
    {Y : Scheme.{u}} (U : Y.affineOpens) (I : Ideal (Γ(Y, U.1)))
    (n : ℕ) (f : Fin n → Γ(Y, U.1)) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
    let E := TC.obj
      ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
    ∃ (bO : signedSheafDualComplex (R := U.1.toScheme.toRingedSpace.sheaf)
          E (T.obj (ModuleCat.of A A)) ≅
        TC.obj ((ExteriorAlgebra.koszulDualComplex A n f).extend
          ComplexShape.embeddingUpNat))
      (bQ : signedSheafDualComplex (R := U.1.toScheme.toRingedSpace.sheaf)
          E (T.obj (ModuleCat.of A (A ⧸ I))) ≅
        TC.obj ((ExteriorAlgebra.koszulQuotientDualComplex A I n f).extend
          ComplexShape.embeddingUpNat)),
      signedSheafDualCoefficientMap E (T.map (ModuleCat.ofHom I.mkQ)) ≫ bQ.hom =
        bO.hom ≫ TC.map (HomologicalComplex.extendMap
          (ExteriorAlgebra.koszulCoefficientReduction A I n f)
          ComplexShape.embeddingUpNat) := by
  classical
  let A := (Γ(Y, U.1) : Type u)
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let K := ExteriorAlgebra.koszulComplex A n f
  let NO := ModuleCat.of A A
  let NQ := ModuleCat.of A (A ⧸ I)
  have : (tilde.functor Γ(Y, U.1)).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := Γ(Y, U.1)) f g
  have : (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).Additive := ⟨by intros; rfl⟩
  have hT : T.Additive := inferInstanceAs
    (tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).Additive
  have hfree (q : ℕ) : Module.Free A (K.X q) := by
    exact Module.Free.of_basis
      ((Finsupp.basisSingleOne : Module.Basis (Fin n) A (Fin n →₀ A)).exteriorPower q)
  have hfinite (q : ℕ) : Module.Finite A (K.X q) := by
    exact Module.Finite.of_basis
      ((Finsupp.basisSingleOne : Module.Basis (Fin n) A (Fin n →₀ A)).exteriorPower q)
  obtain ⟨e, hpre, hpost⟩ := affine_finite_free_coefficient_comparisons U K hfree hfinite
  exact coefficient_dual_square_of_components
    (R := U.1.toScheme.toRingedSpace.sheaf) T hT K NO NQ (ModuleCat.ofHom I.mkQ)
    (ExteriorAlgebra.koszulDualBoundary_comp A n f)
    (ExteriorAlgebra.koszulQuotientDualBoundary_comp A I n f)
    (fun q ↦ e q NO) (fun q ↦ e q NQ)
    (fun q ↦ hpre q NO) (fun q ↦ hpre q NQ)
    (fun q ↦ hpost q NO NQ (ModuleCat.ofHom I.mkQ))
    (ExteriorAlgebra.koszulCoefficientReduction A I n f) (fun q ↦ rfl)

end AlgebraicGeometry
