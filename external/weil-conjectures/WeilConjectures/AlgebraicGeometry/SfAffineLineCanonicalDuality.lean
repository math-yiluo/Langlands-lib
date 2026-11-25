/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.SfAffineBaseP1TraceAdjunction
import WeilConjectures.AlgebraicGeometry.SfExceptionalTensorTransitivity

/-! # Canonical affine-line duality over arbitrary affine bases

proof.md`, paragraphs 2-3, and
`sk-lem-geo-affine-local/cor-amb-affine-space-adjunction.proof.md`, paragraph 1
(auxiliary; not a blueprint node).

The compactification is the actual standard affine chart of projective space.
The right adjoint and adjunction are selected ambient data; their existence follows
from `sfEtaleAmbientAdjointProjection`. The tensor map is precisely that dependency's
counit transpose, with the same selected adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] sfEtaleAmbientTensorMap
  sfExceptionalEtaleRestrictionComparison sfTensorPullbackUnitIso

/-- The standard open-then-proper factorization of the affine-line projection.
The homogeneous coordinates are indexed by `Option (ULift (Fin 1))`, so the
compactifying scheme is the projective line, not the projective plane.
Source: blueprint `cor-amb-affine-space-adjunction.proof.md`, paragraph 1
(auxiliary; not a blueprint node). -/
noncomputable def sfAffineLineCompactification (S : Scheme.{u}) :
    Compactification (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) where
  Z := ProjectiveSpace (Option (ULift.{u} (Fin 1))) S
  i := AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S
  g := ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S
  comm := (AffineSpace.toRelativeProjectiveSpace_over (ULift.{u} (Fin 1)) S).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

-- This calculation is categorical, so its proof need not unfold derived categories.
private theorem tensorMap_of_trace
    {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (U : D ⥤ C) (TX : C ⥤ C ⥤ C) (TY : D ⥤ D ⥤ D)
    (I : D) (l : TY.obj I ⟶ 𝟭 D)
    (p : ∀ (M : C) (K : D), (TY.obj (F.obj M)).obj K ⟶
      F.obj ((TX.obj M).obj (U.obj K)))
    [pi : ∀ M K, IsIso (p M K)]
    (pn : ∀ {M M' : C} (g : M ⟶ M') (K : D),
      (TY.map (F.map g)).app K ≫ p M' K =
        p M K ≫ F.map ((TX.map g).app (U.obj K)))
    (B : C) (t : F.obj B ⟶ I) (r : B ≅ (TX.obj B).obj (U.obj I))
    (adjB : F ⊣ U ⋙ TX.obj B)
    (ht : ∀ K, p B K ≫ adjB.counit.app K = (TY.map t).app K ≫ l.app K)
    (hu : F.map r.hom ≫ adjB.counit.app I = t)
    (G : D ⥤ C) (adj : F ⊣ G) :
    ∃ gamma : B ≅ G.obj I, ∀ K : D,
      IsIso ((TX.map gamma.hom).app (U.obj K) ≫
        adj.homEquiv _ _ (inv (p (G.obj I) K) ≫
          (TY.map (adj.counit.app I)).app K ≫ l.app K)) := by
  let e := adjB.rightAdjointUniq adj
  let gamma := r ≪≫ e.app I
  have hscalar : F.map gamma.hom ≫ adj.counit.app I = t := by
    dsimp only [gamma, Iso.trans_hom, Iso.app_hom, e]
    rw [Functor.map_comp, Category.assoc,
      Adjunction.rightAdjointUniq_hom_app_counit]
    exact hu
  refine ⟨gamma, fun K ↦ ?_⟩
  have := pi B K
  have := pi (G.obj I) K
  have hp := pn gamma.hom K
  have hpi : F.map ((TX.map gamma.hom).app (U.obj K)) ≫
      inv (p (G.obj I) K) =
      inv (p B K) ≫ (TY.map (F.map gamma.hom)).app K := by
    rw [← cancel_epi (p B K)]
    simp only [← Category.assoc]
    erw [← hp]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  have he : (TX.map gamma.hom).app (U.obj K) ≫
      adj.homEquiv _ _ (inv (p (G.obj I) K) ≫
        (TY.map (adj.counit.app I)).app K ≫ l.app K) = e.hom.app K := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
    dsimp only [e]
    erw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
    rw [← Category.assoc, ← Category.assoc, hpi]
    simp only [Category.assoc]
    rw [← Category.assoc ((TY.map (F.map gamma.hom)).app K)
      ((TY.map (adj.counit.app I)).app K),
      ← NatTrans.comp_app, ← Functor.map_comp, hscalar]
    rw [← ht K, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rfl
  rw [he]
  infer_instance

-- Compare the actual counit transposes, rather than arbitrary isomorphisms of functors.
private theorem tensorMap_of_trace_adjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (B : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj B ⟶
      constantComplex A Y)
    (adjB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        (derivedTensor (ModuleCat.{u + 1} A) X).obj B)
    (ht : ∀ K : DerivedCategoryModule A Y,
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app B).app K ≫
        adjB.counit.app K =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map t).app K ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y K).hom)
    (hu : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (sfTensorPullbackUnitIso A f B).hom ≫ adjB.counit.app (constantComplex A Y) = t)
    (G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    ∃ gamma : B ≅ G.obj (constantComplex A Y),
      ∀ K : DerivedCategoryModule A Y,
        IsIso ((((derivedTensor (ModuleCat.{u + 1} A) X).map gamma.hom).app
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
          sfEtaleAmbientTensorMap A c G adj K) := by
  unfold sfEtaleAmbientTensorMap
  apply tensorMap_of_trace
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (L(upperStar (ModuleCat.{u + 1} A) f))
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedTensor (ModuleCat.{u + 1} A) Y)
    (constantComplex A Y) (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} A) Y).hom
    (fun M K ↦ ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K)
    (fun g K ↦ congr_app
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).naturality g) K)
    B t (sfTensorPullbackUnitIso A f B) adjB ht hu G adj
    (pi := (sfEtaleAmbientAdjointProjection A c).2)

-- The etale restriction identity transports invertibility for every unbounded complex.
private theorem tensorMap_etale_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) {f : X ⟶ Z}
    (hf : a ≫ b = f) [Etale a] [IsSeparated a]
    (ca : Compactification a) (cb : Compactification b) (cf : Compactification f)
    (Gb : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (adjb : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb ⊣ Gb)
    (hb : ∀ K : DerivedCategoryModule A Z, IsIso (sfEtaleAmbientTensorMap A cb Gb adjb K))
    (G : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⊣ G) :
    Nonempty (Gb ⋙ L(upperStar (ModuleCat.{u + 1} A) a) ≅ G) ∧
      ∀ K : DerivedCategoryModule A Z, IsIso (sfEtaleAmbientTensorMap A cf G adj K) := by
  subst f
  have := (sfEtaleAmbientAdjointProjection A ca).1
  let Ga := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca).rightAdjoint
  let adja := Adjunction.ofIsLeftAdjoint
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca)
  refine ⟨⟨sfExceptionalEtaleRestrictionComparison A a b ca cb cf Ga Gb G adja adjb adj⟩,
    fun K ↦ ?_⟩
  have := hb K
  have h := sfExceptionalTensorEtaleRestriction A a b ca cb cf Ga Gb G adja adjb adj K
  have hi : IsIso ((L(upperStar (ModuleCat.{u + 1} A) a)).map
      (sfEtaleAmbientTensorMap A cb Gb adjb K) ≫
      (sfExceptionalEtaleRestrictionComparison A a b ca cb cf Ga Gb G adja adjb adj).hom.app
        K) := inferInstance
  rw [h] at hi
  simpa only [isIso_comp_left_iff] using hi

/-- Affine-line duality identifies the concrete roots-of-unity Tate line shifted by
2 with the ambient dualizing object, and the resulting actual tensor composite is
invertible for every ordinary unbounded complex. The arguments G and adj select
an ambient right adjoint, whose existence is already guaranteed; they impose no
additional geometric or cohomological hypothesis.

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraphs 2-3, and
`cor-amb-affine-space-adjunction.proof.md`, paragraph 1
(auxiliary; not a blueprint node).

Proof plan:
1. Use the standard chart j and proper projection q in sfAffineLineCompactification
   (lemma-nagata-relative-affine-space-open-immersion and
   lemma-nagata-projective-space-base-change-proper). Then F_p = Rq_* Dj_!.
2. Apply lem-sf-affine-base-p1-trace-adjunction over the arbitrary affine base.
   Its right adjoint H(K) = A_P(1)[2] tensor q^*K has the projection-normalized
   trace counit. Compare H with the ambient G_q using proposition-sp-unique-adjoint--1;
   the counit-preserving comparison gives gamma_q at the coefficient unit.
3. Transpose theta_q composed with gamma_q tensor 1. Naturality of projection
   identifies its transpose with the trace counit from step 2. The adjunction
   bijection therefore identifies this composite with the right-adjoint comparison,
   so every theta_q is invertible (lem-sf-etale-ambient-adjoint-projection).
4. The chart j is separated etale (lem-weil-pbc-open-immersion-etale).
   Apply lem-sf-etale-unit-tensor-arbitrary-base and the etale restriction equation
   of lem-sf-exceptional-tensor-transitivity to j followed by q. Its
   counit-preserving comparison intertwines the actual theta maps, proving that
   theta_p is invertible on all unbounded K.
5. Pull back gamma_q along j and compose with that comparison at the unit.
   The roots-of-unity pullback of lem-asd-etale-finite-twist-pullback identifies
   its source with the concrete A_X(1)[2], giving gamma_p. Tensoring gamma_p
   with the identity is invertible, as is theta_p by step 4, so their actual
   composite is invertible. No Noetherian or boundedness assumption is used. -/
theorem sfAffineLineCanonicalDuality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsAffine S]
    (hS : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (G : DerivedCategoryModule A S ⥤
      DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S))
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (sfAffineLineCompactification S) ⊣ G) :
    ∃ gamma :
      (shiftFunctor _ (2 : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) S) N A hA)) ≅
        G.obj (constantComplex A S),
      ∀ K : DerivedCategoryModule A S,
        IsIso
          ((((derivedTensor (ModuleCat.{u + 1} A)
              (AffineSpace (ULift.{u} (Fin 1)) S)).map gamma.hom).app
              ((L(upperStar (ModuleCat.{u + 1} A)
                (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))).obj K)) ≫
            sfEtaleAmbientTensorMap A (sfAffineLineCompactification S) G adj K) := by
  classical
  let P := ProjectiveSpace (Option (ULift.{u} (Fin 1))) S
  let j := AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S
  let q : P ⟶ S := P ↘ S
  let B : DerivedCategoryModule A P :=
    (shiftFunctor _ (2 : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine P N A hA))
  obtain ⟨t, adjB, ht, hu⟩ := sfAffineBaseP1TraceAdjunction A N hN hA S hS
  let H := L(upperStar (ModuleCat.{u + 1} A) q) ⋙
    (derivedTensor (ModuleCat.{u + 1} A) P).obj B
  obtain ⟨gammaq, hgammaq⟩ := tensorMap_of_trace_adjunction A
    (sfProjectiveLineCompactification S) B t adjB ht hu H adjB
  have hq (K : DerivedCategoryModule A S) :
      IsIso (sfEtaleAmbientTensorMap A (sfProjectiveLineCompactification S) H adjB K) := by
    have := hgammaq K
    exact IsIso.of_isIso_comp_left
      (((derivedTensor (ModuleCat.{u + 1} A) P).map gammaq.hom).app
        ((L(upperStar (ModuleCat.{u + 1} A) q)).obj K)) _
  have hjq : j ≫ q = AffineSpace (ULift.{u} (Fin 1)) S ↘ S :=
    AffineSpace.toRelativeProjectiveSpace_over (ULift.{u} (Fin 1)) S
  obtain ⟨⟨e⟩, hp⟩ := tensorMap_etale_restriction A j q hjq
    (Compactification.ofIsOpenImmersion j) (sfProjectiveLineCompactification S)
    (sfAffineLineCompactification S) H adjB hq G adj
  have hP : IsUnit (N : Γ(P, ⊤)) := by
    apply P.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using (hS (q x)).map (q.stalkMap x).hom
  have hX : IsUnit (N : Γ(AffineSpace (ULift.{u} (Fin 1)) S, ⊤)) := by
    simpa only [map_natCast] using hP.map j.appTop.hom
  let c := (Scheme.finiteEtaleTwistPullbackData A N hN hA).c j hP hX 1
  let pb : (L(upperStar (ModuleCat.{u + 1} A) j)).obj B ≅
      (shiftFunctor _ (2 : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) S) N A hA)) :=
    ((L(upperStar (ModuleCat.{u + 1} A) j)).commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) j).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso c)
  let gamma := pb.symm ≪≫ (L(upperStar (ModuleCat.{u + 1} A) j)).mapIso gammaq ≪≫
    e.app (constantComplex A S)
  refine ⟨gamma, fun K ↦ ?_⟩
  have := hp K
  infer_instance

end AlgebraicGeometry.Etale
