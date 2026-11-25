/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.AlgebraicGeometry.Noetherian

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteNativeRelativeLisse
import WeilConjectures.AlgebraicGeometry.Relative.RelativeNilpotentLissity
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Propagation of lissity along a normalized adic tower

This is the nilpotent propagation step used by the common-strata theorem.

## References

* Stacks Project, Tag 094I
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A finite native constant model on a covering sieve.

The predicate records the local finite constant models after transporting to the
native coefficient ring. It is the fixed-level input for nilpotent propagation.
-/
def NormalizedNativeSieveFiniteLisse (Z : Scheme.{u}) (D : Type (u + 1)) [CommRing D]
    (F : pbcModules Z (adicLisseConstantRing Z D)) : Prop :=
  ∃ S : Sieve (⊤_ Z.ProEt), S ∈ ProEt.topology Z (⊤_ Z.ProEt) ∧
    ∀ (U : Z.ProEt) (f : U ⟶ ⊤_ Z.ProEt), S f →
      ∃ M : ModuleCat.{u + 1} D, Finite M ∧
        Nonempty (F.over U ≅
          ((adicLisseConstantModules Z D).obj M).over U)

namespace LissePropagationProof

private def restrictCancelIso {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

attribute [local irreducible] restrictCancelIso

private abbrev coefficientEquivalence {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
  CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (restrictCancelIso e.inv e.hom e.inv_hom_id).symm
    (restrictCancelIso e.hom e.inv e.hom_inv_id)

private theorem relative_of_iso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    {F G : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))}
    (e : F ≅ G) (h : IsRelativelyFiniteLisseModule g B F) :
    IsRelativelyFiniteLisseModule g B G := by
  obtain ⟨T, hT, ht⟩ := h
  refine ⟨T, hT, fun U f hf ↦ ?_⟩
  obtain ⟨V, hV, ⟨i⟩⟩ := ht U f hf
  exact ⟨V, hV, ⟨(SheafOfModules.overFunctor _ U).mapIso e.symm ≪≫ i⟩⟩

private noncomputable def coefficientExtensionIso {X : Scheme.{u}}
    {R S R' S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (eR : R ≅ R') (eS : S ≅ S') (f : R ⟶ S) (f' : R' ⟶ S')
    (hsq : f ≫ eS.hom = eR.hom ≫ f') :
    pbcDerivedRestrict eR.hom ⋙ pbcDerivedExtend f ≅
      pbcDerivedExtend f' ⋙ pbcDerivedRestrict eS.hom := by
  let ER₀ := coefficientEquivalence ((adicLisseForget X).mapIso eR)
  let ES₀ := coefficientEquivalence ((adicLisseForget X).mapIso eS)
  have : ER₀.functor.Additive := inferInstanceAs (pbcRestrict eR.hom).Additive
  have : ER₀.inverse.Additive := inferInstanceAs (pbcRestrict eR.inv).Additive
  have : ES₀.functor.Additive := inferInstanceAs (pbcRestrict eS.hom).Additive
  have : ES₀.inverse.Additive := inferInstanceAs (pbcRestrict eS.inv).Additive
  let ER := ER₀.mapDerivedCategory
  let ES := ES₀.mapDerivedCategory
  have hi : eR.inv ≫ f = f' ≫ eS.inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun k ↦ eR.inv ≫ k ≫ eS.inv) hsq
  let r : pbcDerivedRestrict f ⋙ pbcDerivedRestrict eR.inv ≅
      pbcDerivedRestrict eS.inv ⋙ pbcDerivedRestrict f' :=
    pbcDerivedRestrictComp eR.inv f (f' ≫ eS.inv) hi ≪≫
      (pbcDerivedRestrictComp f' eS.inv (f' ≫ eS.inv) rfl).symm
  let a : pbcDerivedRestrict eR.hom ⋙ pbcDerivedExtend f ⊣
      pbcDerivedRestrict f ⋙ pbcDerivedRestrict eR.inv :=
    ER.toAdjunction.comp (pbcDerivedScalarAdjunction f)
  let b : pbcDerivedExtend f' ⋙ pbcDerivedRestrict eS.hom ⊣
      pbcDerivedRestrict eS.inv ⋙ pbcDerivedRestrict f' :=
    (pbcDerivedScalarAdjunction f').comp ES.toAdjunction
  exact (a.ofNatIsoRight r).leftAdjointUniq b

private noncomputable def pulledCoefficientHomologyIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (e : R ≅ S)
    (K : DerivedCategory (pbcModules X S)) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((adicTowerPullback g R).obj ((pbcDerivedRestrict e.hom).obj K)) ≅
      (pbcRestrict ((adicTowerInverseImage g).map e.hom)).obj
        ((DerivedCategory.homologyFunctor _ q).obj ((adicTowerPullback g S).obj K)) := by
  let b := proEtaleRingRestrictionDerivedPullback g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    e.hom ((adicTowerInverseImage g).map e.hom) (Iso.refl _) (Iso.refl _)
    (by simp)
  exact (DerivedCategory.homologyFunctor _ q).mapIso (b.app K).symm ≪≫
    (((pbcRestrict ((adicTowerInverseImage g).map e.hom)).mapDerivedCategoryHomologyFunctorIso
      q).app ((adicTowerPullback g S).obj K)).symm

end LissePropagationProof

/-- Level-zero native finite models propagate through every normalized quotient. -/
theorem normalizedTower_lisse_of_native_strata
    (X : Scheme.{u}) [IsNoetherian X] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (S : Stratification X) (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hnative : ∀ (i : Fin S.n) (q : ℤ),
      ∃ c : (proEtaleSheafInverseImage (S.immersion i) CommRingCat.{u + 1}).obj
          (adicLisseConstantRing X (A ⧸ d.ideal ^ (0 + 1))) ≅
          adicLisseConstantRing (S.domain i) (A ⧸ d.ideal ^ (0 + 1)),
        NormalizedNativeSieveFiniteLisse (S.domain i)
          (A ⧸ d.ideal ^ (0 + 1))
          ((proEtaleRingModulePullback (S.immersion i)
            (adicLisseConstantRing X (A ⧸ d.ideal ^ (0 + 1)))
            (adicLisseConstantRing (S.domain i) (A ⧸ d.ideal ^ (0 + 1))) c).obj
            ((pbcRestrict (pbcLevelConstantComparison X d 0).hom).obj
              ((DerivedCategory.homologyFunctor _ q).obj (M.level 0))))) :
    ∀ (i : Fin S.n) (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule (S.immersion i)
        (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage (S.immersion i)).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback (S.immersion i)
                ((pbcAdicRings X d).obj (op n))).obj (M.level n)))) := by
  classical
  have := d.quotientFinite
  intro i
  let g := S.immersion i
  let B (n : ℕ) := A ⧸ d.ideal ^ (n + 1)
  let e (n : ℕ) := pbcLevelConstantComparison X d n
  let K (n : ℕ) := (pbcDerivedRestrict (e n).hom).obj (M.level n)
  have hKbounded (n : ℕ) : ∃ c : ℤ, ∀ q : ℤ, c < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (K n)) := by
    refine ⟨max a b, fun q hq ↦ ?_⟩
    rw [max_eq_right hab] at hq
    exact ((pbcRestrict (e n).hom).map_isZero (hbounded n q (Or.inr hq))).of_iso
      (((pbcRestrict (e n).hom).mapDerivedCategoryHomologyFunctorIso q).app
        (M.level n)).symm
  have hlevels (n : ℕ) : ∀ q : ℤ, IsRelativelyFiniteLisseModule g (B n)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((adicTowerPullback g (adicLisseConstantRing X (B n))).obj (K n))) := by
    induction n with
    | zero =>
      intro q
      obtain ⟨c, hc⟩ := hnative i q
      have h := finite_native_models_relative_lisse g (B 0)
        ((pbcRestrict (e 0).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj (M.level 0))) c hc
      let P := proEtaleModuleInverseImage g (adicLisseConstantRing X (B 0))
      let adj := proEtaleModuleInverseImageAdjunction g
        (adicLisseConstantRing X (B 0))
      have : P.Additive := adj.left_adjoint_additive
      have : PreservesFiniteLimits P :=
        proEtaleModuleInverseImage_preservesFiniteLimits g _
      have : PreservesColimitsOfSize.{0, 0} P := adj.leftAdjoint_preservesColimits
      let eP := Functor.mapDerivedCategoryNatIso
        ((proEtaleModuleInverseImageAdjunction g (adicLisseConstantRing X (B 0))).leftAdjointUniq
          (proEtaleRingModuleAdjunction g (adicLisseConstantRing X (B 0))
            ((adicTowerInverseImage g).obj (adicLisseConstantRing X (B 0))) (Iso.refl _)))
      let j := P.mapIso
        (((pbcRestrict (e 0).hom).mapDerivedCategoryHomologyFunctorIso q).app
          (M.level 0)) ≪≫ (P.mapDerivedCategoryHomologyFunctorIso q).app (K 0) ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso (eP.app (K 0))
      exact LissePropagationProof.relative_of_iso g (B 0) j h
    | succ n ih =>
      let f : B (n + 1) →+* B n := Ideal.Quotient.factorPowSucc d.ideal (n + 1)
      have hnil : IsNilpotent (RingHom.ker f) := by
        change IsNilpotent (RingHom.ker (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))
        rw [Ideal.Quotient.factor_ker]
        refine ⟨2, ?_⟩
        rw [← Ideal.map_pow, ← pow_mul]
        change (d.ideal ^ ((n + 1) * 2)).map
          (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1))) = ⊥
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
        apply Ideal.pow_le_pow_right
        omega
      let fS := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom f)
      have hsq : fS ≫ (e n).hom = (e (n + 1)).hom ≫
          pbcAdicQuotient X d (n + 1) n (Nat.le_succ n) := by
        simpa only [fS, f, B, e, pbcAdicQuotient, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
          using pbcConstantSystemComparison_naturality X d (homOfLE (Nat.le_succ n)).op
      let j : (pbcDerivedExtend fS).obj (K (n + 1)) ≅ K n :=
        (LissePropagationProof.coefficientExtensionIso (e (n + 1)) (e n) fS
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) hsq).app (M.level (n + 1)) ≪≫
          (pbcDerivedRestrict (e n).hom).mapIso
            (M.normalization (n + 1) n (Nat.le_succ n))
      apply relative_finite_lisse_of_nilpotent_reduction g f
        (Ideal.Quotient.factor_surjective _) hnil (K (n + 1)) (hKbounded (n + 1))
      intro q
      exact LissePropagationProof.relative_of_iso g (B n)
        ((DerivedCategory.homologyFunctor _ q).mapIso
          ((adicTowerPullback g (adicLisseConstantRing X (B n))).mapIso j.symm)) (ih q)
  intro n q
  exact LissePropagationProof.relative_of_iso g (B n)
    (LissePropagationProof.pulledCoefficientHomologyIso g (e n) (M.level n) q)
    (hlevels n q)

end AlgebraicGeometry.Scheme
