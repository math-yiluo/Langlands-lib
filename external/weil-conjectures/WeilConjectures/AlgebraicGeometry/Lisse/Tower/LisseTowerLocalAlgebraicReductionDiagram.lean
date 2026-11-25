/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantAlgebraicReductionDiagram
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantUnboundedFiniteDiagramComparison

/-! # Local finite algebra diagrams for lisse towers

## References

* Stacks Project, Tag 09BV, and the bounded-derived local-constancy argument in amplification (c)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem relativelyFiniteLisse_of_iso
    {X Y : Scheme.{u}} (g : Y ⟶ X) (B : Type (u + 1)) [CommRing B]
    {F G : ringedSiteModules.{u + 1} ((adicLisseForget Y).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X B)))}
    (e : F ≅ G) (hG : IsRelativelyFiniteLisseModule g B G) :
    IsRelativelyFiniteLisseModule g B F := by
  obtain ⟨S, hS, hlocal⟩ := hG
  refine ⟨S, hS, fun V f hf ↦ ?_⟩
  obtain ⟨N, hN, ⟨eN⟩⟩ := hlocal V f hf
  exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ V).mapIso e ≪≫ eN⟩⟩

private theorem paste_reduction_squares
    {D₀ D₁ : Type*} [Category* D₀] [Category* D₁] (R : D₁ ⥤ D₀)
    {P Q T : D₀} {P' Q' T' : D₁}
    (i : P ≅ Q) (j : Q ≅ T) (i' : P' ≅ Q') (j' : Q' ≅ T')
    {a : P ⟶ R.obj P'} {b : Q ⟶ R.obj Q'} {c : T ⟶ R.obj T'}
    (hi : i.hom ≫ b = a ≫ R.map i'.hom)
    (hj : j.hom ≫ c = b ≫ R.map j'.hom) :
    (i ≪≫ j).hom ≫ c = a ≫ R.map (i' ≪≫ j').hom := by
  simp only [Iso.trans_hom, Functor.map_comp]
  rw [Category.assoc, hj, ← Category.assoc, hi, Category.assoc]

-- Preserve the original names of proof binders inside the theorem statement.
set_option linter.unusedVariables false in
/-- Local finite constant diagrams, with descent of an effective algebraic cone.
This statement constructs the finite normalized algebra tower. It requires only
separate bounds for each level and constructs no complete algebraic object. Its last
clause applies to any object whose actual adjunction units give compatible reductions
to that tower. -/
theorem lisse_tower_local_algebraic_reduction_diagram
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) :
    let C := AdicCompletion d.ideal A
    let J := d.ideal.map (algebraMap A C)
    ∃ V : Sieve (⊤_ Y.ProEt), V ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
      ∀ (U : Y.ProEt) (f : U ⟶ ⊤_ Y.ProEt), V f →
        ∃ (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))))
          (t : ∀ n : ℕ, K (n + 1) ⟶
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
              (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj
                  (K n)),
          (∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1)))),
            Function.Bijective (fun k : K n ⟶ N ↦ t n ≫
              (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
                (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.map
                    k)) ∧
          (∀ (n : ℕ) (q : ℤ),
            IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)) →
            IsZero ((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))) q).obj (K n))) ∧
          (∀ (n : ℕ) (q : ℤ), Module.Finite (C ⧸ J ^ (n + 1))
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))) q).obj (K n))) ∧
          let R (n : ℕ) := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (Ideal.Quotient.mk (J ^ (n + 1)))
          let s (n : ℕ) := (R (n + 1)).mapDerivedCategory.map (t n) ≫
            (Functor.mapDerivedCategoryCompIso
              (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
                (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
              (R (n + 1))).hom.app (K n) ≫
            (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
              (Ideal.Quotient.mk (J ^ (n + 2)))
              (Ideal.Quotient.factor
                (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
              (Ideal.Quotient.mk (J ^ (n + 1)))
              (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n)
          ∀ (E : DerivedCategory (ModuleCat.{u + 1} C))
            (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1} C) ⥤
              DerivedCategory (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))))
            (adj : ∀ n : ℕ, L n ⊣ (R n).mapDerivedCategory)
            (e₀ : ∀ n : ℕ, (L n).obj E ≅ K n)
            (he₀ : ∀ (m n : ℕ) (h : n ≤ m),
              (adj m).unit.app E ≫ (R m).mapDerivedCategory.map (e₀ m).hom ≫
                (Functor.ofOpSequence
                  (X := fun k : ℕ ↦ (R k).mapDerivedCategory.obj (K k)) s).map
                  (homOfLE h).op =
              (adj n).unit.app E ≫ (R n).mapDerivedCategory.map (e₀ n).hom),
          ∀ (φ : adicLisseConstantRing U.left (AdicCompletion d.ideal A) ⟶
      adicLisseCompletedRing U.left d.ideal)
            (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem U.left d.ideal) (op n) =
      (constantSheaf (ProEt.topology U.left) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom))
            (β : (adicTowerInverseImage (U.hom ≫ g)).obj (adicLisseCompletedRing X d.ideal) ⟶
      adicLisseCompletedRing U.left d.ideal)
            (hβ : ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem U.left d.ideal) (op n) =
      (adicTowerInverseImage (U.hom ≫ g)).map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
        proEtaleConstantInverseImageMap (U.hom ≫ g) CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))),
            let c := completedConstantRealization U.left d.ideal φ ⋙ pbcRestrict β ⋙
      pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map (pbcCompletedComparison X d).inv)
            ∀ (hc : c.Additive) (hlim : PreservesFiniteLimits c)
              (hcolim : PreservesFiniteColimits c),
              letI := hc
              letI := hlim
              letI := hcolim
              (∀ (n : ℕ) (q : ℤ),
                IsRelativelyFiniteLisseModule (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
                  ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                    (pbcLevelConstantComparison X d n).hom)).obj
                      ((DerivedCategory.homologyFunctor _ q).obj
                        ((pbcDerivedExtend ((adicTowerInverseImage (U.hom ≫ g)).map
                  (pbcAdicProjection X d n))).obj (c.mapDerivedCategory.obj E))))) ∧
              ∃ e : ∀ n : ℕ, (pbcDerivedExtend ((adicTowerInverseImage (U.hom ≫ g)).map
                  (pbcAdicProjection X d n))).obj (c.mapDerivedCategory.obj E) ≅
                  (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
                    (M.level n),
                ∀ (m n : ℕ) (hnm : n ≤ m),
                  (e m).hom ≫ adicTowerRestrictedTransition d (U.hom ≫ g) M m n hnm =
                    pbcReductionTransition
                ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicProjection X d m))
                ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicQuotient X d m n hnm))
                ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicProjection X d n))
                (((adicTowerInverseImage (U.hom ≫ g)).map_comp _ _).symm.trans
                  (congrArg (adicTowerInverseImage (U.hom ≫ g)).map
                    (pbcAdicProjection_comp X d m n hnm)))
                (c.mapDerivedCategory.obj E) ≫
                      (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                        (pbcAdicQuotient X d m n hnm))).map (e n).hom := by
  obtain ⟨V, hV, hlocal⟩ := lisse_tower_constant_algebraic_reduction_diagram
    X Y g d M hbounded hlisse
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨K, t, hnorm, hvan, hfinite, hconstant⟩ := hlocal U f hf
  refine ⟨K, t, hnorm, hvan, hfinite,
    fun E L adj e₀ he₀ φ hφ β hβ hc hlim hcolim ↦ ?_⟩
  have := hc
  have := hlim
  have := hcolim
  obtain ⟨hloc, e₂, he₂⟩ := hconstant E L adj e₀ he₀
  obtain ⟨e₁, he₁⟩ := completed_constant_unbounded_finite_diagram_comparison
    X U.left (U.hom ≫ g) d φ hφ β hβ hc hlim hcolim E
  refine ⟨fun n q ↦ ?_, fun n ↦ e₁ n ≪≫ e₂ n, ?_⟩
  · exact relativelyFiniteLisse_of_iso (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso (e₁ n))) (hloc n q)
  · intro m n hnm
    exact paste_reduction_squares
      (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
        (pbcAdicQuotient X d m n hnm)))
      (e₁ m) (e₂ m) (e₁ n) (e₂ n) (he₁ m n hnm) (he₂ m n hnm)

end AlgebraicGeometry.Scheme
