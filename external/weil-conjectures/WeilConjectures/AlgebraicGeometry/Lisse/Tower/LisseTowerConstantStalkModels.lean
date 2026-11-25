/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerStalkLevelModels
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerCompatibleStalkMarkings

/-! # Compatible constant stalk models before algebraic effectivity

## References

* Stacks Tag 09BV, finite derived local constancy and compatible trivializations
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A finite lisse normalized tower is locally a constant algebraic tower. The
comparison is stated after restriction to the common constant completion ring.
It constructs no effective cone E and asserts no descent of such a cone. -/
theorem lisse_tower_constant_stalk_models
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
          ∃ b : ∀ n : ℕ,
              (constantAdicQuotientRealization (U.hom ≫ g) d n).obj (K n) ≅
                (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
                  (M.level n),
            (∀ (n : ℕ) (q : ℤ),
              IsRelativelyFiniteLisseModule (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
                ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                  (pbcLevelConstantComparison X d n).hom)).obj
                    ((DerivedCategory.homologyFunctor _ q).obj
                      ((adicTowerPullback (U.hom ≫ g)
                        ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) ∧
            let a := constantAdicFiniteRealization (U.hom ≫ g) d
            let H (n : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (U.hom ≫ g) d n)
            let z (n : ℕ) :=
              (constantAdicQuotientRightIso (U.hom ≫ g) d n).hom.app (K n) ≫
                (H n).map (b n).hom
            ∀ (m n : ℕ) (h : n ≤ m),
              z m ≫ (H m).map (adicTowerRestrictedTransition d (U.hom ≫ g) M m n h) ≫
                (pbcDerivedRestrictComp
                  (constantAdicFiniteProjection (U.hom ≫ g) d m)
                  ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicQuotient X d m n h))
                  (constantAdicFiniteProjection (U.hom ≫ g) d n)
                  (constantAdicFiniteProjection_comp (U.hom ≫ g) d m n h)).hom.app
                    ((adicTowerPullback (U.hom ≫ g)
                      ((pbcAdicRings X d).obj (op n))).obj (M.level n)) =
                a.map ((Functor.ofOpSequence
                  (X := fun k : ℕ ↦ (R k).mapDerivedCategory.obj (K k)) s).map
                    (homOfLE h).op) ≫ z n := by
  classical
  obtain ⟨V, hV, hlocal⟩ := lisse_tower_stalk_level_models X Y g d M hbounded hlisse
  choose K t ht hz hf hl hm using hlocal
  have hmark (U : Y.ProEt) (f : U ⟶ ⊤_ Y.ProEt) (hu : V f) := by
    apply lisse_tower_compatible_stalk_markings X Y g d M U
      (K U f hu) (t U f hu) (ht U f hu) _ (hf U f hu) (hm U f hu)
    intro n
    obtain ⟨a, b, hab⟩ := hbounded n
    exact ⟨a, b, fun q hq ↦ hz U f hu n q (hab q hq)⟩
  choose T hT hb using hmark
  refine ⟨Sieve.bind V (fun {U} {f} hu ↦ T U f hu),
    (ProEt.topology Y).bind_covering hV (fun {_} {_} hu ↦ hT _ _ hu), ?_⟩
  rintro W f ⟨U, w, u, hu, hw, rfl⟩
  obtain ⟨b, hcompat⟩ := hb U u hu W w hw
  exact ⟨K U u hu, t U u hu, ht U u hu, hz U u hu, hf U u hu,
    b, hl U u hu W w, hcompat⟩

end AlgebraicGeometry.Scheme
