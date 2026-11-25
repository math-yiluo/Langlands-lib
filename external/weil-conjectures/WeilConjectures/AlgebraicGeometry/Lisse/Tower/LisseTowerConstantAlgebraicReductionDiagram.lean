/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantStalkModels

/-! # Local algebraic diagrams over the constant completion ring

## References

* Stacks Tag 09BV, finite-ring derived local constancy and compatible trivializations in
  amplification (c)
* Tag 09BV, the derived local-constancy and simultaneous-trivialization argument in
  amplification (c)
* Tags 06YY and 093J
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] constantAdicFiniteRealization

private theorem relativelyFiniteLisse_of_iso
    {X Y : Scheme.{u}} (g : Y ⟶ X) (B : Type (u + 1)) [CommRing B]
    {F G : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))}
    (e : F ≅ G) (hG : IsRelativelyFiniteLisseModule g B G) :
    IsRelativelyFiniteLisseModule g B F := by
  obtain ⟨S, hS, hs⟩ := hG
  refine ⟨S, hS, fun V f hf ↦ ?_⟩
  obtain ⟨N, hN, ⟨i⟩⟩ := hs V f hf
  exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ V).mapIso e ≪≫ i⟩⟩

private theorem comparison_unit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (A : C ⥤ D) (R : C' ⥤ C) (H : D' ⥤ D) (F : C' ⥤ D')
    (k : R ⋙ A ≅ F ⋙ H) {L : C ⥤ C'} (a : L ⊣ R)
    {B : D ⥤ D'} (b : B ⊣ H) (E : C)
    (q : B.obj (A.obj E) ⟶ F.obj (L.obj E))
    (hq : (b.homEquiv _ _) q = A.map (a.unit.app E) ≫ k.hom.app (L.obj E))
    {K : C'} (i : L.obj E ≅ K) {M : D'} (j : F.obj K ≅ M) :
    b.unit.app (A.obj E) ≫ H.map (q ≫ F.map i.hom ≫ j.hom) =
      A.map (a.unit.app E ≫ R.map i.hom) ≫ k.hom.app K ≫ H.map j.hom := by
  have hk : A.map (R.map i.hom) ≫ k.hom.app K =
      k.hom.app (L.obj E) ≫ H.map (F.map i.hom) := k.hom.naturality i.hom
  change (b.homEquiv _ _) (q ≫ F.map i.hom ≫ j.hom) = _
  rw [b.homEquiv_naturality_right, hq]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ A.map (a.unit.app E) ≫ f ≫ H.map j.hom) hk.symm

private theorem paste_unit_square
    {C D : Type*} [Category* C] [Category* D] (A : C ⥤ D)
    {E Pm Pn : C} {Mm Mn : D}
    (wm : E ⟶ Pm) (wn : E ⟶ Pn) (s : Pm ⟶ Pn)
    (zm : A.obj Pm ⟶ Mm) (zn : A.obj Pn ⟶ Mn) (v : Mm ⟶ Mn)
    (vm : A.obj E ⟶ Mm) (vn : A.obj E ⟶ Mn)
    (hm : vm = A.map wm ≫ zm) (hn : vn = A.map wn ≫ zn)
    (hmodel : zm ≫ v = A.map s ≫ zn) (hw : wm ≫ s = wn) : vm ≫ v = vn := by
  rw [hm, Category.assoc, hmodel, ← Category.assoc, ← A.map_comp, hw, ← hn]

private theorem reduction_square_of_units
    {D Dm Dn : Type*} [Category* D] [Category* Dm] [Category* Dn]
    {Bm : D ⥤ Dm} {Hm : Dm ⥤ D} (am : Bm ⊣ Hm)
    {Bn : D ⥤ Dn} {Hn : Dn ⥤ D} (an : Bn ⊣ Hn)
    (T : Dn ⥤ Dm) (c : T ⋙ Hm ≅ Hn)
    (Q : D) {Mm : Dm} {Mn : Dn}
    (em : Bm.obj Q ⟶ Mm) (en : Bn.obj Q ⟶ Mn) (t : Mm ⟶ T.obj Mn)
    (h : am.unit.app Q ≫ Hm.map em ≫ Hm.map t ≫ c.hom.app Mn =
      an.unit.app Q ≫ Hn.map en) :
    em ≫ t =
      (am.homEquiv Q (T.obj (Bn.obj Q))).symm
        (an.unit.app Q ≫ c.inv.app (Bn.obj Q)) ≫ T.map en := by
  apply (am.homEquiv Q (T.obj Mn)).injective
  simp only [am.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_apply]
  have h' := congrArg (fun f ↦ f ≫ c.inv.app Mn) h
  have hn : Hn.map en ≫ c.inv.app Mn = c.inv.app (Bn.obj Q) ≫ Hm.map (T.map en) :=
    c.inv.naturality en
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj] at h'
  simpa only [Category.assoc, Category.comp_id, hn] using h'

-- Keep the name of the compatibility binder, unused in its conclusion.
set_option linter.unusedVariables false in
/-- Finite local diagrams and effective cones over the constant algebraic ring.
This assertion has no completed ring sheaf, completed realization or scalar maps
phi and beta. Inverse image retains exactly the constant algebraic coefficient ring. -/
theorem lisse_tower_constant_algebraic_reduction_diagram
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
              (∀ (n : ℕ) (q : ℤ),
                IsRelativelyFiniteLisseModule (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
                  ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                    (pbcLevelConstantComparison X d n).hom)).obj
                      ((DerivedCategory.homologyFunctor _ q).obj
                        ((pbcDerivedExtend
                          (constantAdicFiniteProjection (U.hom ≫ g) d n)).obj
                            ((constantAdicFiniteRealization (U.hom ≫ g) d).obj E))))) ∧
              ∃ e : ∀ n : ℕ,
                (pbcDerivedExtend (constantAdicFiniteProjection (U.hom ≫ g) d n)).obj
                    ((constantAdicFiniteRealization (U.hom ≫ g) d).obj E) ≅
                  (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
                    (M.level n),
                ∀ (m n : ℕ) (hnm : n ≤ m),
                  (e m).hom ≫ adicTowerRestrictedTransition d (U.hom ≫ g) M m n hnm =
                    pbcReductionTransition
                (constantAdicFiniteProjection (U.hom ≫ g) d m)
                ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicQuotient X d m n hnm))
                (constantAdicFiniteProjection (U.hom ≫ g) d n)
                (constantAdicFiniteProjection_comp (U.hom ≫ g) d m n hnm)
                ((constantAdicFiniteRealization (U.hom ≫ g) d).obj E) ≫
                      (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
                        (pbcAdicQuotient X d m n hnm))).map (e n).hom := by
  classical
  obtain ⟨V, hV, hlocal⟩ := lisse_tower_constant_stalk_models X Y g d M hbounded hlisse
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨K, t, ht, hzero, hfinite, b, hMlisse, hb⟩ := hlocal U f hf
  refine ⟨K, t, ht, hzero, hfinite, ?_⟩
  intro R s E L adj e₀ he₀
  let a := constantAdicFiniteRealization (U.hom ≫ g) d
  let H (n : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (U.hom ≫ g) d n)
  let F (n : ℕ) := constantAdicQuotientRealization (U.hom ≫ g) d n
  let k (n : ℕ) := constantAdicQuotientRightIso (U.hom ≫ g) d n
  let w (n : ℕ) := (adj n).unit.app E ≫ (R n).mapDerivedCategory.map (e₀ n).hom
  let z (n : ℕ) := (k n).hom.app (K n) ≫ (H n).map (b n).hom
  let q (n : ℕ) :=
    ((pbcDerivedScalarAdjunction (constantAdicFiniteProjection (U.hom ≫ g) d n)).homEquiv
      (a.obj E) ((F n).obj ((L n).obj E))).symm
        (a.map ((adj n).unit.app E) ≫ (k n).hom.app ((L n).obj E))
  have hq (n : ℕ) : IsIso (q n) :=
    (constantAdicQuotientScalarComparison X d n).exists.choose_spec.2
      U.left (U.hom ≫ g) E (L n) (adj n)
  let e (n : ℕ) := asIso (q n) ≪≫ (F n).mapIso (e₀ n) ≪≫ b n
  have he (n : ℕ) :
      (pbcDerivedScalarAdjunction (constantAdicFiniteProjection (U.hom ≫ g) d n)).unit.app
          (a.obj E) ≫ (H n).map (e n).hom = a.map (w n) ≫ z n := by
    exact comparison_unit a _ (H n) (F n) (k n) (adj n)
      (pbcDerivedScalarAdjunction (constantAdicFiniteProjection (U.hom ≫ g) d n)) E
      (q n) (Equiv.apply_symm_apply _ _) (e₀ n) (b n)
  refine ⟨?_, e, ?_⟩
  · intro n q
    apply relativelyFiniteLisse_of_iso (U.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso (e n)))
    exact hMlisse n q
  · intro m n h
    apply reduction_square_of_units
      (pbcDerivedScalarAdjunction (constantAdicFiniteProjection (U.hom ≫ g) d m))
      (pbcDerivedScalarAdjunction (constantAdicFiniteProjection (U.hom ≫ g) d n))
      (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
        (pbcAdicQuotient X d m n h)))
      (pbcDerivedRestrictComp
        (constantAdicFiniteProjection (U.hom ≫ g) d m)
        ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicQuotient X d m n h))
        (constantAdicFiniteProjection (U.hom ≫ g) d n)
        (constantAdicFiniteProjection_comp (U.hom ≫ g) d m n h))
      (a.obj E) (e m).hom (e n).hom
      (adicTowerRestrictedTransition d (U.hom ≫ g) M m n h)
    have hw : w m ≫ (Functor.ofOpSequence
        (X := fun j : ℕ ↦ (R j).mapDerivedCategory.obj (K j)) s).map
          (homOfLE h).op = w n := by
      simpa only [w, Category.assoc] using he₀ m n h
    have hh := paste_unit_square a (w m) (w n)
      ((Functor.ofOpSequence (X := fun j : ℕ ↦ (R j).mapDerivedCategory.obj (K j)) s).map
        (homOfLE h).op) (z m) (z n)
      ((H m).map (adicTowerRestrictedTransition d (U.hom ≫ g) M m n h) ≫
        (pbcDerivedRestrictComp
          (constantAdicFiniteProjection (U.hom ≫ g) d m)
          ((adicTowerInverseImage (U.hom ≫ g)).map (pbcAdicQuotient X d m n h))
          (constantAdicFiniteProjection (U.hom ≫ g) d n)
          (constantAdicFiniteProjection_comp (U.hom ≫ g) d m n h)).hom.app
            ((adicTowerPullback (U.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj (M.level n)))
      _ _ (he m) (he n)
      (by simpa only [z, k, H, a, Category.assoc] using hb m n h) hw
    simpa only [Category.assoc] using hh

end AlgebraicGeometry.Scheme
