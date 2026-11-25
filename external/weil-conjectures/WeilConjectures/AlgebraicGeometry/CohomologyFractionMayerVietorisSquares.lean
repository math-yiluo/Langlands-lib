/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.CohomologySectionDivision

/-! # Comparison squares on cohomology fractions

Source: Stacks Project, Tag 09MR, Mayer--Vietoris paragraph.
(blueprint: lem-sc-cohomology-fraction-mayer-vietoris-squares)
-/

@[expose] public section

universe uMV

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

private theorem cohomologyRestriction_comp (X : Scheme.{uMV}) (p : ℕ)
    {A B C : X.Opens} (i : B ⟶ A) (j : C ⟶ B) :
    openModuleCohomologyRestriction X.toRingedSpace p i ≫
      openModuleCohomologyRestriction X.toRingedSpace p j =
        openModuleCohomologyRestriction X.toRingedSpace p (j ≫ i) := by
  let : EnoughInjectives (SheafOfModules.{uMV} (moduleRings X.toRingedSpace)) :=
    (moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  unfold openModuleCohomologyRestriction
  rw [← NatTrans.rightDerived_comp]
  congr 1
  apply NatTrans.ext
  funext F
  exact (F.val.presheaf.map_comp i.op j.op).symm

private theorem cohomologyRestriction_square (X : Scheme.{uMV}) (p : ℕ)
    {A B C D : X.Opens} (ab : B ⟶ A) (bd : D ⟶ B) (ac : C ⟶ A) (cd : D ⟶ C) :
    openModuleCohomologyRestriction X.toRingedSpace p ab ≫
      openModuleCohomologyRestriction X.toRingedSpace p bd =
    openModuleCohomologyRestriction X.toRingedSpace p ac ≫
      openModuleCohomologyRestriction X.toRingedSpace p cd := by
  rw [cohomologyRestriction_comp, cohomologyRestriction_comp]
  congr 1

private theorem fraction_addHom_ext {X : Scheme.{uMV}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) {G : Type uMV} [AddCommGroup G]
    (f g : CohomologyFractionPresentation L F s p W →+ G)
    (h : ∀ n ξ, f (cohomologyFraction L F s p W n ξ) =
      g (cohomologyFraction L F s p W n ξ)) : f = g := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    change f ((QuotientAddGroup.mk' _) z) = g ((QuotientAddGroup.mk' _) z)
    induction z using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n ξ => exact h n ξ
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The three fraction-comparison squares commute for any additive maps satisfying
the generator formulas and any module-natural boundary compatible with restricting covers.
Exactness of either row is not assumed.

Source: Stacks Project, Tag 09MR, Mayer--Vietoris paragraph; Tag 01EB naturality.
Proof: Multiplication by s^n on W intersect S is an isomorphism on cohomology, since
s trivializes L there. Thus the formula for c uniquely determines its values on
fractions. For each generator xi/s^n, apply this invertible multiplication to both
sides of the restriction square. The formula for a and the formula for c reduce
both sides to successive restrictions of xi, which agree by functoriality. The two
summands of the difference square are treated in the same way using the formulas
for b; additivity handles their difference. For the boundary square, use the formula
for d and c, restriction compatibility of δ, and naturality of δ for the module
morphism F to F tensor L^n. The lattice equalities identify the two intersection
and union opens in that square; restrictions along their equality are inverse.
After multiplication both sides are the restriction of δ applied to xi, so cancel
multiplication. Finally direct-sum generators generate the quotient additively.
Additivity therefore extends all three equalities from generators to every fraction.
The proof also covers s=0 (S empty), degree zero, and arbitrary opens.
(blueprint: lem-sc-cohomology-fraction-mayer-vietoris-squares). -/
theorem cohomologyFraction_mayerVietoris_squares (X : Scheme.{uMV})
    (L F : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤))
    (U V S : X.Opens) (_hS : (S : Set X) = nonvanishingLocus L s)
    (δ : ∀ (A B : X.Opens) (p : ℕ),
      openModuleCohomology X.toRingedSpace p (A ⊓ B) ⟶
        openModuleCohomology X.toRingedSpace (p + 1) (A ⊔ B))
    (_hrestrict :
      (∀ (A B T : X.Opens) (p : ℕ),
        δ A B p ≫ openModuleCohomologyRestriction X.toRingedSpace (p + 1)
            (homOfLE (sup_le_sup inf_le_left inf_le_left)) =
          openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE (inf_le_inf inf_le_left inf_le_left)) ≫
            δ (A ⊓ T) (B ⊓ T) p))
    (c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F)
    (_hc :
      (∀ (W : X.Opens) (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules)),
        (openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (c W p (cohomologyFraction L F s p W n ξ)) =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : W ⊓ S ≤ W))).app (F ⊗ L.tensorPow n : X.Modules) ξ))
    (a : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊔ V) →+
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V)
      (b : ∀ p : ℕ,
        CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V →+
          CohomologyFractionPresentation L F s p (U ⊓ V))
      (d : ∀ p : ℕ, CohomologyFractionPresentation L F s p (U ⊓ V) →+
        CohomologyFractionPresentation L F s (p + 1) (U ⊔ V))
    (_hform :
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊔ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        a p (cohomologyFraction L F s p (U ⊔ V) n ξ) =
          (cohomologyFraction L F s p U n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ),
          cohomologyFraction L F s p V n
            ((openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE le_sup_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ))) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (cohomologyFraction L F s p U n ξ, 0) = cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_left)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p V).obj (F ⊗ L.tensorPow n : X.Modules)),
        b p (0, cohomologyFraction L F s p V n ξ) = -cohomologyFraction L F s p (U ⊓ V) n
          ((openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE inf_le_right)).app (F ⊗ L.tensorPow n : X.Modules) ξ)) ∧
      (∀ (p n : ℕ) (ξ : (openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        d p (cohomologyFraction L F s p (U ⊓ V) n ξ) =
          cohomologyFraction L F s (p + 1) (U ⊔ V) n
            ((δ U V p).app (F ⊗ L.tensorPow n : X.Modules) ξ))) :
      (∀ (p : ℕ) (x : CohomologyFractionPresentation L F s p (U ⊔ V)),
        c U p (a p x).1 =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S le_sup_left))).app F (c (U ⊔ V) p x) ∧
        c V p (a p x).2 =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S le_sup_right))).app F (c (U ⊔ V) p x)) ∧
      (∀ (p : ℕ)
        (x : CohomologyFractionPresentation L F s p U × CohomologyFractionPresentation L F s p V),
        c (U ⊓ V) p (b p x) =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S inf_le_left))).app F (c U p x.1) -
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_inf_right S inf_le_right))).app F (c V p x.2)) ∧
      (∀ (p : ℕ) (x : CohomologyFractionPresentation L F s p (U ⊓ V)),
        c (U ⊔ V) (p + 1) (d p x) =
          (openModuleCohomologyRestriction X.toRingedSpace (p + 1)
            (homOfLE (inf_sup_right U V S).le)).app F
            ((δ (U ⊓ S) (V ⊓ S) p).app F
              ((openModuleCohomologyRestriction X.toRingedSpace p
                (homOfLE (inf_inf_distrib_right U V S).ge)).app F
                  (c (U ⊓ V) p x)))) := by
  obtain ⟨_, _, _, hmul⟩ := exists_cohomologySection_division X L F s S _hS
  have hcrestrict (A B : X.Opens) (i : B ⟶ A) (p n : ℕ)
      (ξ : (openModuleCohomology X.toRingedSpace p A).obj
        (F ⊗ L.tensorPow n : X.Modules)) :
      c B p (cohomologyFraction L F s p B n
        ((openModuleCohomologyRestriction X.toRingedSpace p i).app
          (F ⊗ L.tensorPow n : X.Modules) ξ)) =
      (openModuleCohomologyRestriction X.toRingedSpace p
        (homOfLE (inf_le_inf_right S (leOfHom i)))).app F
          (c A p (cohomologyFraction L F s p A n ξ)) := by
    apply (hmul B p n).1
    rw [_hc]
    let t : F ⟶ (F ⊗ L.tensorPow n : X.Modules) :=
      (ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n
    let r := openModuleCohomologyRestriction X.toRingedSpace p
      (homOfLE (inf_le_inf_right S (leOfHom i)))
    have hnat := congrArg (fun f ↦ f (c A p (cohomologyFraction L F s p A n ξ)))
      (r.naturality t)
    simp only [ConcreteCategory.comp_apply] at hnat
    change _ = (openModuleCohomology X.toRingedSpace p (B ⊓ S)).map t
      (r.app F (c A p (cohomologyFraction L F s p A n ξ)))
    rw [← hnat, _hc]
    have hsquare := cohomologyRestriction_square X p i (homOfLE inf_le_left)
      (homOfLE inf_le_left) (homOfLE (inf_le_inf_right S (leOfHom i)))
    exact congrArg (fun f ↦ f.app (F ⊗ L.tensorPow n : X.Modules) ξ) hsquare
  obtain ⟨ha, hbU, hbV, hd⟩ := _hform
  refine ⟨?_, ?_, ?_⟩
  · intro p x
    have heU : (c U p).comp ((AddMonoidHom.fst _ _).comp (a p)) =
        ((openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_inf_right S le_sup_left))).app F).hom.comp (c (U ⊔ V) p) := by
      apply fraction_addHom_ext L F s p (U ⊔ V)
      intro n ξ
      change c U p (a p (cohomologyFraction L F s p (U ⊔ V) n ξ)).1 = _
      rw [ha]
      exact hcrestrict (U ⊔ V) U (homOfLE le_sup_left) p n ξ
    have heV : (c V p).comp ((AddMonoidHom.snd _ _).comp (a p)) =
        ((openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_inf_right S le_sup_right))).app F).hom.comp (c (U ⊔ V) p) := by
      apply fraction_addHom_ext L F s p (U ⊔ V)
      intro n ξ
      change c V p (a p (cohomologyFraction L F s p (U ⊔ V) n ξ)).2 = _
      rw [ha]
      exact hcrestrict (U ⊔ V) V (homOfLE le_sup_right) p n ξ
    exact ⟨DFunLike.congr_fun heU x, DFunLike.congr_fun heV x⟩
  · intro p x
    have heU : (c (U ⊓ V) p).comp ((b p).comp (AddMonoidHom.inl _ _)) =
        ((openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_inf_right S inf_le_left))).app F).hom.comp (c U p) := by
      apply fraction_addHom_ext L F s p U
      intro n ξ
      change c (U ⊓ V) p (b p (cohomologyFraction L F s p U n ξ, 0)) = _
      rw [hbU]
      exact hcrestrict U (U ⊓ V) (homOfLE inf_le_left) p n ξ
    have heV : (c (U ⊓ V) p).comp ((b p).comp (AddMonoidHom.inr _ _)) =
        -(((openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_inf_right S inf_le_right))).app F).hom.comp (c V p)) := by
      apply fraction_addHom_ext L F s p V
      intro n ξ
      change c (U ⊓ V) p (b p (0, cohomologyFraction L F s p V n ξ)) = _
      rw [hbV, map_neg, hcrestrict V (U ⊓ V) (homOfLE inf_le_right) p n ξ]
      rfl
    calc
      c (U ⊓ V) p (b p x) =
          c (U ⊓ V) p (b p (x.1, 0)) + c (U ⊓ V) p (b p (0, x.2)) := by
        rw [← map_add, ← map_add]
        congr 2
        exact (Prod.ext (add_zero _) (zero_add _)).symm
      _ = _ := by
        have hu := DFunLike.congr_fun heU x.1
        have hv := DFunLike.congr_fun heV x.2
        change c (U ⊓ V) p (b p (x.1, 0)) = _ at hu
        change c (U ⊓ V) p (b p (0, x.2)) = _ at hv
        rw [hu, hv]
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply, sub_eq_add_neg]
  · intro p x
    let ri := openModuleCohomologyRestriction X.toRingedSpace p
      (homOfLE (inf_inf_distrib_right U V S).ge)
    let ro := openModuleCohomologyRestriction X.toRingedSpace (p + 1)
      (homOfLE (inf_sup_right U V S).le)
    let η := ri ≫ δ (U ⊓ S) (V ⊓ S) p ≫ ro
    have hδ : δ U V p ≫ openModuleCohomologyRestriction X.toRingedSpace (p + 1)
        (homOfLE (inf_le_left : (U ⊔ V) ⊓ S ≤ U ⊔ V)) =
        openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_left : (U ⊓ V) ⊓ S ≤ U ⊓ V)) ≫ η := by
      calc
        _ = δ U V p ≫ (openModuleCohomologyRestriction X.toRingedSpace (p + 1)
              (homOfLE (sup_le_sup inf_le_left inf_le_left)) ≫ ro) := by
          dsimp only [ro]
          rw [cohomologyRestriction_comp]
          rfl
        _ = (openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE (inf_le_inf inf_le_left inf_le_left)) ≫
                δ (U ⊓ S) (V ⊓ S) p) ≫ ro := by
          rw [← Category.assoc, _hrestrict]
        _ = _ := by
          dsimp only [η, ri]
          rw [← Category.assoc, ← Category.assoc, cohomologyRestriction_comp]
          rfl
    have he : (c (U ⊔ V) (p + 1)).comp (d p) =
        (η.app F).hom.comp (c (U ⊓ V) p) := by
      apply fraction_addHom_ext L F s p (U ⊓ V)
      intro n ξ
      change c (U ⊔ V) (p + 1) (d p (cohomologyFraction L F s p (U ⊓ V) n ξ)) = _
      apply (hmul (U ⊔ V) (p + 1) n).1
      rw [hd, _hc]
      let t : F ⟶ (F ⊗ L.tensorPow n : X.Modules) :=
        (ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n
      have hnat := congrArg (fun f ↦ f (c (U ⊓ V) p
        (cohomologyFraction L F s p (U ⊓ V) n ξ))) (η.naturality t)
      simp only [ConcreteCategory.comp_apply] at hnat
      change _ = (openModuleCohomology X.toRingedSpace (p + 1) ((U ⊔ V) ⊓ S)).map t
        (η.app F (c (U ⊓ V) p (cohomologyFraction L F s p (U ⊓ V) n ξ)))
      rw [← hnat, _hc]
      exact congrArg (fun f ↦ f.app (F ⊗ L.tensorPow n : X.Modules) ξ) hδ
    simpa only [AddMonoidHom.comp_apply, η, NatTrans.comp_app,
      ConcreteCategory.comp_apply] using DFunLike.congr_fun he x

end AlgebraicGeometry
