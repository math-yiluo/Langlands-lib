/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechTotalRegrouping

/-! # Naturality of the explicit principal Čech regrouping

Source: Stacks, Tag 08D1, coefficient maps of total cochains
(blueprint: lem-sc-principal-cech-regroup-naturality).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

private theorem principalCechRowToTerms_naturality
    (F G : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (g : F ⟶ G)
    (p q n : ℤ) (hpq : p + q = n) :
    principalCechRowToTerms r f F p q n hpq ≫
        ((principalCechObjIso r f F).inv ≫ (principalCechFunctor r f).map g ≫
          (principalCechObjIso r f G).hom).f n =
      ((principalCechColumnFunctor r f p).map g).f q ≫
        principalCechRowToTerms r f G p q n hpq := by
  with_unfolding_all
    classical
    dsimp only [principalCechTotal, CochainComplex.of_X, principalCechRowIndex] at *
    have hmap := (principalCechFunctor_exists r f).choose_spec.choose_spec.2 F G g n
    ext x
    funext J
    have hm := hmap (principalCechRowToTerms r f F p q n hpq x) J
      ((principalCechFunctor_exists r f).choose_spec.choose_spec.1 F)
      ((principalCechFunctor_exists r f).choose_spec.choose_spec.1 G)
    change (((principalCechObjIso r f F).inv ≫ (principalCechFunctor r f).map g ≫
      (principalCechObjIso r f G).hom).f n)
        (principalCechRowToTerms r f F p q n hpq x) J = _ at hm
    simp only [ModuleCat.comp_apply]
    refine hm.trans ?_
    by_cases h : (J.val.card : ℤ) = p + 1
    · have hd : q = n + 1 - (J.val.card : ℤ) := by omega
      have hc := congrArg (fun k ↦ k.f q)
        (Limits.Pi.map_π (fun S : principalCechRowIndex r p ↦
          (principalCechSectionFunctor r f S.val.val).map g) ⟨J, h⟩)
      simp only [HomologicalComplex.comp_f] at hc
      have ht : (affineOpenSections A (principalCechIntersection r f J.val)).map
          (g.f q) ≫ (affineOpenSections A (principalCechIntersection r f J.val)).map
            (eqToHom (congrArg G.X hd)) =
        (affineOpenSections A (principalCechIntersection r f J.val)).map
            (eqToHom (congrArg F.X hd)) ≫
          (affineOpenSections A (principalCechIntersection r f J.val)).map
            (g.f (n + 1 - (J.val.card : ℤ))) := by
        cases hd
        simp
      simp only [principalCechRowToTerms_apply, dite_eq_left h]
      have hx := ConcreteCategory.congr_hom hc x
      simp only [ModuleCat.comp_apply] at hx
      erw [hx]
      exact (ConcreteCategory.congr_hom ht
        ((Limits.Pi.π (fun S : principalCechRowIndex r p ↦
          (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q x)).symm
    · simp only [principalCechRowToTerms_apply, dite_eq_right h]
      exact map_zero _

/-- Graded regrouping commutes with maps acting columnwise on sections.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-regroup-naturality).

Proof: precompose with a diagonal coproduct inclusion. The total-map inclusion
formula changes this to the corresponding column map, and the hypothesis he
moves that map past e. Project to a nonempty subset J. If card(J)≠p+1, both
row-to-terms maps are zero in this coordinate. Otherwise, the product-map
projection formula changes the map to the section map of g.f q. Naturality of
g with respect to the degree equality q=n+1-card(J) commutes this map with
the transport used in principalCechRowToTerms. The componentwise specification
of principalCechFunctor_exists identifies the transported chosen functor map
with this same section map. The coproduct universal property and equality of
all subset coordinates give the result. Empty covers have no coordinates.
Neither horizontal differentials nor bounds on F and G are needed. -/
theorem principalCechTotalRegroup_naturality
    (F G : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (g : F ⟶ G)
    (B D : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (eF : ∀ p, B.X p ≅ (principalCechColumnFunctor r f p).obj F)
    (eG : ∀ p, D.X p ≅ (principalCechColumnFunctor r f p).obj G) (φ : B ⟶ D)
    (he : ∀ p, φ.f p ≫ (eG p).hom =
      (eF p).hom ≫ (principalCechColumnFunctor r f p).map g) (n : ℤ) :
    principalCechTotalRegroup r f F B eF n ≫
        ((principalCechObjIso r f F).inv ≫ (principalCechFunctor r f).map g ≫
          (principalCechObjIso r f G).hom).f n =
      (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n ≫
        principalCechTotalRegroup r f G D eG n := by
  with_unfolding_all
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    simp only [principalCechTotalRegroup, Category.assoc,
      HomologicalComplex₂.ι_totalDesc_assoc, HomologicalComplex₂.ιTotal_map_assoc,
      HomologicalComplex₂.ι_totalDesc]
    have hc := congrArg (fun k ↦ k.f q) (he p)
    simp only [HomologicalComplex.comp_f] at hc
    simp only [← Category.assoc]
    rw [hc]
    simp only [Category.assoc]
    rw [← principalCechRowToTerms_naturality r f F G g p q n hpq]

end
end AlgebraicGeometry
