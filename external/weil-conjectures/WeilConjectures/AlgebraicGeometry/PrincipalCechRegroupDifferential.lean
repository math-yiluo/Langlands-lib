/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechTotalRegrouping
import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
import WeilConjectures.CategoryTheory.DoubleComplexTotal

/-! # Differential compatibility of the explicit regrouping

Source: Stacks, Tag 08D1, signs of alternating total cochains
(blueprint: lem-sc-principal-cech-regroup-differential).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

private theorem module_sum_apply {ι : Type*} [Fintype ι]
    {X Y : ModuleCat.{u} A} (g : ι → (X ⟶ Y)) (x : X) :
    (∑ i, g i) x = ∑ i, g i x := by
  change (∑ i, g i).hom x = _
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]

private theorem section_transport_d
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (U : (Spec (.of A)).Opens) (a b c d : ℤ) (h : a = c) (h' : b = d) :
    (affineOpenSections A U).map (eqToHom (congrArg F.X h)) ≫
      (affineOpenSections A U).map (F.d c d) =
    (affineOpenSections A U).map (F.d a b) ≫
      (affineOpenSections A U).map (eqToHom (congrArg F.X h')) := by
  subst c d
  simp

private theorem section_transport_restriction
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (U V : (Spec (.of A)).Opens) (hVU : V ≤ U)
    (a b c : ℤ) (h : a = b) (h' : b = c) :
    (affineOpenSections A U).map (eqToHom (congrArg F.X h)) ≫
      (affineOpenSections A U).map (eqToHom (congrArg F.X h')) ≫
        (modulesSpecToSheaf.obj (F.X c)).obj.map (homOfLE hVU).op =
    (modulesSpecToSheaf.obj (F.X a)).obj.map (homOfLE hVU).op ≫
      (affineOpenSections A V).map (eqToHom (congrArg F.X (h.trans h'))) := by
  subst b c
  simp [affineOpenSections]

private theorem module_zsmul_apply {X Y : ModuleCat.{u} A}
    (g : X ⟶ Y) (k : ℤ) (x : X) : (k • g) x = k • g x := by
  change (k • g).hom x = _
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply]

/-- The total differential of one row has its horizontal and signed vertical parts.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-regroup-differential).

Proof: evaluate at a nonempty subset J. The vertical term is zero unless
card(J)=p+1. In that row, the product projection is a chain map and degree
transports commute with the coefficient differential; p=card(J)-1 is
nonnegative, so p.negOnePow gives exactly the scalar (-1)^(card(J)-1).
The horizontal term is zero unless card(J)=p+2: erasing a member lowers
cardinality by one. In that row, the product projection of the horizontal
map is its defining sum of signed restrictions. The two successive degree
transports compose to the unique equality transport from q to
n+2-card(J), so each summand equals the corresponding explicit differential
summand. Empty deletions give zero. Equality of all subset coordinates
proves equality of module maps, including empty covers and unsupported rows. -/
private theorem principalCechRowToTerms_differential
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    principalCechRowToTerms r f F p q n hpq ≫ principalCechDifferential r f F n =
      ((principalCechHorizontal r f p).app F).f q ≫
        principalCechRowToTerms r f F (p + 1) q (n + 1) (by omega) +
      p.negOnePow • (((principalCechColumnFunctor r f p).obj F).d q (q + 1) ≫
        principalCechRowToTerms r f F p (q + 1) (n + 1) (by omega)) := by
  with_unfolding_all
    classical
    dsimp only [principalCechTerms, principalCechRowIndex] at *
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change (principalCechDifferential_exists r f F n).choose
      (principalCechRowToTerms r f F p q n hpq x) = _
    rw [(principalCechDifferential_exists r f F n).choose_spec]
    funext J
    simp only [principalCechDifferentialValue, id_eq]
    simp only [ModuleCat.hom_add, LinearMap.add_apply, Pi.add_apply,
      ModuleCat.hom_smul, LinearMap.smul_apply, Pi.smul_apply,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    refine (congrArg₂ (· + ·) ?_ ?_).trans (add_comm _ _)
    · by_cases h : (J.val.card : ℤ) = p + 1
      · have hd : q = n + 1 - (J.val.card : ℤ) := by omega
        have hd' : q + 1 = n + 1 + 1 - (J.val.card : ℤ) := by omega
        change _ = p.negOnePow •
          principalCechRowToTerms r f F p (q + 1) (n + 1) (by omega)
            (((principalCechColumnFunctor r f p).obj F).d q (q + 1) x) J
        simp only [principalCechRowToTerms_apply, dite_eq_left h]
        have hs : ((J.val.card - 1 : ℕ) : ℤ) = p := by
          have := J.property.card_pos
          omega
        have hsign : ((p.negOnePow : ℤ) : A) = (-1 : A) ^ (J.val.card - 1) := by
          rw [← hs, Int.cast_negOnePow_natCast]
        rw [Units.smul_def, ← Int.cast_smul_eq_zsmul A, hsign]
        apply congrArg (_ • ·)
        let π := Limits.Pi.π (fun S : principalCechRowIndex r p ↦
          (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩
        have hc := π.comm q (q + 1)
        dsimp only [principalCechSectionFunctor,
          Functor.mapHomologicalComplex_obj_d] at hc
        have ht : (affineOpenSections A (principalCechIntersection r f J.val)).map
            (eqToHom (congrArg F.X hd)) ≫
              (affineOpenSections A (principalCechIntersection r f J.val)).map
                (F.d (n + 1 - (J.val.card : ℤ))
                  (n + 1 + 1 - (J.val.card : ℤ))) =
          (affineOpenSections A (principalCechIntersection r f J.val)).map
            (F.d q (q + 1)) ≫
              (affineOpenSections A (principalCechIntersection r f J.val)).map
                (eqToHom (congrArg F.X hd')) := by
          exact section_transport_d F _ q (q + 1) _ _ hd hd'
        exact (ConcreteCategory.congr_hom ht (π.f q x)).trans
          (congrArg
            ((affineOpenSections A (principalCechIntersection r f J.val)).map
              (eqToHom (congrArg F.X hd')))
            (ConcreteCategory.congr_hom hc x))
      · change _ = p.negOnePow •
          principalCechRowToTerms r f F p (q + 1) (n + 1) (by omega)
            (((principalCechColumnFunctor r f p).obj F).d q (q + 1) x) J
        simp only [principalCechRowToTerms_apply, dite_eq_right h, map_zero, smul_zero]
    · change _ = principalCechRowToTerms r f F (p + 1) q (n + 1) (by omega)
        (((principalCechHorizontal r f p).app F).f q x) J
      by_cases h : (J.val.card : ℤ) = (p + 1) + 1
      · simp only [principalCechRowToTerms_apply, dite_eq_left h]
        have hc := congrArg (fun k ↦ k.f q)
          (Limits.Pi.lift_comp_π (fun S : principalCechRowIndex r (p + 1) ↦
            ∑ j : S.val.val,
              if hn : (S.val.val.erase j.val).Nonempty then
                ((-1 : ℤ) ^ (S.val.val.filter (fun k ↦ k < j.val)).card) •
                  (Limits.Pi.π (fun T : principalCechRowIndex r p ↦
                    (principalCechSectionFunctor r f T.val.val).obj F)
                    ⟨⟨S.val.val.erase j.val, hn⟩,
                      principalCechRowIndex_erase_card r p S j⟩ ≫
                    (principalCechEraseRestriction r f S.val.val j.val).app F)
              else 0) ⟨J, h⟩)
        simp only [HomologicalComplex.comp_f] at hc
        have hx := ConcreteCategory.congr_hom hc x
        change ((principalCechHorizontal r f p).app F).f q ≫
          (Limits.Pi.π (fun S : principalCechRowIndex r (p + 1) ↦
            (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q = _ at hc
        simp only [ModuleCat.comp_apply] at hx
        simp only [← HomologicalComplex.Hom.fAddMonoidHom_apply] at hx
        rw [map_sum] at hx
        simp only [HomologicalComplex.Hom.fAddMonoidHom_apply] at hx
        erw [hx]
        rw [module_sum_apply]
        erw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        split
        next hn =>
          have he : ((J.val.erase j.val).card : ℤ) = p + 1 := by
            have := Finset.card_erase_add_one j.property
            omega
          rw [dite_eq_left he]
          simp only [HomologicalComplex.zsmul_f_apply,
            HomologicalComplex.comp_f]
          rw [module_zsmul_apply]
          erw [map_zsmul]
          rw [← Int.cast_smul_eq_zsmul A]
          push_cast
          apply congrArg (_ • ·)
          have hd : q = n + 1 - ((J.val.erase j.val).card : ℤ) := by omega
          have hd' := principalCech_erase_degree r J.val j.val j.property n
          have ht := section_transport_restriction F
            (principalCechIntersection r f (J.val.erase j.val))
            (principalCechIntersection r f J.val)
            (principalCechIntersection_erase_le r f J.val j.val) q _ _ hd hd'
          exact ConcreteCategory.congr_hom ht
            ((Limits.Pi.π (fun S : principalCechRowIndex r p ↦
              (principalCechSectionFunctor r f S.val.val).obj F)
              ⟨⟨J.val.erase j.val, hn⟩, he⟩).f q x)
        next hn =>
          simp only [HomologicalComplex.zero_f_apply]
          erw [map_zero]
      · simp only [principalCechRowToTerms_apply, dite_eq_right h]
        apply Finset.sum_eq_zero
        intro j _
        split
        next hn =>
          have he : ((J.val.erase j.val).card : ℤ) ≠ p + 1 := by
            have := Finset.card_erase_add_one j.property
            omega
          rw [dite_eq_right he]
          erw [map_zero, map_zero, smul_zero]
        next hn => rfl


/-- The explicit graded regrouping commutes with the total differential.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-regroup-differential).

Proof: precompose the equation with every diagonal coproduct inclusion and read
its subset coordinates. The vertical part of Mathlib's total differential has
sign p.negOnePow. A nonzero coordinate has card(J)=p+1 and therefore p≥0;
this sign acts as (-1 : A)^(card(J)-1). The chain-map equation of e p identifies
the vertical differential with the section differential in this coordinate.
For the horizontal part, the displayed hypothesis identifies the column map
with principalCechHorizontal. Its subset projection is the sum over j in J of
(-1) raised to the number of earlier indices times restriction from J.erase j.
The source row has card(J.erase j)=p+1, and its vertical degree equals the
coefficient degree of the target; principalCech_erase_degree gives precisely
the transport in principalCechDifferentialValue. Empty erased sets contribute
zero on both sides. These are exactly the two terms of that formula, which
principalCechDifferential_exists identifies with the chosen differential.
Coproduct inclusions and product projections detect equality. For an empty
cover there are no subset coordinates; outside the supported rows the sources
are zero. This argument imposes no bound on the vertical degrees. -/
theorem principalCechTotalRegroup_comm
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (B : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (e : ∀ p, B.X p ≅ (principalCechColumnFunctor r f p).obj F)
    (he : ∀ p, B.d p (p + 1) ≫ (e (p + 1)).hom =
      (e p).hom ≫ (principalCechHorizontal r f p).app F) (n : ℤ) :
    principalCechTotalRegroup r f F B e n ≫ principalCechDifferential r f F n =
      (B.total (ComplexShape.up ℤ)).d n (n + 1) ≫
        principalCechTotalRegroup r f F B e (n + 1) := by
  with_unfolding_all
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hh : (p + 1) + q = n + 1 := by
      change p + q = n at hpq
      omega
    have hv : p + (q + 1) = n + 1 := by
      change p + q = n at hpq
      omega
    rw [HomologicalComplex₂.total_d]
    simp only [← Category.assoc, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Preadditive.add_comp]
    rw [B.d₁_eq (ComplexShape.up ℤ) (by simp) q (n + 1) hh,
      B.d₂_eq (ComplexShape.up ℤ) p (by simp) (n + 1) hv]
    simp only [principalCechTotalRegroup, Category.assoc,
      HomologicalComplex₂.ι_totalDesc,
      Linear.units_smul_comp]
    have hc := congrArg (fun k ↦ k.f q) (he p)
    simp only [HomologicalComplex.comp_f] at hc
    rw [principalCechRowToTerms_differential r f F p q n hpq]
    simp only [Preadditive.comp_add, Linear.comp_units_smul]
    rw [← Category.assoc, ← hc]
    have vc := (e p).hom.comm q (q + 1)
    simp only [← Category.assoc]
    rw [vc]
    simp [ComplexShape.ε₁, ComplexShape.ε₂, Category.assoc]

end
end AlgebraicGeometry
