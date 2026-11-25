/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # Čech totalization preserves coefficient homotopies

Source: Stacks Project, Tag 08C1, functoriality verification; the explicit signed
homotopy calculation in the parent node's proof Step 3.
(blueprint: lem-sc-alternating-cech-total-homotopy)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem additiveComplexFunctor_total_map_homotopy
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [∀ B : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      B.HasTotal (ComplexShape.up ℤ)]
    (A : C ⥤ CochainComplex D ℤ) [A.Additive]
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    let T := A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)
    Nonempty (Homotopy (T.map f) (T.map g)) := by
  classical
  let B := (A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K
  let E := (A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L
  let H : ∀ n m : ℤ, (B.total (ComplexShape.up ℤ)).X n ⟶
      (E.total (ComplexShape.up ℤ)).X m := fun n m ↦
    B.totalDesc (fun p q _ ↦ p.negOnePow •
      ((A.map (h.hom q (q - 1))).f p ≫ E.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) m))
  have hH (p q n m : ℤ) (hpq : p + q = n) :
      B.ιTotal (ComplexShape.up ℤ) p q n hpq ≫ H n m =
        p.negOnePow • ((A.map (h.hom q (q - 1))).f p ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) m) := by
    exact B.ι_totalDesc _ _ _ _
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rw [hH]
    have hz : ¬ p + (q - 1) = m := by
      change ¬ m + 1 = n at hnm
      change p + q = n at hpq
      omega
    rw [E.ιTotalOrZero_eq_zero _ _ _ _ hz]
    simp
  · intro n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p + q = n at hpq
    subst n
    change B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
      (HomologicalComplex₂.total.map ((A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f)
        (ComplexShape.up ℤ)).f (p + q) = _
    rw [HomologicalComplex₂.ιTotal_map]
    simp only [Preadditive.comp_add]
    change _ =
      B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
          (B.total (ComplexShape.up ℤ)).d (p + q) (p + q + 1) ≫
            H (p + q + 1) (p + q) +
        B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
          H (p + q) (p + q - 1) ≫
            (E.total (ComplexShape.up ℤ)).d (p + q - 1) (p + q) +
        B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
          (HomologicalComplex₂.total.map ((A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map g)
            (ComplexShape.up ℤ)).f (p + q)
    simp only [← Category.assoc]
    rw [HomologicalComplex₂.ιTotal_map, hH]
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      B.d₁_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      B.d₂_eq' (ComplexShape.up ℤ) p (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
    simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = 1 from rfl, one_smul]
    rw [B.ιTotalOrZero_eq _ _ _ _ (by change p + 1 + q = p + q + 1; omega),
      B.ιTotalOrZero_eq _ _ _ _ (by change p + (q + 1) = p + q + 1; omega)]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, hH]
    rw [E.ιTotalOrZero_eq (ComplexShape.up ℤ) p (q - 1) (p + q - 1)
      (by change p + (q - 1) = p + q - 1; omega)]
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      E.d₁_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      E.d₂_eq' (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel (q - 1) q by simp)]
    simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q - 1) = 1 from rfl, one_smul,
      Linear.comp_units_smul, smul_smul,
      Preadditive.comp_add, smul_add]
    rw [show q + 1 - 1 = q by omega]
    change (A.map (f.f q)).f p ≫ E.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl = _
    change _ =
      (p + 1).negOnePow • ((A.obj (K.X q)).d p (p + 1) ≫
        (A.map (h.hom q (q - 1))).f (p + 1) ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) (q - 1) (p + q)) +
      (p.negOnePow * p.negOnePow) • ((A.map (K.d q (q + 1))).f p ≫
        (A.map (h.hom (q + 1) q)).f p ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) p q (p + q)) +
      (p.negOnePow • ((A.map (h.hom q (q - 1))).f p ≫
        (A.obj (L.X (q - 1))).d p (p + 1) ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) (q - 1) (p + q)) +
      (p.negOnePow * p.negOnePow) • ((A.map (h.hom q (q - 1))).f p ≫
        (A.map (L.d (q - 1) q)).f p ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) p q (p + q))) +
      (A.map (g.f q)).f p ≫ E.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl
    rw [Int.units_mul_self, one_smul,
      E.ιTotalOrZero_eq (ComplexShape.up ℤ) p q (p + q) rfl, Int.negOnePow_succ]
    rw [← (A.map (h.hom q (q - 1))).comm_assoc p (p + 1)]
    rw [Units.neg_smul, one_smul]
    have hh := congrArg (fun z ↦ (A.map z).f p) (h.comm q)
    simp only [dNext_eq _ (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (q - 1) q by simp),
      Functor.map_add, Functor.map_comp, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f] at hh
    rw [hh]
    simp only [Preadditive.add_comp, Category.assoc]
    abel


/-- A coefficient homotopy induces a homotopy of the actual Čech total maps.
No covering hypothesis or injectivity is needed.

Source: Stacks Project, Tag 08C1, functoriality verification; parent node
lem-sc-kinjective-alternating-cech-augmentation-quasi-iso, proof Step 3
(blueprint: lem-sc-alternating-cech-total-homotopy).

Proof: Write h for the coefficient homotopy. In total degree n, on the summand
with Čech degree p and coefficient degree q, p+q=n, define H by restricting
h from coefficient degree q to q-1, multiplying by (-1)^p, and including the
result in the (p,q-1) total summand. Use the coproduct universal property to
assemble these maps; set the other degree components to zero. The restrictions
are natural in each open set. Consequently the horizontal pieces in dH+Hd
cancel: the two restrictions agree, while the signs at p and p+1 are opposite.
The vertical differential has sign (-1)^p as well, so the vertical contributions
are the restriction of dh+hd, hence the restriction of f-g. The total summand
inclusions jointly detect equality, proving the homotopy equation. The construction
works for arbitrary complexes and any finite family, including the empty family,
where there are no summands. Negative Čech degrees vanish by extension by zero. -/
theorem alternatingCechTotal_map_homotopy
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    {f g : K ⟶ L} (h : Homotopy f g) :
    Nonempty (Homotopy ((alternatingCechTotalFunctor U).map f)
      ((alternatingCechTotalFunctor U).map g)) := by
  exact additiveComplexFunctor_total_map_homotopy (alternatingCechModuleFunctor U) h

end AlgebraicGeometry
