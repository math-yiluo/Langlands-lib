/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns
public import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Regrouping the graded terms of principal Čech columns

Source: Stacks, Tag 08D1, alternating total cochains
(blueprint: lem-sc-principal-cech-total-regrouping).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex (SheafOfModules.{u}
  (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Include a single product row into the explicit cochains, extending by zero.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-total-regrouping). -/
def principalCechRowToTerms (p q n : ℤ) (hpq : p + q = n) :
    ((principalCechColumnFunctor r f p).obj F).X q ⟶ principalCechTerms r f F n := by
  classical
  let component (J : {J : Finset (Fin r) // J.Nonempty}) :
      ((principalCechColumnFunctor r f p).obj F).X q ⟶
        (affineOpenSections A (principalCechIntersection r f J.val)).obj
          (F.X (n + 1 - (J.val.card : ℤ))) :=
    if h : (J.val.card : ℤ) = p + 1 then
      (Limits.Pi.π (fun S : principalCechRowIndex r p ↦
        (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q ≫
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (eqToHom (congrArg F.X (by omega : q = n + 1 - (J.val.card : ℤ))))
    else 0
  exact ModuleCat.ofHom
    { toFun := fun x J ↦ component J x
      map_add' := fun x y ↦ by funext J; exact (component J).hom.map_add x y
      map_smul' := fun a x ↦ by funext J; exact (component J).hom.map_smul a x }

/-- The subset coordinate of a row inclusion is its projection, or zero off the row.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-total-regrouping). -/
theorem principalCechRowToTerms_apply (p q n : ℤ) (hpq : p + q = n)
    (x : ((principalCechColumnFunctor r f p).obj F).X q)
    (J : {J : Finset (Fin r) // J.Nonempty}) :
    principalCechRowToTerms r f F p q n hpq x J =
      if h : (J.val.card : ℤ) = p + 1 then
        (affineOpenSections A (principalCechIntersection r f J.val)).map
          (eqToHom (congrArg F.X (by omega : q = n + 1 - (J.val.card : ℤ))))
          ((Limits.Pi.π (fun S : principalCechRowIndex r p ↦
            (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q x)
      else 0 := by
  classical
  change (if h : (J.val.card : ℤ) = p + 1 then
    (Limits.Pi.π (fun S : principalCechRowIndex r p ↦
      (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q ≫
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (eqToHom (congrArg F.X (by omega : q = n + 1 - (J.val.card : ℤ))))
    else 0) x = _
  split_ifs <;> rfl

/-- The explicit graded regrouping map, for any bicomplex with the given columns.
It uses the coproduct universal property, rather than a chosen existence witness.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-total-regrouping). -/
def principalCechTotalRegroup
    (B : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (e : ∀ p, B.X p ≅ (principalCechColumnFunctor r f p).obj F) (n : ℤ) :
    (B.total (ComplexShape.up ℤ)).X n ⟶ principalCechTerms r f F n :=
  B.totalDesc (fun p q h ↦ (e p).hom.f q ≫ principalCechRowToTerms r f F p q n h)

set_option backward.isDefEq.respectTransparency false in
private def rowRetract (p q n : ℤ) (h : p + q = n) :
    principalCechTerms r f F n ⟶ ((principalCechColumnFunctor r f p).obj F).X q :=
  Limits.Pi.lift (fun S : principalCechRowIndex r p ↦
    ModuleCat.ofHom (LinearMap.proj S.val : principalCechTerms r f F n →ₗ[A] _) ≫
      (affineOpenSections A (principalCechIntersection r f S.val.val)).map
        (eqToHom (congrArg F.X (show n + 1 - (S.val.val.card : ℤ) = q by
          have hc := S.property
          omega)))) ≫
    inv (piComparison (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) q)
      (fun S : principalCechRowIndex r p ↦
        (principalCechSectionFunctor r f S.val.val).obj F))

set_option backward.isDefEq.respectTransparency false in
private theorem rowRetract_π (p q n : ℤ) (h : p + q = n)
    (S : principalCechRowIndex r p) :
    rowRetract r f F p q n h ≫
      (Limits.Pi.π (fun S : principalCechRowIndex r p ↦
        (principalCechSectionFunctor r f S.val.val).obj F) S).f q =
    ModuleCat.ofHom (LinearMap.proj S.val : principalCechTerms r f F n →ₗ[A] _) ≫
      (affineOpenSections A (principalCechIntersection r f S.val.val)).map
        (eqToHom (congrArg F.X (show n + 1 - (S.val.val.card : ℤ) = q by
          have hc := S.property
          omega))) := by
  simp only [rowRetract, Category.assoc]
  change _ ≫ inv (piComparison _ _) ≫
    (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) q).map
      (Limits.Pi.π _ S) = _
  rw [inv_piComparison_comp_map_π]
  exact Limits.Pi.lift_comp_π _ S

set_option backward.isDefEq.respectTransparency false in
private theorem row_hom_ext (p q : ℤ) {M : ModuleCat.{u} A}
    {a b : M ⟶ ((principalCechColumnFunctor r f p).obj F).X q}
    (h : ∀ S : principalCechRowIndex r p,
      a ≫ (Limits.Pi.π (fun S : principalCechRowIndex r p ↦
        (principalCechSectionFunctor r f S.val.val).obj F) S).f q =
      b ≫ (Limits.Pi.π (fun S : principalCechRowIndex r p ↦
        (principalCechSectionFunctor r f S.val.val).obj F) S).f q) : a = b := by
  apply (cancel_mono (piComparison
    (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) q)
    (fun S : principalCechRowIndex r p ↦
      (principalCechSectionFunctor r f S.val.val).obj F))).mp
  apply Limits.Pi.hom_ext
  intro S
  simpa only [Category.assoc, piComparison_comp_π, HomologicalComplex.eval] using h S

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rowToTerms_retract (p q n : ℤ) (h : p + q = n) :
    principalCechRowToTerms r f F p q n h ≫ rowRetract r f F p q n h = 𝟙 _ := by
  classical
  apply row_hom_ext r f F p q
  intro S
  rw [Category.assoc, rowRetract_π]
  ext x
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply]
  change (affineOpenSections A (principalCechIntersection r f S.val.val)).map
    (eqToHom _) (principalCechRowToTerms r f F p q n h x S.val) = _
  rw [principalCechRowToTerms_apply, dite_eq_left S.property]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rowToTerms_retract_ne (p q p' q' n : ℤ)
    (h : p + q = n) (h' : p' + q' = n) (hne : p ≠ p') :
    principalCechRowToTerms r f F p q n h ≫ rowRetract r f F p' q' n h' = 0 := by
  classical
  apply row_hom_ext r f F p' q'
  intro S
  rw [Category.assoc, rowRetract_π, zero_comp]
  ext x
  simp only [ModuleCat.comp_apply]
  change (affineOpenSections A (principalCechIntersection r f S.val.val)).map
    (eqToHom _) (principalCechRowToTerms r f F p q n h x S.val) = 0
  rw [principalCechRowToTerms_apply, dite_eq_right (by have hc := S.property; omega)]
  exact map_zero _

set_option backward.isDefEq.respectTransparency false in
private theorem retract_row_apply (p q n : ℤ) (h : p + q = n)
    (x : principalCechTerms r f F n) (J : {J : Finset (Fin r) // J.Nonempty}) :
    (rowRetract r f F p q n h ≫ principalCechRowToTerms r f F p q n h) x J =
      if (J.val.card : ℤ) = p + 1 then x J else 0 := by
  classical
  simp only [ModuleCat.comp_apply, principalCechRowToTerms_apply]
  split_ifs with hc
  · have he := congrArg (fun g ↦ g x) (rowRetract_π r f F p q n h ⟨J, hc⟩)
    simp only [ModuleCat.comp_apply] at he
    dsimp only [principalCechRowIndex] at he ⊢
    erw [he, ← ModuleCat.comp_apply, ← Functor.map_comp]
    simp
    rfl
  · rfl

/-- Regrouping is an isomorphism of modules in each total degree.
Source: Stacks, Tag 08D1, the finite alternating total
(blueprint: lem-sc-principal-cech-total-regrouping).

Proof: evaluate each categorical product of section complexes in degree q. Its
projections exhibit a product of the section modules in that degree, since evaluation
preserves products. Nonempty subsets have cardinalities between 1 and r, so only
rows 0 through r-1 are nonzero. The diagonal coproduct therefore has finite support.
For each subset J, put its coordinate in the unique summand p=card(J)-1,
q=n+1-card(J), using the inverse of e p and the degreewise product identification.
Sum these finitely many coordinate insertions. This is an inverse of the displayed
map: after a subset projection only its own row survives, and on each coproduct
summand all its product projections are recovered. Empty rows are zero objects;
for r=0 both families are empty and the same argument identifies zero modules.
The proof uses no differential or boundedness of F. -/
theorem principalCechTotalRegroup_isIso
    (B : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (e : ∀ p, B.X p ≅ (principalCechColumnFunctor r f p).obj F) (n : ℤ) :
    IsIso (principalCechTotalRegroup r f F B e n) := by
  classical
  let rows : Finset ℤ := Finset.univ.image
    (fun J : {J : Finset (Fin r) // J.Nonempty} ↦ (J.val.card : ℤ) - 1)
  let g (p : ℤ) : principalCechTerms r f F n ⟶ (B.total (ComplexShape.up ℤ)).X n :=
    rowRetract r f F p (n - p) n (by omega) ≫ (e p).inv.f (n - p) ≫
      B.ιTotal (ComplexShape.up ℤ) p (n - p) n (by change p + (n - p) = n; omega)
  refine ⟨⟨∑ p ∈ rows, g p, ?_, ?_⟩⟩
  · apply HomologicalComplex₂.total.hom_ext
    intro p q h
    have hpq : p + q = n := h
    have hq : q = n - p := by omega
    subst q
    rw [← Category.assoc, principalCechTotalRegroup,
      HomologicalComplex₂.ι_totalDesc, Preadditive.comp_sum, Category.comp_id]
    by_cases hp : p ∈ rows
    · rw [Finset.sum_eq_single p]
      · dsimp only [g]
        simp only [Category.assoc]
        rw [rowToTerms_retract_assoc]
        simp only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
          HomologicalComplex.id_f, Category.id_comp]
      · intro p' hp' hne
        dsimp only [g]
        simp only [Category.assoc]
        rw [rowToTerms_retract_ne_assoc r f F
          p (n - p) p' (n - p') n (by omega) (by omega) (Ne.symm hne)]
        simp
      · exact fun hn ↦ (hn hp).elim
    · have hz : IsZero (((principalCechColumnFunctor r f p).obj F).X (n - p)) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply row_hom_ext r f F p (n - p)
        intro S
        have hmem : p ∈ rows := by
          apply Finset.mem_image.mpr
          exact ⟨S.val, Finset.mem_univ _, by have hc := S.property; omega⟩
        exact (hp hmem).elim
      have hzB : IsZero ((B.X p).X (n - p)) :=
        hz.of_iso ((HomologicalComplex.eval _ _ (n - p)).mapIso (e p))
      exact hzB.eq_of_src _ _
  · rw [Preadditive.sum_comp]
    have hg (p : ℤ) : g p ≫ principalCechTotalRegroup r f F B e n =
        rowRetract r f F p (n - p) n (by omega) ≫
          principalCechRowToTerms r f F p (n - p) n (by omega) := by
      dsimp only [g, principalCechTotalRegroup]
      rw [Category.assoc, Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
        HomologicalComplex.id_f, Category.comp_id]
    simp only [hg]
    ext x
    funext J
    simp only [ModuleCat.hom_sum, ModuleCat.hom_id, LinearMap.id_apply,
      LinearMap.sum_apply]
    dsimp only [principalCechTerms] at x ⊢
    rw [Finset.sum_apply]
    change (∑ p ∈ rows, (rowRetract r f F p (n - p) n (by omega) ≫
      principalCechRowToTerms r f F p (n - p) n (by omega)) x J) = x J
    simp only [retract_row_apply]
    rw [Finset.sum_eq_single ((J.val.card : ℤ) - 1)]
    · simp
    · intro p hp hne
      rw [ite_eq_right (by omega)]
    · intro hnot
      exact (hnot (Finset.mem_image.mpr ⟨J, Finset.mem_univ _, rfl⟩)).elim

end
end AlgebraicGeometry
