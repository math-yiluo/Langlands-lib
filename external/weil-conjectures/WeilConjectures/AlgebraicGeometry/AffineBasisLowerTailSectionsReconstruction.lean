/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.AlgebraicGeometry.AffineScheme

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

import WeilConjectures.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit
import WeilConjectures.AlgebraicGeometry.TruncationDerivedLimit
import WeilConjectures.AlgebraicGeometry.AffineBasisRestrictedLowerTailLocalBound
import WeilConjectures.AlgebraicGeometry.OpenDerivedSectionsTruncationTowerComparison
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine-basis lower truncation tower inputs
Source: Stacks Project, Tags 0BKT, 0D64, 071B and 08D4. -/

@[expose] public section
universe u wC wA
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

private theorem map_product_lift
    {C : Type wC} {D : Type wA} [Category C] [Category D]
    (G : C ⥤ D) {K : ℕ → C} [HasProduct K] [HasProduct (fun n => G.obj (K n))]
    {A : C} (p : ∀ n, A ⟶ K n)
    (e : G.obj (∏ᶜ K) ≅ ∏ᶜ (fun n => G.obj (K n)))
    (he : ∀ n, e.hom ≫ Pi.π _ n = G.map (Pi.π K n)) :
    G.map (Pi.lift p) ≫ e.hom = Pi.lift (fun n => G.map (p n)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, he, ← Functor.map_comp, Pi.lift_comp_π, Pi.lift_comp_π]

private theorem derivedLimitTriangle_map_product_lift
    {C D : Type*} [Category C] [Category D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (G : C ⥤ D) {K : ℕ → C} [HasProduct K] [HasProduct (fun n => G.obj (K n))]
    {A : C} (p : ∀ n, A ⟶ K n)
    (e : G.obj (∏ᶜ K) ≅ ∏ᶜ (fun n => G.obj (K n)))
    (he : ∀ n, e.hom ≫ Pi.π _ n = G.map (Pi.π K n))
    (f : ∀ n, G.obj (K (n + 1)) ⟶ G.obj (K n))
    (δ : (∏ᶜ (fun n => G.obj (K n))) ⟶ (G.obj A)⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f (G.obj A) (G.map (Pi.lift p) ≫ e.hom) δ) :
    IsDerivedLimitTriangle f (G.obj A) (Pi.lift (fun n => G.map (p n))) δ := by
  rw [← map_product_lift G p e he]
  exact h

private theorem transport_roos_triangle
    {C : Type wC} [Category.{wA} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasProductsOfShape ℕ C]
    {K L : ℕ → C} (f : ∀ n, K (n + 1) ⟶ K n) (g : ∀ n, L (n + 1) ⟶ L n)
    {A B : C} (p : ∀ n, A ⟶ K n) (q : ∀ n, B ⟶ L n)
    (e : A ≅ B) (en : ∀ n, K n ≅ L n)
    (hp : ∀ n, p n ≫ (en n).hom = e.hom ≫ q n)
    (hf : ∀ n, f n ≫ (en n).hom = (en (n + 1)).hom ≫ g n)
    (δ : (∏ᶜ K) ⟶ A⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f A (Pi.lift p) δ) :
    ∃ δ' : (∏ᶜ L) ⟶ B⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle g B (Pi.lift q) δ' := by
  let b := Pi.mapIso en
  have hb : towerTransitionEndomorphism f ≫ b.hom =
      b.hom ≫ towerTransitionEndomorphism g := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, b, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
      Pi.lift_comp_π, Pi.mapIso_hom_π, Pi.mapIso_hom_π_assoc, Pi.lift_comp_π_assoc]
    simp only [← Category.assoc]
    rw [Category.assoc (Pi.π _ (n + 1)), hf]
    simp only [Category.assoc]
  let δ' := b.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom
  refine ⟨δ', Pretriangulated.isomorphic_distinguished _ h _ ?_⟩
  refine Pretriangulated.Triangle.isoMk _ _ e.symm b.symm b.symm ?_ ?_ ?_
  · change Pi.lift q ≫ b.inv = e.inv ≫ Pi.lift p
    apply (cancel_mono b.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, b, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    rw [hp, Iso.inv_hom_id_assoc]
  · change towerTransitionEndomorphism g ≫ b.inv = b.inv ≫ towerTransitionEndomorphism f
    apply (cancel_mono b.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun z => b.inv ≫ z) hb.symm
  · change δ' ≫ (shiftFunctor C (1 : ℤ)).map e.inv = b.inv ≫ δ
    simp [δ', ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived abelian sections reconstruct the lower tail from its canonical lower
truncations. This is only the reconstruction step, with no homology conclusion.
Source: Stacks Project, Tag 0D64 (lemma-is-limit-dimension), Tag 071B
(lemma-K-injective) and Tag 0BKT (lemma-cohomology-over-U-trivial).
(blueprint: lem-sc-affine-basis-lower-tail-sections-reconstruction).

Proof: Restrict to V. Exact restriction identifies the homology of E with the
restriction of H^r(F) for r < a and with zero for r >= a. Affine opens inside V
form a basis of V. On each such open, the module-to-abelian cohomology comparison
transfers hhomology to zero positive derived module sections. Thus Tag 0D64 applies
on V with local bound zero and reconstructs E from its lower truncations. Restriction
preserves K-injectives by the exact extension-by-zero adjoint, so derived sections
of this restriction are the given derived evaluation, followed by exact forgetting.
Sections and forgetting preserve products. Apply the derived-functor product
comparison to the Roos triangle, identifying its first map by its product
projections. This gives precisely the displayed triangle. The argument works for
empty V, all integer a, arbitrary unbounded F and arbitrary derived universes. -/
theorem affineBasisLowerTail_sections_reconstruction
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    let G := S ⋙ forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
    let t := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let E := (t.truncLT a).obj (DerivedCategory.Q.obj F)
    ∃ δ : (∏ᶜ (fun n : ℕ => G.rightDerivedFunctor.obj
        ((t.truncGE (-(n : ℤ))).obj E))) ⟶ (G.rightDerivedFunctor.obj E)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (fun n : ℕ => G.rightDerivedFunctor.map
        ((t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))
        (G.rightDerivedFunctor.obj E)
        (Pi.lift (fun n : ℕ => G.rightDerivedFunctor.map
          ((t.truncGEπ (-(n : ℤ))).app E))) δ := by
  classical
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let G := S ⋙ forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let E := (t.truncLT a).obj (DerivedCategory.Q.obj F)
  let dc := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) := dc
  let : HasDerivedCategory.{u + 1} V.toScheme.Modules := dc
  have : IsGrothendieckAbelian.{u} V.toScheme.Modules :=
    RingedSpace.moduleGrothendieckAbelian V.toScheme.toRingedSpace
  have : Abelian.HasKInjectiveResolutions V.toScheme.Modules :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  let R := (schemeOpenRestriction X V).mapDerivedCategory
  let H := RingedSpace.openModuleSections.{u} V.toScheme.toRingedSpace ⊤
  have : H.Additive := RingedSpace.openModuleSections_additive _ _
  have : PreservesLimitsOfShape (Discrete ℕ) H := by
    dsimp [H, RingedSpace.openModuleSections]
    infer_instance
  let s := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let T : ℕ → DerivedCategory
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) :=
    fun n => (s.truncGE (-(n : ℤ))).obj (R.obj E)
  let f : ∀ n : ℕ, T (n + 1) ⟶ T n := fun n =>
    (s.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app (R.obj E)
  let p : R.obj E ⟶ ∏ᶜ T :=
    Pi.lift (fun n : ℕ => (s.truncGEπ (-(n : ℤ))).app (R.obj E))
  obtain ⟨B, hB, hvan⟩ := affineBasisRestrictedLowerTail_local_bound X V hV F hhomology a
  obtain ⟨_, δ, hδ⟩ := truncation_isDerivedLimitTriangle_of_local_bound V.toScheme
    (R.obj E) ⟨0, B, hB, hvan⟩
  obtain ⟨c, hc, h⟩ := Scheme.rightDerivedFunctor_isDerivedLimitTriangle V.toScheme H
    f (R.obj E) p δ hδ
  have h' := derivedLimitTriangle_map_product_lift H.rightDerivedFunctor
    (fun n : ℕ => (s.truncGEπ (-(n : ℤ))).app (R.obj E)) c hc _ _ h
  obtain ⟨e, en, hπ, hf⟩ := openDerivedSections_truncationTower_comparison X V E
  exact transport_roos_triangle
    (fun n => H.rightDerivedFunctor.map (f n))
    (fun n => G.rightDerivedFunctor.map
      ((t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))
    (fun n => H.rightDerivedFunctor.map ((s.truncGEπ (-(n : ℤ))).app (R.obj E)))
    (fun n => G.rightDerivedFunctor.map ((t.truncGEπ (-(n : ℤ))).app E))
    e en hπ hf _ h'

end AlgebraicGeometry
