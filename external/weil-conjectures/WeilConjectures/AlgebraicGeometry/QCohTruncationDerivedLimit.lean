/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.TruncationDerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit

/-! # Reconstruction of quasi-coherent complexes by lower truncations

Source: Stacks Project, Tags 08D3, 08D4 and 08U1
(blueprint: lem-pc-qcoh-truncation-derived-limit).

Both conclusions use specified Roos triangles: the map to the product is fixed to be
induced by the canonical truncation projections. Products are in the ambient derived
categories, rather than in the full subcategory of quasi-coherent complexes.
-/

@[expose] public section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical projections exhibit a quasi-coherent complex as the derived limit
of its lower truncations. Source: Stacks Project, Tag 08D3
(blueprint: lem-pc-qcoh-truncation-derived-limit).

Proof: On the basis of affine opens, all positive cohomology of every cohomology
sheaf vanishes by pqf-lem-affine-vanishing, since schemeDerivedQCohProperty says these
sheaves are quasi-coherent (lemma-coherent-base-change-invertible-sheaves). Apply
lem-pc-ringed-space-truncation-derived-limit with bound zero. Its Roos triangle uses
exactly the standard truncation projections (def-sbc-standard-tstructure-derived-category)
and the product in D(O_X) (def-weil-derived-limit). This gives the displayed triangle,
which expresses that the canonical reconstruction map is an isomorphism. -/
theorem qcoh_truncation_isDerivedLimitTriangle (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [Abelian.HasKInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    ∃ δ : (∏ᶜ (fun n : ℕ => ((DerivedCategory.TStructure.t (C := SheafOfModules.{u} (moduleRings
        X.toRingedSpace))).truncGE (-(n : ℤ))).obj E)) ⟶ E⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (fun n : ℕ => ((DerivedCategory.TStructure.t (C := SheafOfModules.{u}
        (moduleRings X.toRingedSpace))).natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by
        omega)).app E) E
        (Pi.lift (fun n : ℕ => ((DerivedCategory.TStructure.t (C := SheafOfModules.{u}
        (moduleRings X.toRingedSpace))).truncGEπ (-(n : ℤ))).app E)) δ := by
  obtain ⟨hprod, δ, hδ⟩ := truncation_isDerivedLimitTriangle_of_local_bound X E (by
    refine ⟨0, X.affineOpens, X.isBasis_affineOpens, ?_⟩
    intro U hU p hp q _hq
    let := hE q
    let := subsingleton_openModuleCohomology_of_isAffineOpen X
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).obj E) U hU p hp
    exact AddCommGrpCat.isZero_of_subsingleton _)
  exact ⟨δ, hδ⟩

-- Identifying Scheme.Modules with the shared SheafOfModules category requires
-- unfolding their category and derived-functor instances during equality transport.
/-- Applying a countable-product-preserving additive functor's right derived functor
preserves the canonical reconstruction. Source: Stacks Project, Tag 08U1, and
Tag 08D4, proof of (2) (blueprint: lem-pc-qcoh-truncation-derived-limit).

Proof: First use qcoh_truncation_isDerivedLimitTriangle, proved by affine vanishing
and lem-pc-ringed-space-truncation-derived-limit. Apply
lem-pc-derived-functor-commutes-derived-limit to this Roos triangle: K-injective
products compute the source product, and exact countable products in Ab compute the
target product. Product preservation identifies their images, and triangulatedness
of RF carries the distinguished triangle to the target Roos triangle. The product
comparison respects projections, so its first map is precisely the product lift of
RF applied to each truncation projection. Naturality of truncation and of this
comparison identifies this triangle with the canonical reconstruction after RF. -/
theorem rightDerivedFunctor_qcoh_truncation_isDerivedLimitTriangle (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [Abelian.HasKInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
    [Abelian.HasKInjectiveResolutions AddCommGrpCat.{u}]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (F : (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    ∃ δ : (∏ᶜ (fun n : ℕ => F.rightDerivedFunctor.obj ((fun n : ℕ =>
        ((DerivedCategory.TStructure.t (C := SheafOfModules.{u} (moduleRings
        X.toRingedSpace))).truncGE (-(n : ℤ))).obj E) n))) ⟶
        (F.rightDerivedFunctor.obj E)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (fun n : ℕ => F.rightDerivedFunctor.map ((fun n : ℕ =>
        ((DerivedCategory.TStructure.t (C := SheafOfModules.{u} (moduleRings
        X.toRingedSpace))).natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)
        n))
        (F.rightDerivedFunctor.obj E)
        (Pi.lift (fun n : ℕ =>
          F.rightDerivedFunctor.map (((DerivedCategory.TStructure.t (C := SheafOfModules.{u}
        (moduleRings X.toRingedSpace))).truncGEπ (-(n : ℤ))).app E))) δ := by
  obtain ⟨δ, hδ⟩ := qcoh_truncation_isDerivedLimitTriangle X E hE
  let : Abelian.HasKInjectiveResolutions X.Modules := inferInstanceAs
    (Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  obtain ⟨e, he, h⟩ := Scheme.rightDerivedFunctor_isDerivedLimitTriangle X F
    _ E _ δ hδ
  have hp : F.rightDerivedFunctor.map
      (Pi.lift (fun n : ℕ => ((DerivedCategory.TStructure.t
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGEπ
          (-(n : ℤ))).app E)) ≫ e.hom =
      Pi.lift (fun n : ℕ => F.rightDerivedFunctor.map
        (((DerivedCategory.TStructure.t
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGEπ
            (-(n : ℤ))).app E)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← Functor.map_comp, Pi.lift_comp_π, Pi.lift_comp_π]
  exact ⟨_, hp ▸ h⟩

end AlgebraicGeometry
