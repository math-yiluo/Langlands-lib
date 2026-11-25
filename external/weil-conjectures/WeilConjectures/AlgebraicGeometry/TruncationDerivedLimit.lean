/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.RingedSpaceDerivedProducts
import WeilConjectures.Topology.PointwiseTruncationLimit

/-! # Reconstruction from lower truncations under a local cohomological bound

Source: Stacks Project, Cohomology of Sheaves, Tag 0D64, specialized to a scheme
(blueprint: lem-pc-ringed-space-truncation-derived-limit).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A uniform cohomological bound on a basis for the negative cohomology sheaves
exhibits a complex as the derived limit of its standard lower truncations.
Source: Stacks Project, Tag 0D64
(blueprint: lem-pc-ringed-space-truncation-derived-limit).

Proof:
1. For each point x use the basis opens containing x as a fundamental system of
neighborhoods. Put p_x(m) = d + max(0,m). If p > p_x(m) and m-p < 0, the assumed
vanishing applies since p > d. If m-p >= 0, then p <= m <= max(0,m)+d, a contradiction.
Thus lem-pc-ringed-space-pointwise-truncation-limit applies.
2. By lem-pc-ringed-space-derived-products the product of the truncations exists.
By lemma-reduction-derived-nakayama (1), choose a derived limit (K,p_K,delta_K).
The pointwise criterion supplies an isomorphism c : E -> K whose composite with each
product projection is the canonical truncation map.
3. Transport the distinguished Roos triangle along c (def-weil-triangulated-category).
Its first map p_K composed with c is the product lift of the canonical truncation maps,
and its last map is delta_K followed by the shifted inverse of c. This gives precisely
the specified IsDerivedLimitTriangle (def-weil-derived-limit), hence the canonical
comparison with the chosen derived limit is an isomorphism. -/
theorem truncation_isDerivedLimitTriangle_of_local_bound (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hE : ∃ (d : ℕ) (B : Set (Opens X)),
      IsTopologicalBasis ((fun U : Opens X => (U : Set X)) '' B) ∧
      ∀ (U : Opens X), U ∈ B → ∀ (p : ℕ), d < p → ∀ (q : ℤ), q < 0 →
        IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).obj E))) :
    ∃ (_ : HasProduct (fun n : ℕ => ((DerivedCategory.TStructure.t
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGE (-(n : ℤ))).obj E)),
      ∃ δ : (∏ᶜ (fun n : ℕ => ((DerivedCategory.TStructure.t
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGE
            (-(n : ℤ))).obj E)) ⟶ E⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n : ℕ => ((DerivedCategory.TStructure.t
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E) E
          (Pi.lift (fun n : ℕ => ((DerivedCategory.TStructure.t
            (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGEπ
              (-(n : ℤ))).app E)) δ := by
  obtain ⟨d, B, hB, hvan⟩ := hE
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let t := DerivedCategory.TStructure.t (C := C)
  let T : ℕ → schemeDerivedCategory X := fun n => (t.truncGE (-(n : ℤ))).obj E
  let f : ∀ n : ℕ, T (n + 1) ⟶ T n := fun n =>
    (t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E
  have := RingedSpace.derivedProducts X.toRingedSpace
  have hP : HasProduct T := inferInstance
  refine ⟨hP, ?_⟩
  obtain ⟨K, π, δ, hK⟩ := (exists_isDerivedLimit_and_iso T f).1
  have hlocal : ∀ x : X.toRingedSpace, ∃ (b : ℤ → ℤ)
      (Bx : Set (Opens X.toRingedSpace)),
      (∀ U ∈ Bx, x ∈ U) ∧
      (∀ V : Opens X.toRingedSpace, x ∈ V → ∃ U ∈ Bx, U ≤ V) ∧
      (∀ (m : ℤ) (p : ℕ) (U : Opens X.toRingedSpace), U ∈ Bx → b m < (p : ℤ) →
        IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          ((DerivedCategory.homologyFunctor C (m - (p : ℤ))).obj E))) := by
    intro x
    refine ⟨fun m => (d : ℤ) + max 0 m, {U | U ∈ B ∧ x ∈ U}, ?_, ?_, ?_⟩
    · exact fun U hU => hU.2
    · intro V hxV
      obtain ⟨W, hW, hxW, hWV⟩ := hB.exists_subset_of_mem_open hxV V.isOpen
      obtain ⟨U, hUB, rfl⟩ := hW
      exact ⟨U, ⟨hUB, hxW⟩, hWV⟩
    · intro m p U hU hp
      change (d : ℤ) + max 0 m < (p : ℤ) at hp
      apply hvan U hU.1 p
      · omega
      · omega
  obtain ⟨⟨c, hc⟩, hiso⟩ :=
    RingedSpace.pointwise_truncation_limit X.toRingedSpace E hlocal K π δ hK
  have : IsIso c := hiso c hc
  have hπ : Pi.lift (fun n : ℕ => (t.truncGEπ (-(n : ℤ))).app E) = c ≫ π := by
    apply Pi.hom_ext
    intro n
    simpa only [Pi.lift_comp_π, Category.assoc] using (hc n).symm
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map (inv c), ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hK
  refine Pretriangulated.Triangle.isoMk _ _ (asIso c) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simpa using hπ
  · simp only [Pretriangulated.Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    rfl
  · simp

end AlgebraicGeometry
