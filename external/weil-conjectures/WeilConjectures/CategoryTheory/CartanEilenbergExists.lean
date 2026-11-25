/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.CategoryTheory.CartanEilenbergRowsExists
import WeilConjectures.CategoryTheory.CartanEilenbergRowsIdentifications

/-! # Existence of Cartan--Eilenberg injective resolutions

Source: Stacks Project, derived.tex, Definition 015H and Lemma 015I
(blueprint: lem-sp-cartan-eilenberg-exists).

The resolution index is natural, equivalently extending by zero in negative degrees.
The augmentation is a morphism of bicomplexes from the complex placed in vertical
degree zero. Kernels, images and homology in the category of vertical complexes
are computed degreewise. Quasi-isomorphisms from these single-degree complexes,
together with injectivity of every target term, express injective resolutions
using exactly the data of `CategoryTheory.InjectiveResolution`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- Existence of a Cartan--Eilenberg resolution, with all induced augmentations.
Source: Stacks Project, derived.tex, Definition 015H and Lemma 015I
(blueprint: lem-sp-cartan-eilenberg-exists).

Proof:
1. With the bound n = 0, form cycles Z^p, boundaries B^p and cohomology H^p.
   In the abelian category (def-sp-abelian), decompose K into the alternating
   short exact sequences 0 → Z^p → K^p → B^(p+1) → 0 and
   0 → B^(p+1) → Z^(p+1) → H^(p+1) → 0.
2. Choose a resolution of Z^0 using
   lem-weil-pbc-left-exact-injective-resolution-degree-zero. Apply
   lem-sp-horseshoe-prescribed-resolutions to the first sequence, prescribing
   this resolution and one of B^1. Apply it to the next sequence prescribing
   that same resolution of B^1 and one of H^1, and continue inductively.
   Put the boundary resolution in degree 0 equal to zero and the cohomology
   resolution there equal to the cycle resolution. All resolutions start at 0
   (def-sp-injective-resolutions).
3. Define the horizontal differential by the composite through the quotient
   resolution of B^(p+1), the resolution of Z^(p+1), and the next column.
   The horseshoe diagrams make it commute with vertical differentials and
   the augmentations; exactness gives its square zero
   (def-sp-double-complex-total, lem-sp-horseshoe-prescribed-resolutions).
4. Extend by zero for p < 0. The adjacent degreewise short exact sequences
   identify horizontal cycles, boundaries and homology with the chosen
   resolutions of Z^p, B^p and H^p, including their induced augmentations.
   Their terms are injective and their augmentations are quasi-isomorphisms
   (lem-sp-horseshoe-prescribed-resolutions, def-sp-injective-resolutions).
-/
theorem exists_cartanEilenberg_resolution
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex B ℤ)
    (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) :
    ∃ (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
      (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
        ⟶ I),
      (∀ p : ℤ, p < 0 → IsZero (I.X p)) ∧
      (∀ p : ℤ, QuasiIso (e.f p)) ∧
      (∀ (p : ℤ) (q : ℕ), Injective ((I.X p).X q)) ∧
      (∀ (p : ℤ) (q : ℕ),
        Injective ((I.cycles p).X q) ∧
        Injective ((image (I.d (p - 1) p)).X q) ∧
        Injective ((I.homology p).X q)) ∧
      (∀ p : ℤ,
        QuasiIso (HomologicalComplex.cyclesMap e p) ∧
        QuasiIso
          (image.map (Arrow.homMk' (e.f (p - 1)) (e.f p) (e.comm (p - 1) p))) ∧
        QuasiIso (HomologicalComplex.homologyMap e p)) := by
  obtain ⟨R, hneg, hqi, hinj⟩ := exists_cartanEilenberg_rows B K hK
  obtain ⟨z, d, h, hz, hd, hh⟩ := cartanEilenberg_rows_identifications R
  refine ⟨R.complex, R.augmentation, hneg, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hqi p).1
  · intro p q
    exact (hinj p q).1
  · intro p q
    refine ⟨?_, ?_, ?_⟩
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (z p)).symm
        (hinj p q).2.1
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (d p)).symm
        (hinj p q).2.2.1
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (h p)).symm
        (hinj p q).2.2.2
  · intro p
    refine ⟨?_, ?_, ?_⟩
    · have : QuasiIso
          (HomologicalComplex.cyclesMap R.augmentation p ≫ (z p).hom) := by
        rw [hz p]
        exact (hqi p).2.1
      exact quasiIso_of_comp_right _ (z p).hom
    · have : QuasiIso
          (image.map (Arrow.homMk' (R.augmentation.f (p - 1))
            (R.augmentation.f p) (R.augmentation.comm (p - 1) p)) ≫ (d p).hom) := by
        rw [hd p]
        exact (hqi p).2.2.1
      exact quasiIso_of_comp_right _ (d p).hom
    · have : QuasiIso
          (HomologicalComplex.homologyMap R.augmentation p ≫ (h p).hom) := by
        rw [hh p]
        exact (hqi p).2.2.2
      exact quasiIso_of_comp_right _ (h p).hom

end CategoryTheory
