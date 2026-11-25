/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex

/-! # The first page of the column spectral sequence

Source: Stacks Project, Homology, Tags 0130 and 0132, column filtration of a
first-quadrant double complex.
(blueprint: new-finite-cover-double-complex-page-one)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]
  (X : ExactCouple C ((-1, 0) : ℤ × ℤ) ((1, 1) : ℤ × ℤ) 0)

/-- Include the initial exact couple as page one. The page homology is the next
derived couple, including the transition from page one to page two.
Source: Stacks Project, Tag 0132.
(blueprint: new-finite-cover-double-complex-page-one) -/
def firstQuadrantSpectralSequenceFromOne (hX : X.IsFirstQuadrant) :
    CohomologicalSpectralSequenceNat C 1 where
  page r hr := X.firstQuadrantPage r hr
  iso r r' pq hrr' hr := X.firstQuadrantPageHomologyIso hX r hr pq ≪≫
    eqToIso (X.homology_dComplex_derivedIter _ _ (by omega) _)

end CategoryTheory.ExactCouple

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The column spectral sequence, starting on its actual first page.
Source: Stacks Project, Tags 0130 and 0132.
(blueprint: new-finite-cover-double-complex-page-one) -/
def firstSpectralSequenceFromOne : CohomologicalSpectralSequenceNat C 1 :=
  K.extendNat.columnFiltration.exactCouple.firstQuadrantSpectralSequenceFromOne
    K.extendNat_columnFiltration_isFirstQuadrant

/-- Its initial page is the vertical cohomology of the given columns.
Source: Stacks Project, Tag 0132. The associated graded of the column filtration
is one column with its signed differential. The canonical signed-column comparison,
followed by restriction from integers to naturals, gives the stated isomorphism.
(blueprint: new-finite-cover-double-complex-page-one) -/
def firstSpectralSequenceFromOnePageOneIso (p q : ℕ) :
    (K.firstSpectralSequenceFromOne.page 1).X (p, q) ≅ (K.X p).homology q :=
  K.extendNat.columnFiltrationE₁Iso (p : ℤ) q _ rfl ≪≫ K.extendNatXHomologyIso p q

/-- The first differential is induced by the horizontal column map, with no extra sign.
Source: Stacks Project, Tag 0132. Apply the canonical differential formula for the
column filtration and transport across extension by zero.
(blueprint: new-finite-cover-double-complex-page-one) -/
@[reassoc]
theorem firstSpectralSequenceFromOnePageOneIso_d (p q : ℕ) :
    (K.firstSpectralSequenceFromOnePageOneIso p q).inv ≫
        (K.firstSpectralSequenceFromOne.page 1).d (p, q) (p + 1, q) ≫
        (K.firstSpectralSequenceFromOnePageOneIso (p + 1) q).hom =
      HomologicalComplex.homologyMap (K.d p (p + 1)) q := by
  rw [← cancel_mono (K.firstSpectralSequenceFromOnePageOneIso (p + 1) q).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (K.homologyMap_d_comp_E₁Iso_inv p q).symm

end HomologicalComplex₂
