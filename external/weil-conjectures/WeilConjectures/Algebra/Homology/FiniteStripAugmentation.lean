/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Algebra.Homology.FiniteStripConeFiltration
import WeilConjectures.CategoryTheory.DegreewiseFilteredAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Augmentation of a double complex supported in a finite horizontal strip

Source: Stacks Project, Homology, Lemma 12.25.4, as used in Tag 08C1.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

/-- Exact augmented horizontal rows imply that the total augmentation is a
quasi-isomorphism, without a bound in the vertical direction.

Source: Stacks Project, Homology, Lemma 12.25.4, and Tag 08C1, first paragraph.
(blueprint: lem-sc-finite-strip-row-augmentation)

Proof: The degree-zero equalities specify the maps from the single complexes
uniquely. Their commutation with the horizontal differential, and the commutation
of b with the total differential, identify the cone of b with the total of the
augmented rows, with the cone shift and signs. The quasi-isomorphism of each
single-row augmentation makes every augmented row exact, including injectivity
at the initial term. The augmented horizontal degrees range from -1 to r-1.
In each total degree the sum is therefore finite. For a cone cocycle, use row
exactness to lift its largest horizontal component, then subtract the total
boundary of that lift. The horizontal component disappears; the vertical
contribution lies one column earlier. Repeat finitely often. At column -1,
injectivity of the augmentation forces the remainder to vanish. Hence the cone
is acyclic and b is a quasi-isomorphism. When r=0, K is zero and the row condition
forces each term of A to be zero, so the same conclusion holds. -/
theorem quasiIso_of_finite_strip_row_augmentation
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ p : ℤ, p < 0 ∨ (r : ℤ) ≤ p → IsZero (K.X p))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (hrows : ∀ n : ℤ, ∃ f :
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X n) ⟶ K.flip.X n,
      f.f 0 = (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 (A.X n)).hom ≫ a n ∧ QuasiIso f) :
    QuasiIso b := by
  classical
  choose f hf hq using hrows
  obtain ⟨F, _, hfinite, hgraded⟩ := finite_strip_cone_filtration K r hsupport A a b hb f hf
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic b).mpr
  apply degreewiseFiltered_acyclic _ F
  · intro n
    exact ⟨n - (r : ℤ), n + 2, hfinite n⟩
  · intro p n
    obtain ⟨e⟩ := hgraded p n
    have hcone := (CochainComplex.mappingCone.quasiIso_iff_acyclic (f p)).mp (hq p)
    apply ((F.gradedPiece p).exactAt_iff_isZero_homology n).mpr
    exact e.isZero_iff.mpr (((CochainComplex.mappingCone (f p)).exactAt_iff_isZero_homology
      (n - p)).mp (hcone (n - p)))

end HomologicalComplex₂
