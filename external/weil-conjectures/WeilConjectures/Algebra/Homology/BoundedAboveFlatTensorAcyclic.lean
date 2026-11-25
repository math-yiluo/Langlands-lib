/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree

/-!
# Tensoring bounded-above acyclic complexes with bounded-above flat complexes

Source: Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ) (bounded-above case)
(blueprint: lem-pc-bounded-above-flat-tensor-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- If `A` is bounded above and acyclic, and `P` is bounded above with flat terms,
then their total tensor complex is acyclic. The tensor is the sheaf tensor product
in `SheafOfModules.monoidalCategory R`.
Source: Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ)
(blueprint: lem-pc-bounded-above-flat-tensor-acyclic).

Proof:
1. Choose upper bounds `a` and `b`. For a fixed total degree `n`, put `j = n - 2 - b`
   and `k = n - 1 - a`. Replace `P` below `k` by zero (stupid truncation), and replace
   `A` below `j` by zero and in degree `j` by the image of its degree-`j` differential,
   with the inclusion into `A` in degree `j + 1` as differential. Acyclicity of `A`
   makes this latter truncated complex `B` acyclic. The tensor double complexes agree
   in total degrees `n - 1`, `n`, `n + 1`, so their degree-`n` cohomology agrees
   (`def-pc-tensor-complex-sheaves`, `def-pc-acyclic-complex-modules`). The truncated
   double complex is bounded in both directions. Translate it into the first quadrant,
   adjusting the sign of the second differential, and apply
   `thm-sp-double-complex-spectral-sequences`.
2. Filter by the degree of the truncated `P`. Each first-page term is cohomology of
   `B` tensored with a term of that truncation. These terms are zero or flat, so their
   tensor functors are exact (`def-pc-flat-sheaf-modules`). Each column is therefore
   acyclic (`def-pc-acyclic-complex-modules`) and the first page vanishes.
3. Every later page vanishes. The convergence theorem
   `thm-sp-double-complex-spectral-sequences` gives a finite filtration of degree-`n`
   cohomology with zero graded pieces. Thus that cohomology vanishes. Since `n` was
   arbitrary, the original total complex is acyclic. -/
theorem acyclic_mapBifunctor_of_boundedAbove_flat_sheaf
    (A P : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hAbounded : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (A.X i))
    (hPbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hPflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) :
    A.Acyclic →
      (letI := SheafOfModules.monoidalCategory R
       mapBifunctor A P (curriedTensor _)).Acyclic := by
  intro hA n
  exact isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf A P hAbounded hPbounded
    hPflat hA n

end CochainComplex
