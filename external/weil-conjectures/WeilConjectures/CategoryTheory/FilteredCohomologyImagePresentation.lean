/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex


public import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation
import WeilConjectures.CategoryTheory.FilteredCohomologyImageNormalized

/-! # A cycle presentation of the graded cohomology image

Source: Stacks Project, Tag 012Q, Equation 12.24.5.2.
(blueprint: lem-sp-filtered-cohomology-image-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- The graded cohomology image is a quotient of the ambient cycles in a filtration step.
Source: Stacks Project, Tag 012Q, final quotient calculation, Equation 12.24.5.2.
(blueprint: lem-sp-filtered-cohomology-image-presentation).

Proof. Set A=L^pK^n, A'=L^(p+1)K^n, Z=ker(d^n), B=im(d^(n-1)).
The inclusion of L^pK identifies its cycles with A intersection Z. Its
cohomology surjects onto the image I^p of H^n(L^pK) in H^n(K), and the
cycle projection also surjects onto I^p. The kernel of this last projection
is A intersection B: these are exactly ambient boundaries lying in A.
Likewise the image I^(p+1) is the image of A' intersection Z in H^n(K).
The composite A intersection Z onto I^p onto I^p/I^(p+1) is epic, with
kernel (A intersection B)+(A' intersection Z). Viewing this sum as a
subobject of A intersection Z by pullback, its cokernel is isomorphic to
the cokernel of I^(p+1) into I^p, which defines the graded image filtration.
The assertion needs no finiteness or bounds, and all objects are existing
cycle, image, and cokernel constructions.
-/
theorem cohomologyImage_graded_presentation
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  Nonempty ((L.homologyFiltration n).gradedPiece p ≅
    cokernel ((Subobject.pullback (A ⊓ Z).arrow).obj
      ((A ⊓ B) ⊔ (A' ⊓ Z))).arrow) := by
  dsimp only
  obtain ⟨hBZ, ⟨e₀⟩⟩ := cohomologyImage_graded_normalized L p n
  obtain ⟨e₁⟩ := L.normalizedStationaryQuotient_presentation p n hBZ
  exact ⟨e₀ ≪≫ e₁⟩

end CategoryTheory.DecreasingFiltration
