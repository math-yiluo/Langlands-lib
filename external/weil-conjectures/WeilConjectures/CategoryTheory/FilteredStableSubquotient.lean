/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex


public import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation
import WeilConjectures.CategoryTheory.FilteredCohomologyImagePresentation
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # The stationary subquotient comparison at explicit filtration bounds

Source: Stacks Project, Tags 012Q and 0132.
(blueprint: lem-sp-filtered-stable-subquotient-at-bounds).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

private theorem quotient_iso_of_eq
    {C : Type u} [Category.{v} C] [Abelian C] {X : C}
    {B Z B' Z' : Subobject X} (h : B ≤ Z) (h' : B' ≤ Z')
    (hB : B = B') (hZ : Z = Z') :
    Nonempty (cokernel (Subobject.ofLE B Z h) ≅
      cokernel (Subobject.ofLE B' Z' h')) := by
  subst B'
  subst Z'
  exact ⟨Iso.refl _⟩

/-- At stationary outer steps the cycle/boundary quotient is the graded cohomology image.
Source: Stacks Project, Tags 012Q and 0132.
(blueprint: lem-sp-filtered-stable-subquotient-at-bounds).

Proof. Replace L^(p+r)K^(n+1) by zero in the cycle formula and replace
L^(p-r+1)K^(n-1) by the whole object in the boundary formula. Write A=L^pK^n,
A'=L^(p+1)K^n, Z=ker(d^n), and B=im(d^(n-1)). Then the cycles in A/A'
are ((A ∩ Z)+A')/A', and the boundaries are ((A ∩ B)+A')/A'. The boundary
inclusion is supplied (it follows from d²=0 and the two outer bounds).
The third isomorphism theorem identifies their quotient with
(A ∩ Z)/((A ∩ B)+(A' ∩ Z)): modularity gives
(A ∩ Z) ∩ ((A ∩ B)+A')=(A ∩ B)+(A' ∩ Z).
The image of H^n(L^pK) in H^n(K)=Z/B is the image of A ∩ Z in Z/B,
and the next image step is the image of A' ∩ Z. Their quotient has precisely
the same presentation. The abelian subquotient isomorphisms therefore identify
the stationary quotient with the cokernel defining the graded image filtration.
This uses only the two displayed outer bounds and r≥1; no uniform bound on
other degrees, chosen abutment, or spectral sequence is required. -/
theorem stableSubquotient_at_bounds
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r)
    (hupper : L.complexStep (p + r) (n + 1) = ⊥)
    (hlower : L.complexStep (p - r + 1) (n - 1) = ⊤)
    (hBZ : L.complexBoundaries p n r ≤ L.complexCycles p n r) :
    Nonempty (cokernel (Subobject.ofLE _ _ hBZ) ≅
      (L.homologyFiltration n).gradedPiece p) := by
  have _hr := hr
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
  let P := Subobject.pullback ((L.step p).arrow.f n)
  let Zbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ Z) ⊔ A'))
  let Bbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ B) ⊔ A'))
  have hZ : L.complexCycles p n r = Zbar := by
    simp only [complexCycles, hupper]
    rfl
  have hB : L.complexBoundaries p n r = Bbar := by
    simp only [complexBoundaries, hlower, Subobject.exists_obj_top]
    rfl
  have hnormalized : Bbar ≤ Zbar := by
    rw [← hB, ← hZ]
    exact hBZ
  obtain ⟨e₀⟩ := quotient_iso_of_eq hBZ hnormalized hB hZ
  obtain ⟨e₁⟩ := L.normalizedStationaryQuotient_presentation p n hnormalized
  obtain ⟨e₂⟩ := L.cohomologyImage_graded_presentation p n
  exact ⟨e₀ ≪≫ e₁ ≪≫ e₂.symm⟩

end CategoryTheory.DecreasingFiltration
