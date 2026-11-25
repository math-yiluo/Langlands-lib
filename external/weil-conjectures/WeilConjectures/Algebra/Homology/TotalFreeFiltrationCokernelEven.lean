/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Splittings and free quotients of the alternating column filtration

Source: Stacks Project, Tag 09KP, filtration construction.
(blueprint: lem-pc-derived-total-filtration-cokernel-even)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- The even successive quotient has the prescribed endpoint basis in shifted degrees.
Source: Stacks Project, Tag 09KP, successive quotients of the column filtration.
(blueprint: lem-pc-derived-total-filtration-cokernel-even)

Proof. In total degree k, remove the full columns with index less than j.
The remaining inclusion is zero into the image of the first arrow of S j.
Short exactness identifies its cokernel with (S j).X₁ in vertical degree k+j.
The horizontal differential goes to a preceding full column, so vanishes in
the quotient. The vertical differential vanishes on the endpoint, since its
given coproduct decomposition has zero differential. Thus the degreewise
identifications commute with differentials and define a complex isomorphism.
Compose the endpoint decomposition with reindexing: a summand supported in
vertical degree d is supported in total degree d-j. The induced quotient map
has the cokernel universal property degreewise, hence in cochain complexes.
The argument also covers j=0, empty bases, and the zero ring. -/
theorem cokernel_even
    (h_exact : ∀ j, (S j).ShortExact)
    (j : ℕ) (I : Type u) (degree : I → ℤ)
    (h_endpoint : Nonempty ((S j).X₁ ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i)).obj (ModuleCat.of A A)))) :
    Nonempty (cokernel (step K S e h_positive (2 * j)) ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i - (j : ℤ))).obj (ModuleCat.of A A))) := by
  classical
  let q : (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).obj
      (S j).X₁ ⟶ cokernel (step K S e h_positive (2 * j)) :=
    { f := evenQuotientComponent K S e h_positive j
      comm' := evenQuotientComponent_comm K S e h_positive j }
  have (k : ℤ) : IsIso (q.f k) :=
    (ConcreteCategory.isIso_iff_bijective (q.f k)).mpr
      (evenQuotientComponent_bijective K S e h_positive h_exact j k)
  have : IsIso q := HomologicalComplex.Hom.isIso_of_components q
  obtain ⟨b⟩ := h_endpoint
  let F := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)
  exact ⟨(asIso q).symm ≪≫ F.mapIso b ≪≫
    PreservesCoproduct.iso F _ ≪≫ Sigma.mapIso (fun i ↦
      ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso
        (j : ℤ) (degree i - (j : ℤ)) (degree i) (by omega)).app (ModuleCat.of A A))⟩

end CochainComplex.TotalFreeFiltration
