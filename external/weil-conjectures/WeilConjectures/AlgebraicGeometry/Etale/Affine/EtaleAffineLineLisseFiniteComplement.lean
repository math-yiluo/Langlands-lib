/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.AlgebraicGeometry.AffineSpace.AffineLineDenseOpenFiniteComplement
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.GenericConstancy

/-! A lisse open with finite complement after shrinking an affine-line base. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A constructible sheaf on a relative affine line is lisse with finite complement after
restricting the base to a dense affine open.
Source: Stacks Project, Tag 0GKZ, the generic-constancy and generic-finiteness paragraph.
(blueprint: lem-weil-pbc-affine-line-lisse-finite-complement)

Proof: The base and relative line are Noetherian. Apply generic constancy to obtain a dense
lisse open in the line. Its reduced closed complement has finite fibres over each component
generic point of the base: each such fibre is a proper closed subset of an affine line over
a field, so its points correspond to factors of a nonzero polynomial. The generic-finiteness
neighborhood theorem makes this complement finite after shrinking the base to a dense open.
Choose a principal open contained in this open and containing all the finitely many minimal
primes, using finite prime avoidance. This principal open is dense, affine, and finite type
over the integers. Identify it with its affine spectrum, pull back the original lisse open,
and use base-change stability of finiteness and finite local constancy. For an empty base,
take the zero ring and the empty opens; all conclusions hold. -/
theorem exists_dense_affine_open_lisse_finite_complement
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    [Algebra.FiniteType ℤ Γ(Y, ⊤)]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R)
      (g : Spec (.of R) ⟶ Y) (_ : IsOpenImmersion g),
      Dense (Set.range g.base) ∧
      ∃ U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens,
        Scheme.IsFiniteLocallyConstantSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ)
              (AffineSpace.map (ULift.{u} (Fin 1)) g)).obj F)) ∧
        ∃ (Z : Scheme.{u}) (i : Z ⟶ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)))
          (_ : IsClosedImmersion i), Set.range i.base = (U : Set _)ᶜ ∧
          IsFinite (i ≫
            (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))) := by
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hF
  obtain ⟨U, hUd, hU⟩ := Scheme.IsConstructibleSheaf.exists_dense_open F
  obtain ⟨R, hR, hft, g, hg, hgd, hZ⟩ :=
    AffineSpace.exists_dense_affine_open_isFinite_closedComplement Y U hUd
  let a := AffineSpace.map (ULift.{u} (Fin 1)) g
  let U' := a ⁻¹ᵁ U
  refine ⟨R, hR, hft, g, hg, hgd, U', ?_, hZ⟩
  have hl : Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U'.ι ≫ a)).obj F) := by
    refine Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
      (U'.ι ≫ a) U.ι ?_ F
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.2
  exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) U'.ι a).app F)

end AlgebraicGeometry
