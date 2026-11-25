/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # Isolating an irreducible neighbourhood above a component generic point

## References

* Stacks Project, Tag 09BH, Proposition 59.74.1, reduction to an irreducible étale neighbourhood
* Stacks Project, Tag 0BA8
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An étale point above a component generic point has an irreducible open neighbourhood. -/
theorem Etale.exists_isGenericPoint_open_of_isGenericPoint
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [Etale f]
    (η : X) (hη : η ∈ genericPoints X) (y : Y) (hy : f y = η) :
    ∃ (W : Y.Opens) (hyW : y ∈ W),
      IrreducibleSpace W.toScheme ∧
      IsGenericPoint (⟨y, hyW⟩ : W.toScheme) Set.univ  := by
  classical
  have hmin (z : Y) (hz : z ⤳ y) : z = y := by
    have hz' : f z ⤳ η := hy ▸ hz.map f.continuous
    have hle : closure ({η} : Set X) ⊆ closure ({f z} : Set X) := hz'.closure_subset
    have heq : η = f z := isGenericPoint_closure.eq
      (hle.antisymm (hη.2 isIrreducible_singleton.closure hle)).symm
    exact f.eq_of_specializes_of_apply_eq hz (heq.symm.trans hy.symm)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨A, hA, hyA, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  let a : A.toScheme := ⟨y, hyA⟩
  let := IsLocallyNoetherian.component_noetherian (X := Y) ⟨A, hA⟩
  let : TopologicalSpace.NoetherianSpace A.toScheme := noetherianSpace_of_isAffineOpen A hA
  have hcomp (Z : Set A.toScheme) (hZ : Z ∈ irreducibleComponents A.toScheme)
      (haZ : a ∈ Z) : Z = closure ({a} : Set A.toScheme) := by
    have hz := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
    have hza : hZ.1.genericPoint = a := by
      apply Subtype.ext
      exact hmin _ ((hz.specializes haZ).map A.ι.continuous)
    rw [hza] at hz
    exact hz.def.symm
  obtain ⟨B, hBopen, haB, hBpre⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_isPreirreducible a
      (fun Z₁ hZ₁ Z₂ hZ₂ ha₁ ha₂ ↦ (hcomp Z₁ hZ₁ ha₁).trans (hcomp Z₂ hZ₂ ha₂).symm)
  let B' : A.toScheme.Opens := ⟨B, hBopen⟩
  let b : B'.toScheme := ⟨a, haB⟩
  let : IrreducibleSpace B'.toScheme :=
    Subtype.irreducibleSpace (⟨⟨a, haB⟩, hBpre⟩ : IsIrreducible B)
  have hgb : IsGenericPoint b Set.univ := by
    have h := genericPoint_spec B'.toScheme
    have heq : genericPoint B'.toScheme = b := by
      apply Subtype.ext
      apply Subtype.ext
      exact hmin _ ((h.specializes (Set.mem_univ b)).map
        (B'.ι ≫ A.ι).continuous)
    exact heq ▸ h
  let W : Y.Opens := A.ι ''ᵁ B'
  have hyW : y ∈ W := ⟨a, haB, rfl⟩
  have hygen : IsGenericPoint (⟨y, hyW⟩ : W.toScheme) Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro z
    simp only [Set.mem_univ, iff_true]
    obtain ⟨z', hz'B, hz'⟩ := z.property
    apply (subtype_specializes_iff _ _).mpr
    have h := (hgb.specializes (Set.mem_univ (⟨z', hz'B⟩ : B'.toScheme))).map
      (B'.ι ≫ A.ι).continuous
    change y ⤳ A.ι z' at h
    change A.ι z' = z.val at hz'
    rw [hz'] at h
    exact h
  refine ⟨W, hyW, ?_, hygen⟩
  exact (irreducibleSpace_def W.toScheme).mpr hygen.isIrreducible


end AlgebraicGeometry.Scheme
