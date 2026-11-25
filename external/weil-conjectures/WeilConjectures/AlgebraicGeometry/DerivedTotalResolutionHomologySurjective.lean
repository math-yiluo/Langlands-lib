/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- Cycle lifting at column zero makes the total augmentation surjective on homology.
Source: Stacks Project, Homology, Tag 09IZ, proof and exactness of augmented kernels.
(blueprint: lem-pc-derived-total-resolution-homology-surjective)

Proof. Represent a degree n homology class of M by a cycle m. Surjectivity
of the augmentation on cycles gives a cycle x in (K.X 0)^n mapping to m.
Include x into the column-zero summand of the total complex. Its vertical
differential is zero since x is a cycle; its horizontal differential
lands in the zero column K.X 1, and hence is also zero. Thus it is a total
cycle. The augmentation identity on column zero says its image is m, so
its homology class is a preimage of the given class. This argument works
for every integer n and requires neither boundedness nor the other exact rows. -/
theorem total_resolution_homology_surjective
    (M : CochainComplex (ModuleCat R) ℤ)
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (ε : K.total (ComplexShape.up ℤ) ⟶ M)
    (a : K.X 0 ⟶ M)
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ i, M.HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (h_augmentation_zero : ∀ q : ℤ,
      K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q)
    (h_cycles_surjective : ∀ q : ℤ, Function.Surjective
      (HomologicalComplex.cyclesMap a q).hom) :
    Function.Surjective (HomologicalComplex.homologyMap ε n).hom := by
  classical
  have hd (q : ℤ) : (K.d 0 1).f q = 0 := by
    exact ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q).map_isZero
      (h_positive 1 (by omega))).eq_of_tgt _ _
  let j : K.X 0 ⟶ K.total (ComplexShape.up ℤ) :=
    { f := fun q ↦ K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp)
      comm' := by
        intro q q' h
        dsimp [ComplexShape.up] at h
        subst q'
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
          K.d₁_eq' (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1),
          K.d₂_eq (ComplexShape.up ℤ) 0
            (by simp : (ComplexShape.up ℤ).Rel q (q + 1)) _ (by simp), hd]
        simp [ComplexShape.ε₁, ComplexShape.ε₂] }
  have hja : j ≫ ε = a := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact h_augmentation_zero q
  have : Epi (HomologicalComplex.cyclesMap a n) :=
    (ModuleCat.epi_iff_surjective _).2 (h_cycles_surjective n)
  have : Epi (HomologicalComplex.homologyMap a n) :=
    epi_of_epi_fac (HomologicalComplex.homologyπ_naturality a n)
  have : Epi (HomologicalComplex.homologyMap j n ≫ HomologicalComplex.homologyMap ε n) := by
    rw [← HomologicalComplex.homologyMap_comp, hja]
    infer_instance
  exact (ModuleCat.epi_iff_surjective _).1 (epi_of_epi
    (HomologicalComplex.homologyMap j n) (HomologicalComplex.homologyMap ε n))

end WeilConjectures.DerivedTotalResolution
