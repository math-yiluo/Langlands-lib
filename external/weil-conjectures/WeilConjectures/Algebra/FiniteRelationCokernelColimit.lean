/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.Algebra.FiniteRelationMatrixLift
import WeilConjectures.Algebra.FiniteRelationQuotientComparison

/-!
# Descent of a finite relation cokernel

Source: Stacks Project, Algebra, Tag 05N7, proof of (1).
(blueprint: lem-pc-finite-relation-cokernel-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

/-- A finite relation matrix over a ring colimit has a stage cokernel whose
extension is the original cokernel.

Source: Stacks Project, Algebra, Tag 05N7, proof of (1),
label algebra-lemma-colimit-category-fp-modules.
(blueprint: lem-pc-finite-relation-cokernel-colimit).

Proof: express q in the standard bases of the two finite free modules. Represent
its finitely many coefficients at stages and take a common upper bound. The
represented coefficients define qi. Right exactness of tensor product identifies
the extension of the quotient by range qi with the quotient by the range of the
extended matrix. Tensoring the standard bases identifies that matrix with q,
so the two quotients are isomorphic. This also covers zero rows or columns. -/
theorem exists_stage_finite_relation_cokernel
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) (n m : ℕ)
    (q : (Fin m → (colimit F : CommRingCat)) →ₗ[(colimit F : CommRingCat)]
      (Fin n → (colimit F : CommRingCat))) :
    ∃ (i : I) (qi : (Fin m → F.obj i) →ₗ[F.obj i] (Fin n → F.obj i)),
      Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj
        (ModuleCat.of (F.obj i) (ULift.{v} ((Fin n → F.obj i) ⧸ LinearMap.range qi))) ≅
        ModuleCat.of (colimit F : CommRingCat)
          (ULift.{v} ((Fin n → (colimit F : CommRingCat)) ⧸ LinearMap.range q))) := by
  obtain ⟨i, qi, hqi⟩ := exists_stage_finite_relation_matrix F n m q
  exact ⟨i, qi, finite_relation_quotient_comparison F n m q i qi hqi⟩

end ModuleCat
