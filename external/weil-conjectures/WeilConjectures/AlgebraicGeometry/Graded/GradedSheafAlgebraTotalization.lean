/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.GradedSheafAlgebra.GradedSheafAlgebraTotal

/-! # Totalizing a homogeneous sheaf algebra

Source: Stacks Project, Divisors, Section 0630; Cohomology of Schemes, Lemma 087Z.
(blueprint: lem-pur-graded-sheaf-algebra-totalization).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A homogeneous sheaf algebra has a total algebra whose underlying module is
its sheaf coproduct. Its products and structure map agree with the given operations.
Source: Stacks Project, Divisors, Section 0630; Cohomology of Schemes, Lemma 087Z.
(blueprint: lem-pur-graded-sheaf-algebra-totalization).

Proof: On each open form the direct sum of the homogeneous section modules.
The bilinear products extend to convolution on finite sums. The graded laws give
an ordinary commutative ring and the degree-zero unit defines the scalar map.
Restrictions are ring maps by naturality. Sheafify this presheaf of rings and its
scalar map; its underlying additive sheaf is the sheafification of the direct-sum
presheaf, with the induced module structure. A morphism from that sheaf to any
module sheaf is, by sheafification and the sectionwise direct-sum universal property,
exactly a family of module morphisms from the homogeneous pieces. This proves the
cofan is colimiting. The sheafification unit preserves multiplication and the scalar
map, proving both displayed formulas. No assertion that sections on arbitrary
opens commute with infinite sums is made. The construction includes the zero
algebra and the empty scheme. -/
theorem exists_gradedSheafAlgebra_totalization {Z : Scheme.{u}}
    (C : ℕ → Z.Modules) (D : GradedSheafAlgebra C) :
    ∃ (A : Z.CommAlgebraSheaf) (j : ∀ n, C n ⟶ A.toModule),
      Nonempty (IsColimit (Cofan.mk A.toModule j)) ∧
      (∀ (m n : ℕ) (V : Z.Opens)
        (a : (C m).val.obj (op V)) (b : (C n).val.obj (op V)),
        (@id (A.right.obj.obj (op V)) ((j m).val.app (op V) a)) *
          (@id (A.right.obj.obj (op V)) ((j n).val.app (op V) b)) =
          (j (m + n)).val.app (op V) (D.mul m n V a b)) ∧
      (∀ (V : Z.Opens) (r : Γ(Z, V)),
        (j 0).val.app (op V) (D.unit.val.app (op V) r) = A.hom.hom.app (op V) r) := by
  obtain ⟨A, j, hj, hmul, hunit⟩ := GradedSheafAlgebra.exists_total C D
  exact ⟨A, j, hj, fun m n V a b ↦ (hmul V m n a b).symm, hunit⟩

end AlgebraicGeometry
