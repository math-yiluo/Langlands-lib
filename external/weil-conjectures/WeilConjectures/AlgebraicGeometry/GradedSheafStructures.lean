/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Homogeneous algebra and module operations on sheaves

Source: Stacks Project, Cohomology of Schemes, Lemma 087Z, the graded algebra and
module in its statement (blueprint: theorem-finite-etale-covers-proper-henselian--2).

Bilinear operations compatible with restrictions are sheaf operations. Their extension
by the sheaf coproduct universal property gives the algebra and module on the direct sums.
`HEq` expresses equality of homogeneous sections when their degrees differ only by an
associativity or unit identity in the natural numbers.
-/

@[expose] public section

universe ug

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A commutative unital graded O_X-algebra, specified on homogeneous sheaves by bilinear
multiplication, restriction compatibility, a linear unit, and the algebra laws.
Source: Stacks, Lemma 087Z (blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
structure GradedSheafAlgebra {X : Scheme.{ug}} (B : ℕ → X.Modules) where
  mul : ∀ (m n : ℕ) (U : X.Opens),
    (B m).val.obj (op U) →ₗ[Γ(X, U)]
      (B n).val.obj (op U) →ₗ[Γ(X, U)] (B (m + n)).val.obj (op U)
  unit : SheafOfModules.unit X.ringCatSheaf ⟶ B 0
  naturality : ∀ (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
    (a : (B m).val.obj (op U)) (b : (B n).val.obj (op U)),
    (B (m + n)).val.map (homOfLE h).op (mul m n U a b) =
      mul m n V ((B m).val.map (homOfLE h).op a)
        ((B n).val.map (homOfLE h).op b)
  assoc : ∀ (l m n : ℕ) (U : X.Opens) (a : (B l).val.obj (op U))
    (b : (B m).val.obj (op U)) (c : (B n).val.obj (op U)),
    HEq (mul (l + m) n U (mul l m U a b) c)
      (mul l (m + n) U a (mul m n U b c))
  comm : ∀ (m n : ℕ) (U : X.Opens) (a : (B m).val.obj (op U))
    (b : (B n).val.obj (op U)), HEq (mul m n U a b) (mul n m U b a)
  one_mul : ∀ (n : ℕ) (U : X.Opens) (a : (B n).val.obj (op U)),
    HEq (mul 0 n U (unit.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U))) a) a
  mul_one : ∀ (n : ℕ) (U : X.Opens) (a : (B n).val.obj (op U)),
    HEq (mul n 0 U a (unit.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U)))) a

/-- A graded module over a graded sheaf algebra, given by bilinear homogeneous actions,
compatible with restrictions and satisfying associativity and the unit law.
Source: Stacks, Lemma 087Z (blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
structure GradedSheafModule {X : Scheme.{ug}} {B : ℕ → X.Modules}
    (A : GradedSheafAlgebra B) (K : ℕ → X.Modules) where
  act : ∀ (m n : ℕ) (U : X.Opens),
    (B m).val.obj (op U) →ₗ[Γ(X, U)]
      (K n).val.obj (op U) →ₗ[Γ(X, U)] (K (m + n)).val.obj (op U)
  naturality : ∀ (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
    (a : (B m).val.obj (op U)) (x : (K n).val.obj (op U)),
    (K (m + n)).val.map (homOfLE h).op (act m n U a x) =
      act m n V ((B m).val.map (homOfLE h).op a)
        ((K n).val.map (homOfLE h).op x)
  assoc : ∀ (l m n : ℕ) (U : X.Opens) (a : (B l).val.obj (op U))
    (b : (B m).val.obj (op U)) (x : (K n).val.obj (op U)),
    HEq (act (l + m) n U (A.mul l m U a b) x)
      (act l (m + n) U a (act m n U b x))
  one_act : ∀ (n : ℕ) (U : X.Opens) (x : (K n).val.obj (op U)),
    HEq (act 0 n U (A.unit.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U))) x) x

/-- Local finite generation by homogeneous degree-zero sections. Every section in any
homogeneous degree is locally a linear combination of the restrictions of these sections,
with coefficients in the corresponding algebra degree. This is equivalent to a locally
surjective map from a finite sum of copies of the graded algebra (with zero shifts).
Source: Stacks, Lemma 087Z, affine proof
(blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
def GradedSheafModule.IsLocallyGeneratedInDegreeZero {X : Scheme.{ug}}
    {B K : ℕ → X.Modules} {A : GradedSheafAlgebra B} (M : GradedSheafModule A K) : Prop :=
  ∀ p : X, ∃ (U : X.Opens) (_hp : p ∈ U) (t : ℕ)
    (s : Fin t → (K 0).val.obj (op U)),
    ∀ (V : X.Opens) (hVU : V ≤ U) (n : ℕ) (y : (K n).val.obj (op V))
      (q : X) (_hq : q ∈ V),
      ∃ (W : X.Opens) (hWV : W ≤ V) (_hqw : q ∈ W)
        (a : Fin t → (B n).val.obj (op W)),
        HEq ((K n).val.map (homOfLE hWV).op y)
          (∑ i : Fin t, M.act n 0 W (a i)
            ((K 0).val.map (homOfLE (le_trans hWV hVU)).op (s i)))

end AlgebraicGeometry
