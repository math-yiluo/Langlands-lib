/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The fixed homogeneous modules of the conormal algebra

The definitions here are the tensor pullbacks of actual ideal powers, with their
adjunction representatives. Source: Stacks Project, Divisors, Tags 0630--0633.
(blueprint: lem-pur-conormal-graded-algebra-basic).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
noncomputable section
namespace AlgebraicGeometry.ConormalGradedAlgebra
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The ideal-power module with its actual inclusion, including `I^0 = O_X` and `I^1 = I`.
Source: Stacks Tags 0630, 0633 (blueprint: lem-pur-conormal-graded-algebra-basic). -/
def power (n : ℕ) : X.Modules :=
  (Scheme.idealSheafPower i.ker.toModulesι n).1

/-- The inclusion of the ideal power in the structure sheaf.
Source: Stacks Tag 0633 (blueprint: lem-pur-conormal-graded-algebra-basic). -/
def powerInclusion (n : ℕ) : power i n ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.idealSheafPower i.ker.toModulesι n).2

/-- The degree `n` conormal module on `Z`, namely `i^*(I^n) = I^n/I^(n+1)`.
Source: Stacks Tag 0633 (blueprint: lem-pur-conormal-graded-algebra-basic). -/
def piece (n : ℕ) : Z.Modules := (Scheme.Modules.tensorPullback i).obj (power i n)

/-- Pull a representative of an ideal-power section to its quotient class on `Z`.
Source: Stacks Tags 0631, 0633 (blueprint: lem-pur-conormal-graded-algebra-basic). -/
def representative (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    (piece i n).val.obj (op (i ⁻¹ᵁ U)) :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    (power i n)).val.app (op U) a

/-- The homogeneous class in an algebra with specified homogeneous inclusions.
Source: Stacks Tags 0630, 0633 (blueprint: lem-pur-conormal-graded-algebra-basic). -/
def homogeneousClass (A : Z.CommAlgebraSheaf) (j : ∀ n, piece i n ⟶ A.toModule)
    (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
    A.right.obj.obj (op (i ⁻¹ᵁ U)) :=
  (j n).val.app (op (i ⁻¹ᵁ U)) (representative i n U a)

/-- The quotient identification of the closed-subscheme local ring, induced by the actual
surjective structure-stalk map. Source: Stacks Tag 0633
(blueprint: lem-pur-conormal-graded-algebra-basic). -/
def quotientStalk (z : Z) :
    X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom ≃+* Z.presheaf.stalk z :=
  RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)

end AlgebraicGeometry.ConormalGradedAlgebra
