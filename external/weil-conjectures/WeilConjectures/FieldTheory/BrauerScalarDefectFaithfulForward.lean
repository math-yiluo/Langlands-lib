/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import WeilConjectures.FieldTheory.BrauerScalarDefectAmplification
import WeilConjectures.FieldTheory.BrauerScalarDefectUnique
@[expose] public section
universe u
namespace Field

private theorem scalarDefect_transport (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (f : A ≃ₐ[K] B) (x : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) : HasBrauerScalarDefect K B x := by
  obtain ⟨n, hn, e, b, hb, z, hz, hdesc, hdefect⟩ := hx
  let t := Algebra.TensorProduct.congr
    (AlgEquiv.refl : SeparableClosure K ≃ₐ[SeparableClosure K] SeparableClosure K) f.symm
  refine ⟨n, hn, t.trans e, b, hb, z, hz, ?_, hdefect⟩
  intro g a
  simpa [t] using hdesc g (f.symm a)

/-- Equality of scalar-defect classes follows from Brauer equivalence.

Given matrix amplifications of `A` and `B` that are isomorphic, tensor the two
splittings and their projective descent lifts (using the opposite lift for `B`).
The scalar defect of the tensor lift is the quotient of the two scalar defects.
Changing a lift by the resulting scalar one-cochain changes its homogeneous
two-cocycle by the corresponding coboundary.  Thus the two representatives have
the same image under `ContinuousCohomology.π`, and hence `x = y`.  This is the
comparison calculation in Stacks Project, Theorem 03R7, with the homogeneous to
inhomogeneous conversion from Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-faithful-forward). -/
theorem brauerScalarDefect_eq_of_brauerEquivalent (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : IsBrauerEquivalent A B) : x = y := by
  obtain ⟨n, m, hn, hm, ⟨f⟩⟩ := h
  let : NeZero n := ⟨hn⟩
  let : NeZero m := ⟨hm⟩
  let C : CSA.{u, u} K := { toAlgCat := .of K (Matrix (Fin n) (Fin n) A) }
  let D : CSA.{u, u} K := { toAlgCat := .of K (Matrix (Fin m) (Fin m) B) }
  have hxC : HasBrauerScalarDefect K C x :=
    hasBrauerScalarDefect_of_matrix_algEquiv K A C x n hn AlgEquiv.refl hx
  have hyD : HasBrauerScalarDefect K D y :=
    hasBrauerScalarDefect_of_matrix_algEquiv K B D y m hm AlgEquiv.refl hy
  have hxD : HasBrauerScalarDefect K D x := scalarDefect_transport K C D f x hxC
  exact brauerScalarDefect_unique K D x y hxD hyD
end Field
