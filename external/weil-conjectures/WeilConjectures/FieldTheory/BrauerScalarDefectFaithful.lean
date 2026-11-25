/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectFaithfulForward
import WeilConjectures.FieldTheory.BrauerScalarDefectFaithfulBackward

/-!
# Faithfulness and independence of scalar-defect classes

Source: Stacks Project, Theorem 03R7, homomorphism and injectivity arguments.
(blueprint: lem-sc-brauer-scalar-defect-faithful).
-/

@[expose] public section

universe u

namespace Field

/-- Two scalar-defect realizations give the same cohomology class exactly when their
algebras are Brauer equivalent. In particular the class of each algebra is unique.

Proof: changing a splitting conjugates the projective descent datum; changing matrix
lifts multiplies its scalar defect by a continuous coboundary. These changes therefore
preserve its class. A matrix amplification uses the tensor product of the lifts with
identity matrices, so preserves the same scalar defect. An isomorphism between matrix
amplifications consequently proves the reverse implication.
For the forward implication, equality of classes means their homogeneous cocycles differ
by a boundary: the underlying module of TopModuleCat homology is the algebraic kernel
modulo the image. In inhomogeneous coordinates this is a continuous scalar coboundary.
Tensor the descent datum of the first algebra with that of the opposite of the second.
Its defect is the ratio of their defects. Adjust its matrix lifts by the scalar
one-cochain to make them a genuine general-linear cocycle. All the data descend to a
finite Galois extension. Matrix Hilbert 90, or finite Galois descent of vector spaces,
trivializes this cocycle. The tensor product algebra is thus an endomorphism algebra.
The central-simple-algebra criterion that `A ⊗ Bᵒᵖ` is split exactly when A and B have
isomorphic positive matrix amplifications gives `IsBrauerEquivalent A B`.
The homogeneous/inhomogeneous conversions use evaluation at `(1,g,g*h)` and its
Galois-equivariant inverse, so the classes here are exactly those in the stated relation.

Source: Stacks Project, Theorem 03R7 (homomorphism and injectivity), and the scalar-defect
construction preceding it; Section 0DVG for the cochain convention.
(blueprint: lem-sc-brauer-scalar-defect-faithful). -/
theorem brauerScalarDefect_eq_iff (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y) :
    x = y ↔ IsBrauerEquivalent A B := by
  constructor
  · intro hxy
    exact brauerEquivalent_of_brauerScalarDefect_eq K A B x y hx hy hxy
  · intro hAB
    exact brauerScalarDefect_eq_of_brauerEquivalent K A B x y hx hy hAB

end Field
