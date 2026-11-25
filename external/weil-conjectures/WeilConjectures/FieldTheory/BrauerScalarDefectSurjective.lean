/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.CrossedProductRealization

/-!
# Crossed-product realization of continuous degree-two classes

Source: Stacks Project, Theorem 03R7, surjectivity argument, and Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-surjective).
-/

@[expose] public section

universe u

namespace Field

/-- Every continuous degree-two Galois class is realized by matrix scalar defects
of a central simple algebra.

Proof: the map from cycles to homology is surjective on underlying modules, since
TopModuleCat homology is the algebraic kernel modulo image with quotient topology.
Choose a homogeneous cycle representing `x`. Uncurry its iterated continuous maps,
using compact Hausdorffness of the Galois group, and evaluate at `(1,g,g*h)` to obtain
a continuous multiplicative two-cocycle `c`. Its values have finite image in the discrete
units. Compactness and local constancy give an open normal subgroup on whose cosets
`c` is constant; shrink it also to fix all values. Its fixed field L is finite Galois
over K and `c` is inflated from a cocycle on Gal(L/K) with values in Lˣ.
Normalize `c` by a coboundary. Form the crossed product with L-basis `u_g`, multiplication
`u_g a = g(a) u_g` and `u_g u_h = c(g,h) u_(g*h)`. The cocycle identity makes this
associative and normalization gives its unit. Commuting with L forces a central element
into L, and commuting with all `u_g` forces it into K. The usual minimal-support
argument proves simplicity, and its K-dimension is `[L:K]^2`.
The crossed product splits over L. In its regular splitting representation the
projective descent matrices have scalar defect `c` (choose the opposite algebra if
the splitting convention gives the inverse class). Inflate those matrices to the
absolute Galois group; they are locally constant and satisfy the two equations in
`HasBrauerScalarDefect`. Their homogeneous cycle has class `x`, as normalization only
changed a coboundary. This supplies the required central simple algebra and realization.

Source: Stacks Project, Theorem 03R7, surjectivity argument; Section 0DVG for continuous
cochains and their homogeneous-coordinate interpretation.
(blueprint: lem-sc-brauer-scalar-defect-surjective). -/
theorem exists_csa_brauerScalarDefect (K : Type u) [Field K] (x : GaloisUnitsH2 K) :
    ∃ A : CSA.{u, u} K, HasBrauerScalarDefect K A x := by
  obtain ⟨A, n, hn, e, b, hb, z, hz, hdesc, hdefect⟩ :=
    exists_crossedProduct_realization_data K x
  exact ⟨A, n, hn, e, b, hb, z, hz, hdesc, hdefect⟩

end Field
