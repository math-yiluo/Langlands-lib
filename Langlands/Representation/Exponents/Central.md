# Uniform generalized central-character spaces

Let `ρ` be a representation of a group `G` on an `R`-module `V`, where `R` is
a commutative ring, and let `χ : Subgroup.center G →* Rˣ`.
`centralCharacterSpace ρ χ n` is the actual invariant submodule of vectors `v`
such that

`(ρ(z) - χ(z) • id)^n v = 0` for every central element `z`.

The exponent `n` is common to all central elements. The construction intersects
Mathlib's finite generalized eigenspaces, and proves invariance using the
commutation of central action operators with the whole representation.
Exponent one gives exactly the vectors on which every central element acts by
the prescribed scalar.

`generalizedCentralCharacterSpace ρ χ` is the increasing union of these
subrepresentations. Its proved membership criterion is
`∃ n, ∀ z, (ρ(z) - χ(z) • id)^n v = 0`.
The single exponent may depend on `v`; it may not depend on `z`.
The Lean definition realizes this union as a directed supremum of submodules,
using monotonicity of finite generalized eigenspaces. It proves stability under
the action. Exponent zero contributes only the zero vector, so allowing natural
numbers starting at zero does not change the source's union starting at one.

Intertwiners preserve each finite space with its same exponent, and hence
preserve the generalized space. `centralCharacterMap` and
`generalizedCentralCharacterMap` are the resulting actual intertwiners between
the subrepresentations. `generalizedCentralCharacterEquiv` restricts an
ambient equivariant linear equivalence and its inverse to the generalized
spaces. These constructions use Mathlib's genuine intertwiner and
generalized-eigenspace mapping laws. The zero-exponent claim above is proved
in `centralCharacterSpace_zero`.

When `G` has a topology, `IsCentralExponent ρ χ` requires both an open character
kernel in the center's induced topology and a nonzero generalized space. This
is auxiliary central-character data for the given representation. Casselman's
Jacquet exponents additionally restrict such characters to the split component
of a Levi center. To obtain that notion one must use the actual Jacquet
representation and the actual split-center inclusion. This file does not
identify its full-center character type with the split-center exponent type.

## Source and correspondence

The source is Casselman, 1995 notes, section 2.1, printed page 21 (PDF page 21).
The original defines characters as homomorphisms with open kernel, gives
`V_{ω,n}` using the same power for all central elements, and then takes the union
over finite `n`. The file retains precisely that quantifier order. Section 4.4,
printed pages 44-45, uses nonzero generalized central-character spaces of
Jacquet modules as input to the definition of exponents.

The original discussion assumes smooth representations over a characteristic
zero field and introduces these spaces in the center-finite setting. The
formulas and invariant-submodule constructions here are algebraically meaningful
over an arbitrary commutative ring. This is a domain extension of the
definitions and their intrinsic fields only. The file makes no center-finiteness,
finite-exponent-set, direct-sum decomposition, finite-length, admissibility,
temperedness, or square-integrability claim. In particular, Proposition 2.1.9
and the analytic criteria of section 4.4 are not assumed or proved here.

- Literature ID: `casselman-1995-admissible-representations`.
- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft, 1 May 1995, section 2.1, page 21, and
  section 4.4, pages 44-45.
- Retained original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- SHA-256: `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.

## Formal dependencies

Only pinned Mathlib is imported. `Mathlib.LinearAlgebra.Eigenspace.Basic`
supplies the finite generalized eigenspaces, monotonicity and intertwiner
mapping theorem. `Mathlib.RepresentationTheory.Intertwining` supplies the
actual representations, invariant submodules and intertwiners.
`Mathlib.Topology.Algebra.Group.Subgroup` supplies the induced subgroup topology.

Environment artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Author: Worker 23.
