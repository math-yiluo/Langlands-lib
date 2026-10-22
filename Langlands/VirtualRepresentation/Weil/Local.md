# Integral lattices for the actual local Weil group

Author: Worker 24. This module specializes the published representation
lattice to the published actual local Weil group.

For every prime `p` and actual `F : PadicField.{uF} p`, this module specializes
the published `VirtualRepresentation.Weil.Generic` construction to
`Langlands.Weil.Local.localWeilGroup F`. That group is the actual pullback of
the constructed absolute residue action along the geometric-normalized integer
inclusion into the profinite integers. It carries the existing Weil pullback
topology. The imported assembly constructs the field data and proves the
surjectivity needed for its Frobenius lift; this adapter accepts no replacement
group, arithmetic certificate, or assumed local comparison.

The representation-carrier universe `uV` remains independent of the field
universe. The rank family uses the existing
`LocalContinuousIrreducibleWeilClasses F (n : ℕ)` for positive `n`;
`Basis` and `Lattice` use these genuine continuous irreducible complex
representation classes in all positive dimensions of this actual local group.
Continuity means the usual finite-dimensional complex
module topology, not discrete complex coefficients. Degree is representation
dimension, extended by integer linearity. The full pairing is the integral
coefficient pairing.

`UnitaryBasis` is the actual subset defined by existence of an invariant
positive definite Hermitian form on a representative. `UnitaryLattice`,
`unitarySupported`, `unitaryModel`, inclusion, coefficient restriction,
degree and pairing specialize the already proved generic constructions.
No form or representative is chosen. In particular, the specified unitary
basis is not a new uninterpreted label type.

`finiteImageSupported` uses the existence of an actual finite-image
representative. `HasGaloisTypeClass` instead requires an actual representation
that extends continuously along the constructed `localProjection F` into the
absolute Galois group. The existing `IsLocalGaloisType` predicate reuses
the exact definition of `IsGaloisTypeAlong`;
these predicates are not identified by definition. Their support submodules
and the unitary Galois-type support therefore retain this distinction.

The finite-map support constructors take an explicit homomorphism from the
actual absolute Galois group to a finite group and compose it with the actual
local projection. They impose algebraic factorization of a representative
along this composite using the published generic predicate. The map is not
assumed continuous or onto. These are not asserted to be the global generating
families, nor to span the lattice. The finite target-group universe is
independent of the two other universes.

Rank inclusion, coefficient restriction and rank support use the genuine rank
summands. Effective elements have nonnegative multiplicities. Unitary rank
and invariant fibers, total-degree strata and effective total-degree strata
are defined without a finiteness, enumeration or surjectivity hypothesis.
The invariant fiber takes an explicit function and asserts no conductor or
central-character law. The actual-object class and generator constructors,
including the unitary versions, reuse the proved generic class constructors
at this specific local group. No representation decomposition,
semisimplicity, Brauer induction, isometry or Langlands correspondence is used.

## Sources and dependencies

This is a derived local specialization of Henniart (2000), section 1.1,
printed p.439; sections 2.4--2.7, pp.445--447; and the finite/Galois-type
motivation of section 3.1, p.448. The original retained PDF was read for these
constructions. Literature ID `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
No theorem identifying Galois type with finite image, or the global spanning
conclusion, is supplied here.

The direct imports are `Langlands.VirtualRepresentation.Weil.Generic` and
`Langlands.Weil.Local.Parameters`. The latter supplies the reused local class
and Galois-type declarations and imports `Langlands.Weil.Local.Assembly`.
That assembly module, authored by Worker 53, assembles
the published absolute residue action and finite-field comparison proofs,
the existing Weil pullback, and canonical field data. Its paired Markdown
records the original Weil-group and geometric-normalization sources.
This adapter imports those constructions without copying or replacing them.

All quotient and support well-definedness comes from the genuine generic
classes and finite-support constructions. The algebraic finite-factorization
maps use the actual composite homomorphism. Development compilation of this
module against published imports passed with no diagnostics in Lean 4.34.0,
with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The field,
representation-carrier and finite target-group universes remain independent.

Local twist and dual preservation,
their unitary restrictions and numerical orbit data, actual finite-extension
induction specialization, and the weakly-associated global families remain
separate required work.
