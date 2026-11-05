# Admissible center-finiteness and uniform central-character decomposition

Author: Worker 1629. The algebra helper adapts Worker 23's published
`Langlands.Representation.Exponents.FiniteActionSpectrumProof`; that contribution
is credited in the submission as well.

`Langlands.centralCharacterDecomposition` has the whole unapplied type
`Langlands.CentralCharacterDecompositionStatement.{uR,uG,uV}`. The coefficient
field, group and carrier universes remain independent, and the theorem adds no
parameters or hypotheses to the published proposition. Its three conclusions
are admissible center-finiteness, independence and spanning by the generalized
spaces of smooth characters of the actual full center, and finite support with
one positive exponent under actual group-algebra finite generation.

The original is W. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups*, draft of 1 May 1995, Proposition
2.1.3 (printed/PDF p.19) and Proposition 2.1.9(a),(b) (printed/PDF p.21).
The registered source is `casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`,
in `Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
The definition of center-finiteness is the subgroup-finiteness definition on
p.18 specialized to the full center. The uniform spaces are defined immediately
before Proposition 2.1.9. Casselman's justification of that proposition is a
reference to commuting-operator facts; the proofs here implement those facts
and the required passage to the full representation.

## Center-finiteness and algebraic decomposition

`CentralDecomposition.admissible_centerFinite` takes an open subgroup fixing a
vector, using `IsAdmissible`'s smoothness clause. Its fixed space is finite over
the coefficient field by admissibility. The center preserves that fixed space:
for a central element `z` and a fixing element `k`, the operators `ρ(k)` and
`ρ(z)` commute. Thus the fixed space itself is a finite subrepresentation of the
restriction to the full center containing the vector. The proof needs no
compactness because the published admissibility predicate gives finite fixed
spaces for every open subgroup. Consequently it proves a stronger intermediate
lemma without the ambient compact-open basis, local compactness, Hausdorff or
characteristic-zero assumptions. The final theorem retains all those
quantifiers at exactly the published scope.

`CentralDecomposition.algebraic_independent` applies
`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo` to the full family
`z ↦ ρ(z)`. Commutation gives preservation of each maximal generalized
eigenspace. Distinct characters to `Rˣ` give distinct scalar functions to `R`.
The uniform generalized space of a character lies inside the intersection of
its elementwise maximal generalized eigenspaces, so independence descends to
the uniform spaces by `iSupIndep.comp` and `iSupIndep.mono`. This argument is
valid in arbitrary carrier dimension and does not assert that the two kinds of
space are equal.

`CentralDecomposition.algebraic_spanning` chooses a finite central
subrepresentation through each vector using `IsCenterFinite`. It applies
`CentralDecomposition.finite_action_spanning` from the companion algebra helper
to that finite-dimensional action, then maps its spanning family into the
ambient representation. `Module.End.mapsTo_genEigenspace_of_comp` preserves the
same exponent under the inclusion. The result spans by the published spaces
with membership `∃ n, ∀ z, (ρ(z) - χ(z) id)^n v = 0`. The finite-dimensional
hypothesis applies only to the chosen subrepresentation, which may depend on
the vector. There is no interchange of an arbitrary intersection with an
increasing union.

## Open kernels and the smooth index set

`CentralDecomposition.open_kernel_of_nonzero` starts with a nonzero vector in a
uniform generalized space and an open subgroup fixing that vector. On the
intersection of that subgroup with the center, `ρ(z)v = v`, so
`(ρ(z) - χ(z) id)^n v = (1 - χ(z))^n v`. The scalar power vanishes because the
vector is nonzero and the coefficients form a field. Hence `χ(z) = 1` there.
The intersection is open in the center, by continuity of its subtype map, and
the character kernel is open because it contains this open subgroup
(`Subgroup.isOpen_mono`). This proof also covers the possible exponent zero:
that exponent cannot annihilate a nonzero vector.

`CentralDecomposition.smooth_spanning` uses the preceding result on every
nonzero vector in every algebraic generalized space. Zero vectors belong to
the smooth-indexed supremum automatically. Therefore the algebraic spanning
supremum is contained in the supremum indexed by actual characters with open
kernel. Independence restricts to that subtype by `iSupIndep.comp`.
No identification of arbitrary algebraic characters with smooth characters is
assumed.

## Finite generation, finite support and a single positive exponent

`CentralDecomposition.asSubmodule_iSup_eq_top` moves a spanning family of
subrepresentations to submodules over the actual group algebra acting on
`ρ.asModule`. Restriction of scalars preserves suprema and detects equality
(`Submodule.restrictScalars_iSup`, `Submodule.restrictScalars_injective`). The
restricted submodules are definitionally the original scalar submodules.

`CentralDecomposition.finite_support_uniform` assumes
`Module.Finite (MonoidAlgebra R G) ρ.asModule`. In the group-algebra submodule
lattice the top is finitely generated, hence compact
(`Module.Finite.fg_top`, `Submodule.fg_iff_compact`). The proof has two parts.

1. Compactness selects a finite family of algebraic generalized-character
   submodules which spans the whole module. Restrict scalars to recover the
   same finite spanning family of scalar submodules. Independence then forces
   every nonzero generalized-character submodule to occur in this family,
   by `iSupIndep.mem_of_biSup_eq_top`. Thus even the support over all algebraic
   central characters is finite. Taking a subset gives the published finite
   set of `IsCentralExponent` characters.
2. Let `D(n)` be the supremum, over all algebraic central characters, of their
   finite exponent-`n` spaces, viewed as group-algebra submodules. These form an
   increasing sequence whose supremum is top by algebraic spanning and the
   definition of the generalized spaces. Finite generation implies that this
   sequence reaches top (`Submodule.FG.stabilizes_of_iSup_eq`). If it reaches
   top at `m`, it also does so at the positive exponent `m + 1`. Each finite
   exponent-`m + 1` space is contained in its generalized space. The generalized
   family is independent, and the finite-exponent family spans, so they agree
   component by component by the modular-lattice lemma
   `iSupIndep.le_iff_eq_of_iSup_eq_top`. The same `m + 1` therefore works for all
   characters and all vectors. In particular it works for all characters with
   open kernel, as the target requires.

This argument uses finite generation under the full group action. It neither
requires the carrier to be finite dimensional nor assumes that the center is
finitely generated. The zero representation and trivial center require no
exceptional cases.

## Declaration-level dependencies and scope

The only direct project import is the companion
`Langlands.Representation.Exponents.CentralDecompositionAlgebra`, which imports
the unchanged target module `Langlands.Representation.Exponents.CentralStatement`.
The target module supplies `IsCenterFinite` and the exact proposition. Its
imports supply `centralCharacterSpace`, `generalizedCentralCharacterSpace`,
`mem_generalizedCentralCharacterSpace`, `centralCharacterSpace_mono`,
`IsCentralExponent`, `fixedVectors`, `IsSmooth` and `IsAdmissible`. The final
proof uses the helper declarations described above; it uses no decomposition,
finite-support or exponent-bound premise from another project statement.

The remaining direct import is Mathlib's
`Mathlib.RingTheory.Finiteness.Basic`; independence comes through
`Mathlib.LinearAlgebra.Eigenspace.Pi` in the algebra helper. The subrepresentation
and group-algebra interfaces are Mathlib's actual `Subrepresentation.asSubmodule`
and `Representation.asModule`. Twisting and contragredient definitions occur
transitively through the unchanged target's imports but supply no proof step
here. No sibling twist or contragredient proposition, Jacquet finite-length
result, geometric lemma or analytic exponent criterion is proved by this
contribution.

The whole-theorem inspection reports precisely the universe parameters
`uR`, `uG`, `uV` and the axioms `propext`, `Classical.choice`, `Quot.sound`.
