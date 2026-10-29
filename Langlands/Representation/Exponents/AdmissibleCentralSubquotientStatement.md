# Detecting a central scalar subquotient in the full dual

This module defines the proposition
`Langlands.AdmissibleCentralSubquotientStatement.{uG,uA,uV,uW}`.
It contains no proof. The group `G`, the commutative parameter group `A`,
the ambient carrier `V` and the quotient carrier `W` have four independent
universes. The module imports only
`Langlands.Representation.Exponents.DualJacquet`, which supplies
`commutativeTranspose` and `commutativeCharacterSpace` and, through its
imports, the published `IsAdmissible` predicate and Mathlib's
`Subrepresentation`. No new representation, dual or character-space
construction is introduced.

## Hypotheses

Let `G` be a topological group whose compact open subgroups are cofinal
among its open subgroups: every open subgroup `H` contains an open
subgroup `K` that is compact as a subset of `G`. Let `A` be a commutative
topological group and `c : A →* Subgroup.center G` a homomorphism that
is continuous for the subspace topology on the center. Let `V` be a
complex vector space, with no topology, and `ρ : Representation ℂ G V` an
admissible representation. The published `IsAdmissible ρ` says that
every vector is fixed by some open subgroup, and that for every open
subgroup the space of fixed vectors is a finitely generated, hence
finite-dimensional, complex vector space.

Let `χ : A →* ℂˣ` be an arbitrary homomorphism; no continuity of `χ` is
assumed. Let `U : Subrepresentation ρ` be an actual `G`-invariant
subspace, `W` a nonzero complex vector space and
`q : U.toSubmodule →ₗ[ℂ] W` an actual surjective linear map. The last
hypothesis is scalar equivariance under the supplied central map:
`q (ρ(c a) u) = χ(a) • q u` for every `a : A` and `u ∈ U`, where the
action on `U` is the restriction `U.toRepresentation`. Thus `W` is a
nonzero quotient of `U` on which `c(A)` acts by the scalar `χ`. No
representation structure or admissibility is required on `W`, and no
irreducibility, finite length, finite generation, cuspidal support,
global finite-spectrum, full-dual generalized spanning, preselected
eigenfunctional or central projector hypothesis is imposed on `ρ` or
`U`.

## Conclusion

The conclusion has two parts.

1. `IsOpen (χ.ker : Set A)`: the kernel of the same `χ` is open in the
   original supplied topology on `A`.
2. The ordinary eigenspace with power exactly `1`,
   `commutativeCharacterSpace (commutativeTranspose (ρ.comp f)) χ 1`,
   is not `⊥`, where `f = (Subgroup.center G).subtype.comp c : A →* G`.
   Here `commutativeTranspose` acts on the full algebraic dual
   `Module.Dual ℂ V` by `(a • φ)(v) = φ(ρ(f a) v)`
   (`commutativeTranspose_apply`). By
   `mem_commutativeCharacterSpace_one`, the conclusion says that there is
   a nonzero linear functional `φ : V →ₗ[ℂ] ℂ` with
   `φ(ρ(c a) v) = χ(a) φ(v)` for all `a` and `v`.

The character is the same `χ`, without inversion or complex conjugation.
The conclusion does not assert that `φ` restricts to a chosen functional
on `U`, or that it factors through `q`. It asserts no finite spectrum,
uniform nilpotence index, generalized-eigenspace spanning or other
decomposition of the full dual of an arbitrary admissible
representation.

## Provenance and credit

This is a derived internal algebraic interface. It is not a verbatim
numbered theorem of Silberger or of any other literature source, and
it makes no external literature claim. Its intended consumer is a
general-source opposite-Jacquet exponent adapter needed by the
pointwise tempered cone bound (task
`b6bc7ad9-2ad5-40a0-af80-2581a3fd920e`); neither that adapter nor the
cone bound is supplied here. The published irreducible-source
statements, such as `GLDualJacquetFinitenessStatement` and
`GLOppositeJacquetSubquotientExponentInheritanceStatement`, assume an
irreducible ambient source; this statement neither strengthens nor
replaces them.

Worker 84 suggested the finite-fixed-space and central-equivariant
averaging route. Worker 728 supplied an informal consistency check and
local route, without Lean evidence, and confirmed that the
general-source gap lies outside the existing irreducible-source
inheritance interfaces. Worker 429 isolated this interface, identified
the existing generic spectral suppliers and drafted this statement
pair. Worker 261 finalized it for submission. This coordination is
neither semantic acceptance nor a proof.

## Intended proof route

The following route explains why the statement is expected to hold; it
adds no hypothesis and all of its steps are proof obligations.

Choose `u ∈ U` with `q u ≠ 0`. Smoothness gives an open subgroup fixing
`u`. Its preimage under the continuous map `c` is an open subgroup of `A`,
and the scalar equation forces `χ = 1` there, so the kernel of `χ` is
open in the original topology. This step uses smoothness and continuity
of `c`, not finite dimensionality.

Cofinality gives a compact open subgroup `K` fixing `u`. Admissibility
makes this ONE fixed space `V^K` finite dimensional, and it is stable under
each `ρ(c a)` because `c a` is central. Restricting `q` to `U ∩ V^K`
gives a nonzero scalar quotient of a finite-dimensional space. The
published `Langlands.finiteActionCommutativeSpectrum` and
`Langlands.scalarSubquotientDualSpectrum` can then detect `χ` as an
ordinary eigencharacter of the dual of `V^K`; a temporary discrete
topology on `A` may be used in this algebraic step only. Composing the
detected functional with compact averaging over `K` extends it to `V`.
Since each `ρ(c a)` is a `G`-intertwiner, averaging commutes with it, and
averaging is the identity on `V^K`, so the extension is a nonzero
`χ`-eigenfunctional. The temporary discrete topology gives no evidence
for the open-kernel conclusion, which must be proved in the original
topology.

## Boundaries

For an opposite-Jacquet application, admissibility of the actual Jacquet
representation, the actual invariant-subspace and scalar-map
constructions, and identifications of central topologies remain
separate obligations. This proposition gives no analytic exponent
criterion, upper-to-opposite or Weyl bridge, class-exponent
inheritance, cone bound, continuation, composition series, multiplicity
comparison, quotient or head theorem.
