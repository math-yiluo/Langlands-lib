# Effective unitary exact expansion: statements

Author: Worker 981.

This pair states that every actual continuous unitarizable finite-dimensional
complex representation has its whole exact class expanded by a nonnegative
integral combination of genuine unitary irreducible classes. It does not prove
that assertion. The only theorem proved here is the definitional equivalence of
the local proposition with the generic one at the published local Weil group.

## Generic statement

In namespace `Langlands.VirtualRepresentation.Weil`, for every
`G : Type uG` with `[Group G]` and `[TopologicalSpace G]`, and with an
independent representation-carrier universe `uV`,
`EffectiveUnitaryExactExpansionStatement G` is the proposition:

for every `A : Langlands.FiniteRepresentation.{0, uG, uV} ℂ G`, every proof
`hc : A.IsContinuous` and every proof of `A.IsUnitary`, there is
`x : UnitaryLattice.{uG, uV} G` with `x ∈ VirtualRepresentation.effective`
and
`ExactExpansion G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩)
(includeUnitary G x)`.

It is a `Prop`-valued definition whose outer parameters are exactly the group,
its group structure and its topology. Its universe parameters are `uG` and
`uV`, independently.

The ingredients are all existing published constructions:

- `FiniteRepresentation.IsUnitary` (from `Weil.Representation.Predicates`)
  is existence of an `InnerProductSpace.Core ℂ` structure on the carrier, that
  is a positive-definite Hermitian inner product, preserved by every
  `A.representation g`. No form is chosen.
- `FiniteRepresentation.IsContinuous` is continuity of the action into the
  endomorphism space with its usual complex module topology.
- `UnitaryLattice G` (from `Weil.Generic`) is the finite-support integer module
  on `UnitaryBasis G`, the genuine continuous irreducible isomorphism classes
  across all positive ranks whose class contains an actual representation
  satisfying `IsUnitary`. `includeUnitary G` is the existing inclusion into the
  full irreducible lattice.
- `VirtualRepresentation.effective` is the additive submonoid of coefficientwise
  nonnegative integer combinations. The fully qualified name is used because the
  local namespace has a different `LocalWeil.effective` on the full lattice.
- `ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩` is the class of the whole
  representation `A` in `ContinuousExactGroup G`, the exact Grothendieck group
  of continuous finite-dimensional complex representations from
  `Weil.ExactRealization` and `VirtualRepresentation.Exact`.
- `ExactExpansion G c v` (from `Weil.ExactRealization`) means precisely
  `realizeExact G v = c`, where `realizeExact` sends each irreducible class
  generator to the exact class of a representative.

Thus the conclusion says that the entire exact class of `A` is the sum, with
nonnegative integer multiplicities, of the exact classes of genuine continuous
irreducible unitary classes. The proposition does not assume that `A` is
irreducible or semisimple, has finite image, has positive rank, or comes with an
invariant complement or decomposition. It does not assume exact-realization
bijectivity, a chosen inverse, or `IsTopologicalGroup G`, and it does not refer
to a supplied summand or selected constituent. It asserts no uniqueness of `x`,
no chosen expansion function and no canonical decomposition. Uniqueness of
expansions in the full irreducible lattice is the separate exact-K0 statement
`Weil.ExactExpansionUniqueStatement`, which this pair neither uses nor
duplicates.

## Actual local Weil specialization

In namespace `Langlands.VirtualRepresentation.LocalWeil`, with outer
parameters `{p : ℕ}`, `[Fact p.Prime]` and `F : Langlands.PadicField.{uF} p`,
`EffectiveUnitaryExactExpansionStatement F` makes the same assertion for every
`A : FiniteRepresentation.{0, uF, uW} ℂ (Langlands.Weil.Local.localWeilGroup F)`
that is continuous and satisfies `IsUnitary`. It uses the published
`LocalWeil.UnitaryLattice`, `LocalWeil.includeUnitary`,
`LocalWeil.ContinuousExactGroup` and `LocalWeil.ExactExpansion` directly. These
are the existing specializations to the published local Weil group, not an
independently supplied group model, and the carrier universe `uW` is
independent of `uF` and is not resized. Its universe parameters are `uF` and
`uW`.

`LocalWeil.effectiveUnitaryExactExpansion_iff` proves
`EffectiveUnitaryExactExpansionStatement F ↔
Weil.EffectiveUnitaryExactExpansionStatement (localWeilGroup F)` by `Iff.rfl`:
the local proposition is definitionally the generic one at that group. Neither
side is asserted.

## Proposed proof route (internal derived mathematics)

The following explains why the statement is expected to hold and why its
hypotheses suffice. None of these representation-theoretic steps is
implemented or asserted as a theorem here; the existence proof is a separate
successor task.

Fix an invariant positive Hermitian form on `A`. It restricts to a positive
invariant form on every invariant subspace `W`. The orthogonal complement of
`W` is invariant as well: each `A.representation g` is invertible with inverse
`A.representation g⁻¹`, so for `v` orthogonal to `W` and `w` in `W`,
`⟪ρ(g) v, w⟫ = ⟪v, ρ(g⁻¹) w⟫ = 0`. Hence `A` splits as `W ⊕ W⊥`. Induction on the
finite complex dimension then yields a finite direct-sum decomposition of `A`
into nonzero algebraically irreducible invariant subspaces.

Each constituent inherits continuity: its action is the original action
composed with a fixed linear inclusion and a fixed linear projection, and these
operations are continuous on finite-dimensional complex endomorphism spaces.
The published helpers in `Weil.Representation.SubquotientContinuity`, such as
`isContinuous_subrepresentation` and `isContinuous_of_injective_intertwiner`,
supply this argument. Each constituent also inherits a positive invariant form
by restriction, through the existing `InvariantPositiveForm.comap`,
`IsUnitarizable.of_injective` and `isUnitary_iff_isUnitarizable`
(`Representation.Unitary.Basic` and `Weil.Representation.UnitaryProof`).
Therefore each constituent defines a genuine continuous irreducible unitary
class of positive rank, i.e. an element of `UnitaryBasis G`.

A finite direct sum is an iterated split short exact sequence, so in the exact
quotient the class of `A` equals the sum of the classes of its constituents.
Letting `x` count each unitary class with its multiplicity in the decomposition
gives coefficients that are nonnegative integers, and
`realizeExact G (includeUnitary G x)` is that sum, which is the full exact
class of `A`.

The scope is justified as follows.

- Group with a topology: the continuity transfer uses only fixed linear maps
  composed with the continuous map `G → Module.End ℂ A`; continuity of
  multiplication or inversion on `G` is never used, so `IsTopologicalGroup G`
  is not needed. The orthogonal-complement argument uses only that `G` is a
  group acting by invertible operators.
- Zero case: a rank-zero `A` has exact class zero (the published
  `ExactGrothendieckGroup.ofRepresentation_eq_zero_of_rank_zero` in
  `VirtualRepresentation.ExactTensor`). It is witnessed by `x = 0`, the empty
  sum, which is effective.
- Universes: subspaces of a carrier in `Type uV` are again carriers in
  `Type uV`, so every constituent and its unitary representative live in the
  same carrier universe as `A`, independent of `uG`. No universe lifting or
  resizing occurs.

## Source provenance

This proposition is an internal derived statement, not a transcription of a
numbered theorem. It is needed to instantiate the full local unitary
restriction used by Henniart. Henniart does not state this generalized
finite-dimensional proposition, and its proof is not already formalized.

The source conventions were checked directly in this registered original:
Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), source ID `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

- §1.1, printed p.439 (PDF p.1), defines the continuous irreducible
  rank-indexed complex Weil classes.
- §2.4, printed p.445 (PDF p.7), works with continuous irreducible unitary
  representations `S` of the global Weil group associated with unitary
  cuspidal automorphic representations.
- §2.5, printed pp.445–446 (PDF pp.7–8), forms `R_G(F_{v0})`, the free integer
  module on the disjoint union over positive ranks of the local continuous
  irreducible classes, whose elements are viewed as classes of semisimple
  virtual representations. It assigns to such a pair the class of the full
  local restriction `S_{v0}` in that module. This local restriction is
  continuous and unitary but need not be irreducible, which is why an
  expansion of every such representation is needed.
- §2.7, printed p.447 (PDF p.9), refers to the unitary elements of that basis.

No errata for this source are registered in the literature index. The
arbitrary group-with-topology scope and the expansion of every finite-dimensional
continuous unitarizable representation are explicit internal generalizations,
justified by the route above.
