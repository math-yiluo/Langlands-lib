# Local occurrence in an irreducible cuspidal summand (statement)

Module `Langlands.TraceFormula.GroupSchemeCuspidalLocalOccurrenceStatement` contains one
proposition definition and no proof:

- `Langlands.TraceFormula.GroupSchemeCuspidalLocalOccurrenceStatement.{u}`.

In words: let `P` be a nonzero closed subspace of the group-scheme cuspidal space
`L²_cusp([G])` of a connected reductive group `G` over a number field `F`, invariant under
right translation by `G(𝔸_F)` and topologically irreducible, and let `v` be a finite place of
`F`. Then some irreducible admissible representation of `G(F_v)` occurs in `P`: it has a
nonzero `G(F_v)`-equivariant linear map into `P`.

## Setting and notation from the Library

The data and hypotheses are those of the Library statement
`Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement`, copied in the
same order, without its two Haar measures `μv` (on `G(F_v)`) and `ν` (on `G(𝔸_F)`), which
the present conclusion does not use. The Markdown of that statement and of
`GroupSchemeCuspidalLocalTraceFactorizationStatement` explains them in full. In brief:

- `F : Type u` is a number field and `G` an affine group scheme over `Spec F`, locally of
  finite type, with `hPD : ParabolicDynamicStatement.{u}`, `hG : IsConnectedReductive G`, a
  central map `i : T.toGrp ⟶ G` from a commutative group scheme `T` with injective character
  restriction `hi` of finite-index range, an isomorphism `e` of `T` with a split torus indexed
  by a finite type `I`, `hc : IsCentral i`, and right invariance of Haar measure on
  `normOneSubgroup F G`. These are the group data of the Library's cuspidal decomposition
  statement `Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalDecompositionStatement`.
- `v : Langlands.Global.FinitePlace F`, and `G(F_v) = PlaceGroupPoints F G (.inr v)` with the
  instance binders `[MeasurableSpace] [BorelSpace] [LocallyCompactSpace]
  [TotallyDisconnectedSpace]`. `ofPlace F G (.inr v) : G(F_v) → G(𝔸_F)` inserts a local point
  at `v` (identity at the other places); `G(𝔸_F) = AdelicGroupPoints F G`.
- `S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc` is the closed cuspidal subspace of
  `L²` of the quotient of `G(𝔸_F)` by `positiveRationalSubgroup F G T i`, and
  `πc a := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc a` is right translation
  by `a ∈ G(𝔸_F)` on `S`, a norm-preserving bounded operator.
- `Langlands.IsAdmissible ρ` (module `Langlands.Representation.Smooth.Definitions`) says that
  every vector is fixed by an open subgroup and that the fixed vectors of every open subgroup
  form a finitely generated, here finite-dimensional, space. `ρ.IsIrreducible` is Mathlib's
  `Representation.IsIrreducible`: the lattice of subrepresentations is `{⊥, ⊤}` with `⊥ ≠ ⊤`;
  this is algebraic irreducibility, no topology on `V` is involved.

## Statement

For all data as above and every finite place `v` with the four instance binders, let
`P : Submodule ℂ S` with `[CompleteSpace P]`, `P ≠ ⊥`, `P` invariant under every `πc a`, and
such that every closed subspace `Q ≤ P` invariant under every `πc a` is `⊥` or `P`. Then there
are `V : Type u` with `AddCommGroup V` and `Module ℂ V`, a representation
`ρ : Representation ℂ G(F_v) V` with `IsAdmissible ρ` and `ρ.IsIrreducible`, and a linear map
`j₀ : V →ₗ[ℂ] S` with `j₀ ≠ 0`, `LinearMap.range j₀ ≤ P` and

`j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)` for all `y ∈ G(F_v)` and `x ∈ V`.

The map `j₀` is only linear: `V` carries no topology and no continuity is asserted. The
carrier `V` lies in `Type u`, the universe of `F` and of `S`.

## Relation to the trace factorization statements

The conclusion is exactly clause 0 (realization) of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` together with the irreducibility and
admissibility of its representation `ρ`; nothing else is asserted. It is also, word for word,
the occurrence hypothesis of the Library theorem
`Langlands.TraceFormula.IsotypicTrace.cuspidalIsotypicTraceFactorization_of_exists_occurrence`
(module `Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction`), which derives the
whole conclusion of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` for `P` (all four
clauses, for any Haar measures `μv` and `ν`) from such an occurrence. So the present statement
implies `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` by that theorem. Conversely,
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` implies the present statement: take
for `μv` and `ν` the Haar measures `MeasureTheory.Measure.haar` (both groups are locally
compact topological groups with their Borel structures) and keep only clause 0. Neither
derivation is written in this file.

The reduction theorem is proved in the Library, with no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`, from the product decomposition
`G(𝔸_F) = G(F_v) × G(𝔸_F^v)` (`IsotypicTrace.placeSplitting`), Schur's lemma for the closure
of an occurrence (admissibility makes the fixed vectors of an open subgroup
finite-dimensional), a maximal orthogonal family of closures of equivariant copies of the
occurrence (Zorn's lemma), and the trace of a Hilbert sum. The present statement is therefore
the only input of that proof of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` that
is not elementary Hilbert space analysis.

## Why the statement is true

1. **Tensor decomposition.** `(y, h) ↦ ofPlace(y) h` is an isomorphism of topological groups
   `G(F_v) × G(𝔸_F^v) ≅ G(𝔸_F)`, where `G(𝔸_F^v)` is the subgroup of points with trivial
   component at `v`. Right translation on `P` is an irreducible unitary representation of this
   product (the closed-subspace hypothesis). `G(F_v)` is the group of `F_v`-points of an affine
   algebraic group over the characteristic-zero local field `F_v`, so it is of type I
   (Getz–Hahn, Theorem 3.10.2). Hence there are irreducible unitary representations `π_v` of
   `G(F_v)` on `H_v` and `π^v` of `G(𝔸_F^v)` on `H^v` and a unitary isomorphism
   `U : P ≅ H_v ⊗̂ H^v` carrying `πc (ofPlace y)` to `π_v(y) ⊗ 1` (Folland, Theorem 7.17).
2. **The local factor.** The base change of `G` to `F_v` is reductive. By Harish-Chandra and
   Bernstein (Getz–Hahn, Theorem 5.3.9) `π_v` is admissible: its space of smooth vectors
   `V = (H_v)^sm`, the vectors fixed by some compact open subgroup, is an admissible
   representation `ρ`, and it is irreducible because `π_v` is (Getz–Hahn, Proposition 5.3.8).
   Every open subgroup of the totally disconnected locally compact group `G(F_v)` contains a
   compact open subgroup, so these smooth vectors and this admissibility agree with
   `Langlands.IsSmooth` and `Langlands.IsAdmissible`, which use all open subgroups.
3. **The occurrence.** Fix a nonzero `ξ ∈ H^v` and put `j₀ x = U⁻¹ (x ⊗ ξ)`, viewed in `S`.
   It is linear, injective and hence nonzero (`V ≠ 0` since `ρ` is irreducible), has range in
   `P`, and
   `j₀ (ρ y x) = πc (ofPlace y) (j₀ x)` because `π_v(y) ⊗ 1` sends `x ⊗ ξ` to `π_v(y) x ⊗ ξ`.
   Transporting `ρ` along `j₀` to its range, a subspace of `S`, gives a carrier in `Type u`.

## Provenance and sources

This is derived content, formulated for this project: it isolates the local occurrence used
in the factorization of an irreducible cuspidal summand, with the Library's objects. The
argument above follows these sources.

- J. R. Getz and H. Hahn, *An introduction to automorphic representations*, Graduate Texts in
  Mathematics 300, Springer (2024), literature ID `getz-hahn-2024-automorphic-representations`:
  Theorem 3.10.2 (printed p. 97, PDF p. 113): if `G` is an affine algebraic group over a
  characteristic-zero local field `F`, then `G(F)` is of type I. Proposition 5.3.8 (printed
  p. 141, PDF p. 156): for `G` the `F`-points of a reductive group over a non-archimedean local
  field, a unitary representation `V` is irreducible if and only if its smooth vectors
  `V^sm` are. Theorem 5.3.9 (Harish-Chandra, Bernstein; same page): all irreducible unitary
  representations of such `G` are admissible, that is, `V^sm` is admissible. The errata of
  October 2026 (`getz-hahn-2024-errata-2026-10`) list no correction to these results.
- G. B. Folland, *A course in abstract harmonic analysis*, 2nd ed., CRC Press (2015),
  literature ID `folland-2015-abstract-harmonic-analysis-second`, Theorem 7.17 (printed p. 237,
  PDF p. 250): if `G_1` or `G_2` is of type I, every irreducible unitary representation of
  `G_1 × G_2` is equivalent to an outer tensor product `π_1 ⊗ π_2` of irreducible unitary
  representations.

Differences from the sources, all of which keep the content: one place `v` is split off; the
local representation is realized on algebraic (smooth) vectors and the map into `P` is only
linear; irreducibility is Mathlib's algebraic irreducibility; admissibility uses all open
subgroups.

The statement contains no proof.
