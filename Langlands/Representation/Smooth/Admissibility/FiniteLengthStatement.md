# Admissibility of finite-length smooth GL and product-Levi representations

This module declares three proposition definitions and no theorems. Nothing
here proves them; a proof is a separate later task.

Throughout, `F : PadicField.{uF} p` is an arbitrary finite extension of `ℚ_p`
and `T : F.TopologicalData` is an arbitrary supplied local-field realization.
The only topology used is `T.topology` on `F.Carrier`. It is not specialized to
`canonicalTopologicalData`.

## The declarations

- `Langlands.GLFiniteLengthAdmissibilityStatement.{uF, uV} F T` says: for every
  `n : ℕ` and every `A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)`,
  `A.HasFiniteLength → A.IsAdmissible`.
- `Langlands.LeviFiniteLengthAdmissibilityStatement.{uF, uV} F T` says: for every
  `n : ℕ`, every `B : GeneralLinear.BlockShape n` and every
  `A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)`,
  `A.HasFiniteLength → A.IsAdmissible`.
- `Langlands.FiniteLengthAdmissibilityStatement.{uF, uV} F T` is the conjunction
  of the two clauses at the same `F`, `T`, `uF` and `uV`. It is the intended
  exact target of the later proof. Inspection reports its level parameters as
  `[uF, uV]` and its type as `Prop`.

The suggested names were unused in the Library and are adopted unchanged.

## Meaning of the predicates

All predicates are existing Library definitions, reused by name.

- `SmoothRep.{0, uF, uV} ℂ G` is an actual complex representation of `G` on a
  module in `Type uV` in which every vector has an open stabilizer. No topology
  or finite dimension is imposed on the module.
- `SmoothRep.HasFiniteLength A` is Mathlib's `IsFiniteLength ℂ[G]` for the
  module `A.representation.asModule` over the actual group algebra. This is
  finite composition length by `G`-stable subspaces, not finite dimension.
  The zero representation has finite length.
- `SmoothRep.IsAdmissible A` is `Langlands.IsAdmissible A.representation`:
  smoothness, and finite generation of the fixed vectors of every open
  subgroup. Over `ℂ` this is finite dimension of every such space.

The group `GeneralLinear n F.Carrier` is Mathlib's `GL (Fin n) F.Carrier` with
the units-of-matrices topology induced by `T.topology`. This topology agrees
by definition with `T.generalLinearTopology n`. `B.Levi F.Carrier` is the
product over the blocks of `GeneralLinear (B.size i) F.Carrier`, with the
product topology. The predicates need only these topologies. Hence no
`IsTopologicalGroup` instance appears in the statement. A proof may install
`T.generalLinearTopologicalGroup` itself.

## Scope

- Every rank is included, including `n = 0`. Every block shape is included,
  including the empty shape. The empty shape is the only shape of rank `0`,
  because block sizes are positive.
- Zero representations are included.
- No positive rank, irreducibility, admissibility, finite dimension,
  cuspidality, central character or chosen tensor decomposition is assumed.
  No proof-valued hypothesis or theorem-bearing structure stands in for the
  bridge.
- Only admissibility is concluded. Finite generation, also part of the source
  theorem, is not asserted.

## Universe accounting

The field universe `uF` and the carrier universe `uV` are independent. The
coefficient ring `ℂ` lies in universe `0`.

The two Grothendieck groups in `Langlands.Representation.Smooth.FiniteLengthGrothendieck`
use the saturated carrier universe `max uF uV`. The module contains three
compilation-checked `example`s about this.

1. Under `letI := T.topology`, the types
   `GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier` and
   `B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier` are equal by `rfl` to
   `SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ` of
   `GeneralLinear n F.Carrier` and of `B.Levi F.Carrier`, respectively.
2. Given `FiniteLengthAdmissibilityStatement.{uF, max uF uV} F T`, every object
   of `SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ` over either group is
   admissible.
3. Given the same hypothesis, every input `(A, hA)` of
   `GeneralLinear.finiteLengthClass` and of `BlockShape.finiteLengthClass` is
   admissible. The class of `(A, hA)` is `ofRepresentation A hA` by `rfl`.

So the substitution `uV := max uF uV` gives exactly the saturated carrier
types of those groups.

## Sources

The statement has derived provenance. The positive-rank cases are a
specialization of a published theorem. The rank-zero and empty-product cases
are an elementary extension.

**Bernstein and Zelevinsky**, *Representations of the group GL(n,F) where F is
a non-archimedean local field* (survey), 1976. Literature ID
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Printed page numbers:

- Definition 2.1(b), page 15: a representation is admissible if it is
  algebraic (smooth) and `E^N` is finite-dimensional for every open subgroup `N`.
- Section 2.8, pages 16-17: a module has finite length if the lengths of its
  chains of submodules are bounded.
- Definition 3.4, page 29: `G_α = ∏ G_{n_i}` for a partition
  `α = (n_1, …, n_r)` of `n` into consecutive nonempty segments.
- Theorem 3.25, page 35, with proof on pages 36-37: for `G = G_α`, every
  irreducible algebraic representation is admissible.
- Theorem 4.1, pages 37-38: for `G = G_α`, a `G`-module `E` has finite length
  if and only if it is admissible and finitely generated. The text states
  "It follows from 3.25 that (1) ⇒ (2)".

**Casselman**, *Introduction to admissible representations of p-adic groups*,
Chapter II, *Smooth representations*, revision June 16, 2019. Literature ID
`casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
PDF page numbers:

- Section 1, page 2: smooth and admissible representations, with
  admissibility tested on every open subgroup.
- Proposition II.1.3, page 4: in a short exact sequence `0 → U → V → W → 0`
  with `V` smooth, `U` and `W` are smooth. Fixed vectors of every compact open
  subgroup form an exact sequence.
- Corollary II.1.4, page 4: if `V` is smooth, it is admissible if and only if
  `U` and `W` are admissible.

No errata for either source were found in the project literature index, the
central-library listing or the public notes.

## Correspondence with the sources

- **Groups.** The partitions of Definition 3.4 have positive ordered segment
  lengths, as in `BlockShape n`. A one-block shape gives `GL_n`. Bernstein and
  Zelevinsky embed `G_α` in `GL_n` as block-diagonal matrices. The Library's
  `B.Levi` is the abstract product with the product topology. Over a
  topological ring, such as `F.Carrier` with `T.topology`, the published
  `BlockShape.leviEquivContinuous` identifies it with the block-diagonal
  subgroup as topological groups. The field here is a finite extension of
  `ℚ_p`, which is a special case of the sources' non-archimedean local field.
- **Finite length.** Bernstein and Zelevinsky treat a `G`-module as a module
  over the group. Its submodules are its `G`-stable subspaces, so finite length
  in the sense of section 2.8 is finite length over `ℂ[G]`. This is Mathlib's
  `IsFiniteLength`.
- **Admissibility.** Definition 2.1(b) and Casselman's page 2 both test every
  open subgroup. The Library's `IsAdmissible` does the same.

## Derivation, for explanation only

The statement is presented as a consequence of irreducible admissibility and
admissibility in short exact sequences. A later proof may follow this route
or another.

1. **Induction on finite length.** Mathlib's `IsFiniteLength` is generated in
   two ways: a subsingleton module, or a module `M` with a submodule `N` such
   that `N` has finite length and `M ⧸ N` is simple. In the second case, `N` is
   a `G`-stable subspace of `A`, hence a smooth subrepresentation. `M ⧸ N` is
   an irreducible smooth representation.
2. **The zero case.** For a zero module, every space of fixed vectors is zero
   and smoothness is trivial.
3. **The simple quotient.** The irreducible quotient is admissible by
   Theorem 3.25. Here the group is `G_α`, or `GL_n` with `n ≥ 1`.
4. **The extension.** The subrepresentation is admissible by the induction
   hypothesis. The middle term `A` is smooth. Corollary II.1.4 then gives
   admissibility of `A`.

This is the direction (1) ⇒ (2) of Theorem 4.1, restricted to admissibility.

**Rank zero and the empty product.** These cases are not in Bernstein and
Zelevinsky, whose groups have positive rank. `GL_0(F)` consists of the units
of `0 × 0` matrices and is trivial. The empty product Levi is also trivial.
Over a trivial group, `ℂ[G]` is `ℂ`, so finite length means finite dimension.
The only open subgroup is the whole group, whose fixed vectors form the whole
space. So finite length implies admissibility here by elementary reasoning.
Finite length of the zero representation is likewise elementary.

**Library inputs for a later proof.** These are not hypotheses of this
statement.

- `Langlands.CuspidalSupport.cuspidalEmbedding` concludes admissibility of
  every irreducible smooth representation of `GL_n`, for every `n` including
  `0`, every supplied `F`, `T` and independent carrier universes.
- `Langlands.AdmissibleShortExactStatement` states the short-exact-sequence
  admissibility of Corollary II.1.4 under explicit topological-group and
  compact-open cofinality hypotheses. It is a statement; its proof is
  separate.
- Admissibility of an arbitrary irreducible representation of a product Levi
  is not yet stated in the Library. It must be justified independently. The
  restriction of an irreducible `GL_n` representation to a Levi need not be
  irreducible, and a block tensor factorization may not be assumed.

## Dependencies and checking

Project imports:

- `Langlands.LocalField.Definitions` provides `PadicField` and `TopologicalData`.
- `Langlands.Representation.Smooth.FiniteLengthGrothendieck` provides
  `SmoothRep`, `HasFiniteLength`, `IsAdmissible`, `BlockShape` and `Levi`, and
  the two saturated Grothendieck groups used in the examples.

The module was compiled with `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Inspection of `Langlands.FiniteLengthAdmissibilityStatement` reported
`statement_returns_prop: true`. No existing Library pair is changed. Worker 237
wrote this statement and its explanation.
