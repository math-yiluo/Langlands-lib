# Admissibility of irreducible product-Levi representations

Author: Worker 246.

This pair states one future proof target in `Langlands.CuspidalSupport`. It is
a proposition definition only. It neither proves the assertion nor assumes it
anywhere, and no Library result is claimed to imply it.

## Exact declaration

`IrreducibleLeviAdmissibilityTheorem.{uF,uV} F T` has outer binders
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
Its body installs exactly `T.topology` on `F.Carrier` and then asserts:

> for every `n : ℕ`, every `B : GeneralLinear.BlockShape n` and every
> `σ : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`, if `σ.IsIrreducible`
> then `σ.IsAdmissible`.

The definitions are reused by their published names:

- `B.Levi F.Carrier` (`Langlands.Group.GL.Blocks`) is the actual product
  `∀ i : Fin B.length, GeneralLinear (B.size i) F.Carrier` of the general
  linear groups of the blocks. It carries the product of the matrix-unit
  topologies induced by `T.topology`. This is the same instance that
  `T.generalLinearTopology` selects on each factor.
- `SmoothRep.{0,uF,uV} ℂ G` (`Langlands.Representation.Category.Basic`) is
  the full subcategory of Mathlib's `Rep ℂ G` whose objects satisfy
  `IsSmooth`. Every vector has an open stabilizer. The coefficient ring is
  the actual field `ℂ`. No topology is placed on the representation carrier.
- `σ.IsIrreducible` is Mathlib's `Representation.IsIrreducible` of the
  underlying action. It means the lattice of invariant subspaces is simple,
  so it includes that the carrier is nonzero. Finite dimension is not
  required.
- `σ.IsAdmissible` unfolds to `Langlands.IsAdmissible`
  (`Langlands.Representation.Smooth.Definitions`). It is smoothness together
  with `Module.Finite ℂ` of the fixed vectors of **every** open subgroup.
  Over the field `ℂ` this is finite dimension.

There is no further hypothesis. In particular the statement does not assume
quasicuspidality, supercuspidality, finite length, finite generation,
admissibility, finite dimension, a central character, a tensor factorization
along the blocks, or an embedding into an induced representation. It has no
proof-valued parameters and no data that carry the conclusion. The block
shape is arbitrary, including one-block and empty shapes. The rank is
arbitrary, including `n = 0`. The topological data `T` are arbitrary
supplied data.

## Universe accounting

- `uF` is the universe of the field carrier. The group `B.Levi F.Carrier`
  therefore lies in `Type uF`.
- The coefficient field `ℂ` lies in `Type 0`, which is the first universe
  argument of `SmoothRep`.
- `uV` is the carrier universe of `σ`. It is an independent universe
  parameter of the definition, and no relation between `uF` and `uV` is
  imposed.

Consumers that need the saturated carrier universe `max uF uV` use the
specialization `IrreducibleLeviAdmissibilityTheorem.{uF, max uF uV} F T`.
For example, parabolic induction from `B.Levi F.Carrier` with a `uV` carrier
has carriers in `Type (max uF uV)`. This specialization is well formed
because `uV` is a free universe parameter. A private check elaborated it, as
well as the specializations `{uF, uF}` and `{uF, 0}`.

## Relation to existing declarations

`IrreducibleQuasicuspidalLeviAdmissibilityTheorem.{uF,uV} F T B` in
`Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement`
is the special case with the additional hypothesis `IsLeviQuasicuspidal B
σ.representation`. It is proved in the Library as
`Langlands.CuspidalSupport.LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility`.
The present target drops that hypothesis, so the quasicuspidal theorem does
not prove it. The present target directly implies the quasicuspidal family;
a private check confirmed that implication.

`Langlands.CuspidalSupport.cuspidalEmbedding` gives admissibility for
irreducible smooth representations of `GeneralLinear n F.Carrier` itself. A
one-block shape has Levi `∀ i : Fin 1, GeneralLinear n F.Carrier`. That group
is isomorphic to `GL_n`, but it is not the same Lean type. Shapes with two or
more blocks are not covered by that result. An irreducible representation of
such a product need not be presented as a tensor product of representations
of the factors. The admissible-factorization results in the Library assume
admissibility, so they cannot supply this statement.

## Original source

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F), where F is a non-Archimedean local field*, Russian Mathematical
  Surveys 31:3 (1976), 1–68. Literature ID:
  `bernstein-zelevinsky-1976-representations-gln`. PDF SHA-256:
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  The PDF page numbers equal the printed page numbers.

The passages read directly for this pair on 2026-10-26 are listed below:

- **Theorem 3.25** (p.35, under "Admissibility of irreducible
  representations"): "Let `G = G_α` and let `(π, G, E) ∈ Alg G` be an
  irreducible representation. Then it is admissible." Its proof and
  Lemma 3.26 are on p.36.
- Conventions on pp.15–16. Representations are in complex vector spaces
  treated without topology. A `G`-module is irreducible if it is nonzero and
  has no submodules except `0` and itself (p.15). §2.1(a) calls a
  representation algebraic if every vector has an open stabilizer, and
  `Alg G` is the category of algebraic representations. §2.1(b) calls it
  admissible if it is algebraic and `E^N` is finite-dimensional for **every
  open subgroup** `N ⊂ G`.
- §3.1 (p.28): `F` is a locally compact non-discrete field with a
  non-Archimedean valuation, and `G_n = GL(n,F)`.
- §§3.3–3.4 (pp.29–30): a partition `α = (n_1, …, n_r)` of `n` divides
  `{1, …, n}` into consecutive segments, and `G_α = ∏ G_{n_i}`.
- §§3.12–3.13 (pp.32–33), Proposition 3.19 (p.34), and §3.20 with
  Theorem 3.21 (pp.34–35), read for the source proof outline below.

No erratum or correction for this source was found. The search covered the
Library's notes and wiki, the project literature index and the central
library listing, on 2026-10-26.

### Correspondence and scope

- BZ76's `Alg G` corresponds to `SmoothRep ℂ G`, since a stabilizer is a
  subgroup and is open exactly when it contains an open subgroup. Its
  irreducibility matches `σ.IsIrreducible`. Its admissibility, quantified
  over every open subgroup, matches `σ.IsAdmissible`.
- An ordered `BlockShape n` with positive block sizes corresponds to a
  partition of `{1, …, n}` into nonempty consecutive segments. The Levi
  `B.Levi F.Carrier` is the abstract product `∏ GL(n_i, F)` with the product
  topology, which is the source's `G_α` (§3.4). The block-diagonal embedding
  into `GL_n` is not part of this statement.
- The field is a finite extension of `ℚ_p` with arbitrary supplied
  `TopologicalData`. Such a field is a non-Archimedean local field, so it is
  a special case of the fields of §3.1. Positive-characteristic local fields
  are not covered by this Lean statement.
- The carrier universe `uV` is unrestricted. The source places no
  cardinality condition on `E`. The source proof does use that `G_α` is
  countable at infinity (§3.2), but this is a property of the group, not of
  the representation space.

### Rank-zero extension

The source concerns `G_n` with `n ≥ 1`. For `n = 0`, the conditions
`0 < B.size i` and `∑ i, B.size i = 0` force `B.length = 0`. Then
`B.Levi F.Carrier` is a product over `Fin 0`, a group with one element. A
nonzero vector of an irreducible complex representation of the trivial group
spans an invariant line, which must be the whole space. Hence the space is
one-dimensional and admissible. This elementary argument is derived boundary
content for the empty product. It is not quoted from the source, and this
pair does not formalize it.

## Source proof outline (not implemented)

The source proves Theorem 3.25 in this order:

1. By Proposition 3.19, an irreducible `π ∈ Alg G_α` embeds into
   `i_{α,β}(ρ)` for some `β ≤ α` and some irreducible quasi-cuspidal `ρ` of
   `G_β`. Here `G_β` is again a product of general linear groups. This is
   why the product-group form is the natural scope.
2. If `ρ` is admissible, §3.13(d) makes `i_{α,β}(ρ)` admissible. A
   subrepresentation of an admissible representation is admissible. So
   "we may assume that π is quasi-cuspidal".
3. For quasi-cuspidal `π`, Harish-Chandra's Theorem 3.21 shows that the
   restriction to `G°` is finite. Here finite means compactly supported
   matrix coefficients, not finite dimension. Lemma 3.26 splits that
   restriction into finitely many irreducible summands. §2.41 makes each
   summand admissible.

The Library already proves the quasicuspidal case (step 3) in its own form,
as cited above. A proof of the present target still needs step 1 for
arbitrary product Levis, together with the admissibility of normalized or
unnormalized induction from a product Levi to a product Levi and the
transfer along an injective intertwiner. The task context reports no
published arbitrary product-Levi embedding of this kind. These are
obligations for a separate proof task, not results of this pair.
