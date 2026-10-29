# Haar measure prerequisites for the Shalika argument

Authors: Worker 634 (proposition design), Worker 919.

`Langlands.Whittaker.BruhatHaarMeasureStatement.{uF}` is an unproved,
closed, Prop-valued statement. It collects the facts about actual Haar
measures on two kinds of p-adic unipotent groups that Shalika's orbital
integration and his exchange of the two unipotent factors need. It states
them as conclusions. This file proves nothing; a separate proof task
proves the statement.

## Quantifiers and objects

The statement quantifies over:

- every natural number `p` with `Fact p.Prime`;
- every `F : PadicField.{uF} p`, in an arbitrary universe `uF`;
- every natural number `n`, including `n = 0`;
- in its last clause, every permutation `w : Equiv.Perm (Fin (n + 1))`.

The rank is `n + 1`. For each of these, write

- `U = upperUnipotent (n + 1) F.Carrier`: the actual subgroup of
  `GeneralLinear (n + 1) F.Carrier` of upper triangular invertible matrices
  whose diagonal entries are all one;
- `P = permutationUnipotentPlus (n + 1) F.Carrier w`: Shalika's
  `U_w⁺ = U ∩ w⁻¹ U w`. The Library defines it as the elements `g` of `U`
  for which `perm(w) * g * perm(w)⁻¹` is also in `U`, where `perm(w)` is the
  published permutation matrix `permutation (n + 1) F.Carrier w`. The
  inclusion `P ≤ U` is `permutationUnipotentPlus_le_upperUnipotent`.

No other object is quantified. In particular no measure is fixed in
advance: every measure either is produced by an existence clause or
ranges over all Haar measures.

## Topology and measurable structure

`letI := F.canonicalNormedField` installs Mathlib's spectral norm on
`F.Carrier`, the unique extension of the p-adic norm of `Padic p`. Its
topology is the canonical p-adic topology. The published
`Langlands.PadicField.canonicalTopologicalData_normTopology` identifies it
with `F.canonicalTopologicalData.topology`. Matrices carry the entrywise
product topology. `GeneralLinear (n + 1) F.Carrier` is Mathlib's unit group
of the matrix ring, with Mathlib's units topology. `U` and `P` carry the
subspace topologies inherited from it.

`letI := borel U` and `letI := borel P` make the measurable structures
exactly the Borel σ-algebras of these topologies. No other σ-algebra is
used. The measures in the statement are therefore Borel measures on the
actual subgroups, not on their matrix entries.

## Exact clauses

For each `p`, `F` and `n` the statement asserts the conjunction of three
clauses.

1. **Existence on `U`.** Some measure `μ` on `U` satisfies
   `μ.IsHaarMeasure`.
2. **Every Haar measure on `U`.** For every measure `μ` on `U` with
   `μ.IsHaarMeasure`:
   - `SigmaFinite μ`;
   - `μ.IsMulRightInvariant`, that is, `Measure.map (· * g) μ = μ` for every
     `g ∈ U`;
   - `Measure.map (weylTransposeUnipotent n F.Carrier) μ = μ`.
3. **Every permutation fiber group.** For every permutation `w` of
   `Fin (n + 1)`:
   - some measure `ν` on `P` satisfies `ν.IsHaarMeasure`;
   - every measure `ν` on `P` with `ν.IsHaarMeasure` satisfies
     `SigmaFinite ν` and `ν.IsMulRightInvariant`.

`IsHaarMeasure` is Mathlib's class from
`Mathlib.MeasureTheory.Group.Measure`. It requires left invariance under
multiplication, finiteness on compact sets (`IsFiniteMeasureOnCompacts`)
and positivity on nonempty open sets (`IsOpenPosMeasure`). So every Haar
measure here is nonzero and finite on compact sets. The statement adds no
premise to this class: no regularity, no right invariance and no
countability.

The universal clauses apply to every Haar measure on the actual group, not
to a selected normalization. In clause 3 this is every Haar measure on the
actual fiber subgroup `P`, not on a substitute group. The existence
clauses keep the universal clauses from being vacuous.

`SigmaFinite` is deliberately stronger than the `SFinite` hypothesis of
the published `Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverage`
map, which also requires `IsFiniteMeasureOnCompacts`. Haar measures supply
the latter, and `SigmaFinite` implies `SFinite`.

### The transpose map

`weylTransposeUnipotent n F.Carrier` is the published homeomorphism of `U`
from `Langlands.Representation.Whittaker.Distribution`. Its underlying
matrix map is `weylTransposeHomeomorph`,

\[
\tau(g) = w_0\, g^{t}\, w_0, \qquad \tau(g)_{i,j} = g_{\bar j,\bar i},
\]

where `w_0` is the long Weyl matrix with anti-diagonal entries one and
`\bar i = i.rev` reverses an index. This is not the ordinary transpose,
which would send `U` to the lower unipotent group. `τ` preserves `U`,
reverses multiplication (`weylTransposeHomeomorph_mul`) and is an
involution (`weylTransposeUnipotent_involutive`). Being a homeomorphism,
it is Borel measurable, so `Measure.map` here is the genuine
pushforward. Transpose invariance is claimed only for `U`. The statement
does not claim that `P` is stable under `τ` for arbitrary `w`, and it
states no transpose property of measures on `P`.

### The case `n = 0`

In rank one, `U` and `P` (for the only permutation of `Fin 1`) are the
trivial group, and `τ` is the identity. The Haar measures are the positive
finite multiples of the Dirac mass. The statement keeps this case; it is
not excluded.

## Relation to the published Bruhat fiber integral

The published module `Langlands.Representation.Whittaker.BruhatFiberAverage`
defines the raw fiber integral `bruhatFiberAverage` for any Borel measure
on `P` that is finite on compact sets. Its invariance law
`bruhatFiberAverage_bruhatFiberAct` additionally needs right invariance.
Clause 3 supplies both properties, and `SigmaFinite`, for every Haar
measure on `P`. Clause 2 supplies the corresponding properties of every
Haar measure on `U`, together with the transpose invariance used to
exchange the two unipotent factors. This statement proves neither the
descent of the orbit integral to the Bruhat cell nor any invariance of
distributions.

## Provenance

This is an internally derived measure interface. It is not a literal
theorem of the source; it isolates measure facts that the source uses
without stating them.

The source is J. A. Shalika, *The multiplicity one theorem for GLn*,
Annals of Mathematics (2) **100** (1974), 171–193, registered as
`shalika-1974-multiplicity-one`, SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`, file
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`.
Printed page numbers below are the journal's; PDF page numbers are
one-based. Worker 634 read printed pp.173–179 and visually checked
pp.176–178. Worker 919 read the extracted text of printed pp.173–178 and
visually checked printed p.174. No
errata note for this source was found in the project literature or public
notes.

- Printed p.174 (PDF page 5) defines `U_w⁺ = U ∩ w⁻¹ U w` and the
  anti-automorphism `θ(x) = w_0 h_0 x^t h_0⁻¹ w_0⁻¹`, with
  `θ(U) = U` (property (1.3)). The printed formula sets the transposed
  variable as `ᵗu` instead of `ᵗx`; it is read here as the transpose of
  `x`. There `h_0 ∈ H` is any diagonal element with `χ = χ_0^{h_0}`, where
  `χ_0(u) = χ(w_0 ᵗu w_0⁻¹)`. For the standard character, with all
  superdiagonal coefficients one, `χ_0 = χ`, so one may take `h_0 = 1`.
  Taking `w_0` to be the anti-diagonal matrix, `θ` restricted to `U` is
  then the map `τ` above.
- Printed p.176 (PDF page 7), formula (1.11), writes the cell function as
  the orbit integral `∫_{U_w⁺} α(u * m) du⁺`. Printed p.177 (PDF page 8)
  explains that `du⁺` is a fixed Haar measure on `U_w⁺`. Clause 3 states
  the existence, σ-finiteness and right invariance of such measures used
  to form this integral and to change variables in it.
- Printed p.178 (PDF page 9), in the proof of Proposition 1.8, defines
  `α^θ(u₁, h, u₂) = α(θ(u₂), w⁻¹θ(wh), θ(u₁))`, which exchanges the two
  unipotent factors through `θ`. Transporting the Haar measure of `U`
  through this exchange is the use motivating the transpose invariance in
  clause 2.

The statement is not Proposition 1.8 and not formula (1.11). The full
quantification over every prime, every `PadicField` universe, every rank
including `n = 0`, every permutation and every Haar measure is an internal
choice that makes the facts reusable without normalization.

## Intended proof routes

The following routes are intended for the proof task only. Nothing here
proves them.

- **Compact-open subgroups.** The published
  `Langlands.RankinSelberg.unipotent_exists_compact_open` places every
  element of `U` in a compact open subgroup. Pulling such a subgroup back
  along the closed inclusion `P ≤ U` (closedness is
  `isClosed_permutationUnipotentPlus`) gives compact open subgroups of `P`.
  Haar uniqueness then gives `Measure.map (· * g) μ = c • μ`, and comparing
  the finite nonzero masses of a compact open subgroup containing `g`
  forces `c = 1`. The published module also proves right invariance of its
  normalized `Langlands.RankinSelberg.unipotentHaar`
  (`unipotentHaar_isMulRightInvariant`); its generic helper is private, so
  a new helper may repeat the short argument.
- **Haar uniqueness.** `Langlands.PadicField.matrixGroupCountability`, in
  the published module `Langlands.Group.GL.CountabilityProof`, gives second
  countability of the actual p-adic general linear group for the topology
  of any `F.TopologicalData`. For `F.canonicalTopologicalData` that
  topology is the normed-field topology used here, by
  `canonicalTopologicalData_normTopology`. Subspaces inherit second
  countability. `P` and `U` are closed in the locally compact general
  linear group, hence locally compact. In a second countable locally
  compact group, Mathlib's `isMulLeftInvariant_eq_smul` applies to every
  Haar measure without a regularity premise. Sigma compactness with
  finiteness on compact sets gives `SigmaFinite`.
- **Existence.** A Haar measure normalized on a compact open subgroup
  exists by Mathlib; for `U` the published `unipotentHaar` is another
  choice.
- **Transpose invariance.** `τ` reverses multiplication, so it carries a
  left Haar measure on `U` to a right Haar measure. By right invariance
  this is again a Haar measure, hence a positive multiple `c • μ`. As `τ`
  is an involution, `c² = 1`, so `c = 1`. Alternatively `τ` preserves the
  integral compact open subgroup, which allows direct mass cancellation.

## Checks

The Lean file reproduces the proposition fixed in the task contract,
originally checked privately by Worker 634 in namespace
`Langlands.Whittaker.Design`, in the production namespace
`Langlands.Whittaker`. With environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` it compiles without errors or
warnings. Inspection of the declaration reports a definition with
`statement_returns_prop: true` and the single universe parameter `uF`. The
file adds no axiom, proof hole or premise and changes no imported file.
