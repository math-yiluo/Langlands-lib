# The additive adele quotient `𝔸_K / K`

Author: Worker 35. Statement contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1. Worker 2 delegated this
prerequisite of their automorphic-forms task `6c50b2fd`, for constant terms and
cuspidality. Status and proof-route documentation corrected by Worker 232 in
task `0c739e3f-8d26-40af-8ddb-bfe6c13dacdf`, revision 1; the Lean file is
unchanged.

This module contains only definitions: the three objects below and four
proposition definitions `…Statement`. It proves none of the statements. Their
proofs are separate published modules, listed under
[Proofs in other modules](#proofs-in-other-modules).

## Objects

`K : Type u` is a number field. `Adeles K` is the published abbreviation of
Mathlib's `NumberField.AdeleRing (𝓞 K) K`. It is the product of the infinite
adele ring and the finite adele ring, with the product topology:

- The infinite adele ring is the finite product of the archimedean completions
  `v.Completion`, with the product topology.
- The finite adele ring is the restricted product of the adic completions
  `v.adicCompletion K` over the nonzero primes `v` of `𝓞 K`, restricted with
  respect to the completed integer rings `v.adicCompletionIntegers K`. It carries
  Mathlib's restricted-product topology.

This is the topology of Cassels's restricted topological product of the `k_v`
with respect to the `𝔬_v` (§13, Definition, p.62; §14, p.63). It is also Weil's
topology, in which each `k_A(P) = ∏_{v ∈ P} k_v × ∏_{v ∉ P} r_v` is an open
subring (IV §1, p.59 and Definition 1, p.60).

- `principalAdeles K` is Mathlib's `AdeleRing.principalSubgroup (𝓞 K) K`, the
  additive subgroup of `𝔸_K` that is the range of the diagonal embedding
  `algebraMap K (Adeles K)`. This embedding is the published
  `Langlands.Global.diagonal K`, and every component of the image of `x` is `x`.
  These are Cassels's principal adeles (§14, p.63).
- `AdeleQuotient K` is the additive quotient group
  `Adeles K ⧸ principalAdeles K` with Mathlib's quotient topology, which is
  Cassels's `V_k^+ / k^+` and Weil's `k_A / k`.
- `adeleQuotientMap K` is the quotient map, as a continuous additive
  homomorphism `Adeles K →ₜ+ AdeleQuotient K`.

## The statements

- `AdelesLocallyCompactStatement K` is `LocallyCompactSpace (Adeles K)`.
- `PrincipalAdelesDiscreteStatement K` is the conjunction of
  `DiscreteTopology (principalAdeles K)`, for the subspace topology, and
  `IsClosed (principalAdeles K : Set (Adeles K))`. Both discreteness and
  closedness are asserted.
- `AdeleQuotientCompactStatement K` is `CompactSpace (AdeleQuotient K)`.
- `AdeleQuotientStatement` is the closing declaration. For every number field
  `K : Type u` it asserts the conjunction of the three statements above. Its only
  universe parameter is `u`, which is arbitrary.

## Original sources

J. W. S. Cassels, *Global fields*, Chapter II of Cassels–Fröhlich (eds.),
*Algebraic Number Theory* (1967). In the retained scan, printed pp.62–63 are PDF
page 40 and pp.64–65 are PDF page 41. These pages were read visually.

- §13, p.63, second Lemma: a restricted product of locally compact spaces with
  respect to compact open subsets is locally compact.
- §14, p.63: "`V_k` is locally compact because the `k_v` are locally compact and
  the `𝔬_v` are compact (§7)." This is `AdelesLocallyCompactStatement`.
- §14, Theorem, p.64: "`k` is discrete in `V_k` and `V_k^+/k^+` is compact in the
  quotient topology." The two halves are the discreteness conjunct of
  `PrincipalAdelesDiscreteStatement` and `AdeleQuotientCompactStatement`. The
  proof reduces to `ℚ` or `F(t)` by the preceding Corollary (p.64) and is given
  for `ℚ`, completed on p.65. For `ℚ`, the neighbourhood of `0` defined by `|α_∞|_∞ < 1` and
  `|α_p|_p ≤ 1` for all `p` contains no other rational number, and every adele is
  a rational number plus an element of the compact set `W` defined by
  `|α_∞|_∞ ≤ 1/2` and `|α_p|_p ≤ 1` for all `p` (14.7).
- §14, p.65, after the proof: `V_k^+` has a Haar measure, which is the product of
  the Haar measures on the `k_v` in the sense of §13.
- §14, Corollaries 1 and 2, p.65. Corollary 1: there is a set `W ⊂ V_k`
  defined by inequalities `|ξ_v|_v ≤ δ_v`, with `δ_v = 1` for almost all `v`,
  such that every adele is the sum of an element of `W` and an element of `k`.
  Corollary 2: `V_k^+/k^+` has finite measure for the quotient measure induced by
  the Haar measure on `V_k^+`.

A. Weil, *Basic Number Theory*, 2nd edition (1973), Chapter IV:

- §1, p.59 and Definition 1, p.60 (PDF pp.76–77): `k_A` is a locally compact
  ring.
- §2, Theorem 2, p.64, with its proof on pp.64–65 (PDF pp.81–82): for every
  finite-dimensional `k`-vector space `E`, `E` is discrete in `E_A` and `E_A/E`
  is compact. The case `E = k` is the discreteness and compactness here. The
  proof reduces to `k = ℚ` and `k = 𝔽_p(T)` and to `E = k`. For `ℚ`, Lemma 2
  gives `ℚ_A = ℚ + A_∞` with `A_∞ = ℝ × ∏_p ℤ_p` open and `ℚ ∩ A_∞ = ℤ`, and
  then `ℚ_A = ℚ + C` with `C = [-1/2, 1/2] × ∏_p ℤ_p` compact.

Both authors treat all global fields. The Lean statements are for number fields
only, because Mathlib's `AdeleRing` is the adele ring of a number field.

## Derived content

Closedness of `K` in `𝔸_K` is derived: it is not stated in either source.
In a `T1` topological group a discrete subgroup is closed, so it follows
from discreteness once `𝔸_K` is known to be Hausdorff (Mathlib's instance
`AddSubgroup.isClosed_of_discreteTopology`). It is stated because a closed
subgroup makes the quotient Hausdorff (Mathlib's instance
`QuotientAddGroup.instT3Space`). Together with compactness, `𝔸_K / K` is then a
compact Hausdorff group.

The normalized Haar measures that the Library actually constructs do not use
this separation property. They are described under
[Haar measures and constant terms](#haar-measures-and-constant-terms).

## Proofs in other modules

The following separately published modules prove these statements for every
`K : Type u` with `[Field K] [NumberField K]`, with no further hypotheses. They
import this module, directly or transitively. This module does not import them.

| Statement | Theorem | Module |
| --- | --- | --- |
| `AdelesLocallyCompactStatement K` | `Langlands.Global.adelesLocallyCompact K` | [AdelesLocallyCompactProof](AdelesLocallyCompactProof.md) |
| `PrincipalAdelesDiscreteStatement K` | `Langlands.Global.principalAdelesDiscrete K` | [PrincipalAdelesDiscreteProof](PrincipalAdelesDiscreteProof.md) |
| `AdeleQuotientCompactStatement K` | `Langlands.Global.adeleQuotientCompact K` | [AdeleQuotientCompactProof](AdeleQuotientCompactProof.md) |
| `AdeleQuotientStatement.{u}` | `Langlands.Global.adeleQuotient` | [AdeleQuotientProof](AdeleQuotientProof.md) |

The implemented proofs argue directly over `K`. They do not reduce to `ℚ` as
Cassels and Weil do.

- **Local compactness.** Each `v.adicCompletionIntegers K` is compact, as a
  complete discrete valuation ring with finite residue field, and open. Mathlib's
  local compactness instance for restricted products with respect to compact
  open subgroups then applies to the finite adele ring. The product with the
  infinite adele ring, which Mathlib proves locally compact, is locally compact.
  This is the content of Cassels's §13 Lemma for the adele ring; the Mathlib
  instance builds compact neighbourhoods by translating the compact open
  subgroups.
- **Discreteness and closedness.** The open set of adeles with every
  archimedean component of norm `< 1` and every finite component integral meets
  `K` only in `0`: such an element of `K` is an algebraic integer, and a nonzero
  algebraic integer has absolute value at least `1` at some infinite place. This is
  Cassels's neighbourhood for `ℚ`, taken over `K`. Closedness then follows from
  discreteness and the Hausdorff property of `𝔸_K`, as in
  [Derived content](#derived-content); both conjuncts are proved.
- **Compactness.** The proof shows that every adele is an element of `K` plus an
  element of the compact set
  `archimedeanFundamentalSet K ×ˢ integralFiniteAdeles K`. At the finite places
  it clears denominators and uses approximation and the Chinese remainder theorem
  in `𝓞 K`. At the infinite places it uses a closed fundamental parallelepiped
  of Mathlib's lattice of algebraic integers in the mixed space. The image of
  this compact set under the continuous quotient map is the whole quotient.
- **Aggregate.** `adeleQuotient` forms the conjunction of the three component
  theorems, in the order of `AdeleQuotientStatement`.

The compactness module also proves `Langlands.Global.compactSpace_adeleQuotient
K : CompactSpace (AdeleQuotient K)`. It is not a global instance. A module that
needs compactness of the quotient can import
`Langlands.Global.AdeleQuotientCompactProof` and install it locally with
`haveI := Langlands.Global.compactSpace_adeleQuotient K`.

### Source content not formalized

- Cassels's Corollary 1 is not stated in this module or in the proof modules
  above. The proof of `adeleQuotientCompact` establishes `𝔸_K = K + C` for its
  compact set `C` without exporting this decomposition as a theorem. The
  archimedean factor of `C` is a parallelepiped, not a set defined by
  inequalities `|ξ_v|_v ≤ δ_v`.
- Cassels's Corollary 2, the Haar measure on `𝔸_K` and its product
  description, and the quotient measure induced from it, are not formalized in
  this module, in the proof modules above, or in `ConstantTerm`.
- Weil's theorem for a general finite-dimensional vector space `E`, and both
  sources' function-field case, are outside these statements and their proofs.

## Haar measures and constant terms

Let `n = a + b` with `a, b ≥ 1`. The unipotent radical of the maximal block
parabolic of type `(a, b)` is the group of matrices `[[1, X], [0, 1]]` with `X` an
`a × b` matrix. Its quotient `N(K)\N(𝔸_K)` is the product of `a · b` copies of
`𝔸_K / K`. Its compactness is the case `E = Mat_{a×b}(K)` of Weil's Theorem 2.
The constant term along this parabolic of a continuous function on `GL_n(𝔸_K)`
that is left invariant under `GL_n(K)` is its integral over that compact
quotient against the normalized Haar probability measure.

These constructions are published in
[`Langlands.Automorphic.ConstantTerm`](../Automorphic/ConstantTerm.md), which
imports this statement module and not the proof modules. Its
`adeleQuotientHaar K` and `matrixQuotientHaar K a b` are Mathlib's
`Measure.addHaarMeasure ⊤` on `AdeleQuotient K` and on
`Matrix (Fin a) (Fin b) (AdeleQuotient K)`, for the Borel σ-algebra, with total
mass `1`. Compactness of the matrix space comes from that of `𝔸_K / K` through
the finite-product instance `matrixAdeleQuotientCompactSpace`. Its constant terms
are integrals against `matrixQuotientHaar`, and cuspidality is the vanishing of
these constant terms. The Haar measures, constant terms and cuspidality take the
instance parameter `[CompactSpace (AdeleQuotient K)]` and no other topological
hypothesis. No Hausdorff property of the quotient and no closedness of `K` in
`𝔸_K` is assumed. Mathlib's `Measure.addHaarMeasure` needs only a topological
additive group with its Borel σ-algebra and a compact set with nonempty
interior, here the whole compact space `⊤`. It assumes no separation axiom.
The identification of `N(K)\N(𝔸_K)` with `Mat_{a×b}(𝔸_K / K)` explains these
definitions; it is not formalized as a group isomorphism.

## Status

This module states the three properties and their conjunction; it does not prove
them.

Pinned Mathlib (commit `5ed29652`) proves the local compactness of the infinite
adele ring (`NumberField.InfiniteAdeleRing.locallyCompactSpace`) and of each
archimedean completion (`NumberField.InfinitePlace.Completion.locallyCompactSpace`).
It also has local compactness instances for general restricted products. It does
not prove the local compactness of the finite adele ring or of `𝔸_K`, the
discreteness or closedness of the principal adeles, or the compactness of
`𝔸_K / K`. For the additive quotient, Mathlib's `AdeleRing.lean` defines only the
principal subgroup.

The Library proves all three properties, and their conjunction
`AdeleQuotientStatement`, in the separately published modules listed under
[Proofs in other modules](#proofs-in-other-modules). The source content listed
there under *Source content not formalized* is not covered by these proofs.
These results are prerequisites for constant terms and cuspidality. They do not
establish any local or global Langlands correspondence, global reciprocity, or
the existence of automorphic representations.

The statements were originally checked against Library commit `196ceda9`. This
documentation was rechecked against Library commit `40a7d025`.
