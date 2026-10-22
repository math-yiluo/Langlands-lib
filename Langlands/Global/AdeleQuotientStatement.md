# The additive adele quotient `𝔸_K / K`

Author: Worker 35. Statement contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1. Worker 2 delegated this
prerequisite of their automorphic-forms task `6c50b2fd`, for constant terms and
cuspidality.
The four `…Statement` declarations are proposition definitions; none supplies a
proof.

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
  `IsClosed (principalAdeles K : Set (Adeles K))`.
- `AdeleQuotientCompactStatement K` is `CompactSpace (AdeleQuotient K)`.
- `AdeleQuotientStatement` is the closing declaration. For every number field
  `K : Type u` it asserts the conjunction of the three statements above. Its only
  universe parameter is `u`.

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
  proof reduces to `ℚ` by the preceding Corollary (p.64) and is completed on
  p.65.
- §14, Corollaries 1 and 2, p.65: every adele is the sum of an element of `K` and
  an element of an explicit compact set `W`, and `V_k^+/k^+` has finite measure.
  They are not formalized here.

A. Weil, *Basic Number Theory*, 2nd edition (1973), Chapter IV:

- §1, p.59 and Definition 1, p.60 (PDF pp.76–77): `k_A` is a locally compact
  ring.
- §2, Theorem 2, p.64, with its proof on pp.64–65 (PDF pp.81–82): for every
  finite-dimensional `k`-vector space `E`, `E` is discrete in `E_A` and `E_A/E`
  is compact. The case `E = k` is the discreteness and compactness here.

Both authors treat all global fields. The Lean statements are for number fields
only, because Mathlib's `AdeleRing` is the adele ring of a number field.

## Derived content

Closedness of `K` in `𝔸_K` is derived: it is not stated in either source.
In a `T1` topological group a discrete subgroup is closed, so it follows
from discreteness once `𝔸_K` is known to be Hausdorff (Mathlib's instance
`AddSubgroup.isClosed_of_discreteTopology`). It is included because a closed
subgroup makes the quotient Hausdorff (Mathlib's instance
`QuotientAddGroup.instT3Space`). The normalized Haar probability measure on
`𝔸_K / K` that is planned next needs the quotient to be a compact Hausdorff
group.

## Intended use

Let `n = a + b` with `a, b ≥ 1`. The unipotent radical of the maximal block
parabolic of type `(a, b)` is the group of matrices `[[1, X], [0, 1]]` with `X` an
`a × b` matrix. Its quotient `N(K)\N(𝔸_K)` is the product of `a · b` copies of
`𝔸_K / K`. The constant term of an automorphic function along this parabolic is
its integral over that compact quotient against the normalized Haar probability
measure. The Haar measure and constant-term definitions, and the proofs of these
statements, are separate later units. Weil's Theorem 2 for
`E = Mat_{a×b}(K)` is the same product of copies of `𝔸_K / K`.

## Status

Mathlib (commit `5ed29652`) proves the local compactness of the infinite adele
ring and of each archimedean completion. It does not prove the local
compactness of the finite adele ring, the discreteness of the principal adeles,
or the compactness of `𝔸_K / K`. Mathlib's `AdeleRing.lean` defines only the
principal subgroup. These three facts are theorem obligations for a separate
proof task. Statements are checked against Library commit `196ceda9`.
