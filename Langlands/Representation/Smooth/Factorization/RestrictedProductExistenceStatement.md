# Existence of restricted tensor factorizations

`Langlands.FlathRestrictedProductExistenceStatement` states the existence
assertion of Flath's Theorem 2 for the actual restricted product of Hausdorff,
locally compact, totally disconnected groups. Its hypothesis retains
commutativity of the spherical Hecke algebra at all but finitely many indices.
Its output uses the published algebraic restricted tensor product and its
actual group action.

## Objects and quantifiers

The index type, the family of groups, and the original complex representation
carrier have independent universes `uI`, `uG`, and `uV`. At each index the
reference subgroup is compact and open. Each group carries its Borel measurable
space and a supplied regular left Haar measure. Mathlib's `IsHaarMeasure`
requires left invariance, finite mass on compact sets and positive mass on
nonempty open sets; `Measure.Regular` explicitly supplies the usual regularity
condition. In particular, zero measures are excluded. There is no countability,
sigma-compactness, unimodularity or normalization-to-mass-one hypothesis.

`SphericalHeckeCommutative μ H` is a proposition about actual functions.
For any two elements of `Hecke.HeckeAlgebra μ` whose underlying test functions
belong to `Hecke.TestFunction.biInvariant H H`, it requires `f * g = g * f`.
The carrier is the published space of locally constant compactly supported
complex functions. Its multiplication is the published convolution

`(f * g)(x) = ∫ y, f(y) g(y⁻¹ x) dμ(y)`.

This is an equality of test functions, hence pointwise equality, and not a
condition on arbitrarily supplied polynomial or algebra data. The helper can
be formed for any subgroup and measure; the theorem uses it only with the
compact open subgroups and regular Haar measures just specified.

The statement quantifies over an actual representation `π` of
`RestrictedTensor.RestrictedGroup G H`, with Mathlib's cofinite restricted-product
topology. It assumes `IsAdmissible π` and `π.IsIrreducible`. Admissibility
includes smoothness and finite-dimensional fixed spaces for every open
subgroup. This agrees with the source's compact-open convention: van Dantzig
provides a compact open subgroup inside any open subgroup, and the latter's
fixed space is a subspace of the former's. No topology or norm is imposed on
the representation carrier.

The conclusion supplies a family `W : ι → ModuleCat.{uV} ℂ` and actual local
representations `ρ i`, each admissible and irreducible. It then supplies one
finite exceptional set `E`, a nonzero reference vector at every index outside
`E`, and proofs that the reference subgroup fixes those vectors. Outside the
same `E`, the full subgroup-fixed space has dimension exactly one. Finally it
asserts the existence of a genuine intertwining linear equivalence between
`π` and `RestrictedTensor.productRepresentation H ρ E r hr`.

Bundled `ModuleCat` objects carry only the actual additive and scalar
structures; they do not assume irreducibility, admissibility or factorization.
Those assertions occur in the conclusion. The factors may be chosen in the
original carrier universe: after a factorization, fixing nonzero vectors in
the other factors embeds any one local factor into the original space.
Transporting its structure to its image supplies a carrier in `Type uV`.
The restricted tensor carrier itself can have universe `max uI uV`, and
`Representation.Equiv` permits these different carrier universes. This
universe choice does not impose a dimension or cardinality hypothesis on `π`.

The exceptional set in the conclusion can enlarge the finite set of
noncommutative spherical algebras; no equality of those two exceptional sets
is asserted. For a finite index type the cofinite hypothesis is automatic.
For an empty index type the conclusion is the empty tensor over the trivial
group, as in the source construction. The hypotheses are nonvacuous, for
example for trivial local groups with their positive counting measures.
Irreducibility excludes zero representations.

## Original source and reformulation

The original is D. Flath, *Decomposition of representations into tensor
products*, Proceedings of Symposia in Pure Mathematics 33, part 1 (1979),
pp.179–183. The source is registered as `flath-1979-tensor-products`.
The retained file is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The complete article was reread for this statement.

- Printed p.179, one-based PDF p.175: the Hecke algebra, normalized subgroup
  indicator, corner `e_H H(G) e_H`, and the fixed-space corollary.
- Printed pp.180–181, PDF pp.176–177: the algebraic restricted tensor
  construction and Example 2, including nonzero fixed reference vectors and
  one-dimensional fixed spaces almost everywhere.
- Printed p.181, PDF p.177: Theorem 2 and its proof state factorization under
  almost-everywhere commutativity, uniqueness of local equivalence classes,
  and one-dimensional reference fixed spaces almost everywhere.

Flath denotes the spherical algebra by the normalized-indicator corner.
The helper uses its concrete function description instead. For a compact
open subgroup, left and right convolution by `e_H = μ(H)⁻¹ 1_H` average over
the subgroup. Their simultaneous fixed functions are precisely the
bi-invariant test functions, so their image `e_H H(G) e_H` is that subspace.
The left averaging substitution uses left Haar invariance. In the right
averaging formula, translations by elements of the compact subgroup preserve
Haar measure because its modular character is trivial. Thus this
reformulation needs no global unimodularity. Its multiplication is exactly
the already published convolution; normalization cancels in the averaging
identities. Proving those intrinsic algebra identities belongs to the separate corner
construction task; they are not assumed as theorem fields here.

The same finite exceptional set can be chosen for fixed-space dimension and
reference vectors by enlarging the finite set in the source. Same-universe
factor carriers and the explicit `Nonempty` of an intertwiner are internal
formalization choices explained above. No stronger automorphic theorem is
used to formulate the target.

## Dependency and scope boundary

The pair imports the published `RestrictedTensor.Smooth` and
`Hecke.Convolution` constructions, together with Mathlib. The entire project
import closure below was compared byte for byte with Library commit
`f01c1864161b6d1cdc1d04b1f8d577dfd4e8400f`. Each row gives the module
path relative to `Langlands/`, followed by its Lean and Markdown SHA256.

| Module | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `HarmonicAnalysis/Basic` | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` | `770a9f6e068d76d72fb10ff91ee1a27b66696ebf0c52af23464fb4d0956ffdf6` |
| `Representation/Hecke/Convolution` | `7aed8c839a537413ca951a719f8bed7eeb51e7faa1693efcaeb630ee34e96832` | `f3a9ad1ad3bc612d966e78709cea8717bb8dceab05e290cb20ebb1a93a9a033f` |
| `Representation/Hecke/TestFunction` | `57db020a996e2486945c92dde4073fd13a5c94201b8184d441d51db417708749` | `5d615c6b041939d68fb4aaca47b09fbf365f06453e2d7e3015e67f96b17ea5a3` |
| `Representation/RestrictedTensor/Action` | `88248d0195c390eb37b7589b0ecd0e9e70cf951b07fb42a052fcd62c080e9602` | `9c1efc1205b1b64fcd7d65d235b04b8089fddd55eddb875749bbaecc34e4feea` |
| `Representation/RestrictedTensor/Basic` | `f486e17b27d35c0882bae1ac84d0aaddb280a2305746984b31705ada762aae27` | `a28f98b2ae59fb0c8a5fc0e19aab583c818bbf095506eb81a8694b49c72d373c` |
| `Representation/RestrictedTensor/Maps` | `dd20942a74c78afa7d4feb793175184e562d439ef9ffe24aef9fe4a9f2ccf4ef` | `6aa054eae3f5cd71f89b08969aa12f41cb39f9bd092ef1272c3765ad10af2ce7` |
| `Representation/RestrictedTensor/Smooth` | `6238ba286f6ab1512dcdacaf9d160632add27629b83690dacf5858f2374951c0` | `ca2ad7227b5c12dad39dece9f7f3fa87c65e76d85eeeadd436a96611d2d042c1` |
| `Representation/Smooth/Definitions` | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |

Compilation and declaration inspection use environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The complete proposition compiles
without diagnostics and returns `Prop`, with exactly the independent universe
parameters `uI`, `uG`, `uV`. Its dependency assumptions are the standard
`propext`, `Classical.choice`, and `Quot.sound`. Full declaration printing
confirms that the final equivalence has carrier universes `uV` and `max uI uV`.
These are development checks, not a proof of the proposition.

The source's uniqueness assertion is already the separate published
`Langlands.RestrictedTensorFactorUniquenessStatement`, in
`Representation/Smooth/Factorization/RestrictedTensorStatement`. Together
with the current existence target it gives the full conclusion of Theorem 2.
The present pair imports no theorem-statement group and assumes no theorem
truth. Mathematical proofs of factorization and uniqueness remain separate.
The archimedean `(g,K)` category of Theorem 3 and the Hilbert completion of
Theorem 4 are distinct targets. In particular this statement does not supply
archimedean automorphic local components, Satake data, or weak association.
