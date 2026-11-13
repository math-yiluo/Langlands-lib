# Galois-stable even-path pattern data for pairing-compatible pinnings

Authors: Worker 5375 and Worker 90.

This module proves the Library statement
`Langlands.GroupScheme.EvenChainGaloisDataStatement`. That statement is a
derived finite-Galois, rational-point formulation of the rationality of
Steinberg's modified cross-section products. The sources are Robert Steinberg,
*Regular elements of semi-simple algebraic groups* (1965), 9.3, 9.4, the
notation before 9.11, 9.11 and the proof of 9.7 e); see *Sources and
provenance* below. The closing theorem is
`Langlands.GroupScheme.evenChainGaloisData`.

## Statement proved

Let `k, K : Type u` be fields with `[Algebra k K]`, `[FiniteDimensional k K]`
and `[IsGalois k K]`. Let `G` be an affine group scheme over `Spec k`, and let
`D : PairingCompatiblePinningData k K G`. Then there are

- a finite type `J` with `Fintype J`,
- even-path data `C : D.pinning.EvenChainData J`,
- natural numbers `r, q`, an enumeration `o : Fin r ≃ J` of the paths and an
  enumeration `e : Fin q ≃ C.Rest` of the unmerged simple roots,

such that `e` is middle-out for `C` (`C.IsMiddleOut e`). In addition, for every
`σ ∈ Aut_k(K)`, the Galois conjugate `GaloisPointComparison.rationalConjugate k K G σ g`
of a pattern product `g ∈ C.patternSet D.rootMaps
(SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps) o e` lies in the same
set.

## Declarations

- `PairingCompatiblePinningData.nonempty_mergedGaloisData`: for
  `[FiniteDimensional k K]`, the type `D.MergedGaloisData` (from
  `EvenChainGaloisAssembly`) is nonempty. Elements of this type are merged-root data at
  the pairs `D.Pairs`, with merged roots `c.1` and `partner D.action c.1`, both
  unipotent coordinates `1`, merged representative in `U(α)(K) ⊔ U(-α)(K)`,
  and root coordinate, representative and coroot points transported exactly
  by the Galois action.
- `evenChainGaloisData : EvenChainGaloisDataStatement.{u}`.

## Implemented proof

`nonempty_mergedGaloisData` applies Worker 90's
`GaloisCompatiblePinningData.exists_mergedRootGaloisData` (module
`MergedRootGaloisData`) to the underlying `GaloisCompatiblePinningData`. The
index set is `J := D.Pairs` with its action `pairAction D.isPairingCompatible`.
The arguments are `a c := c.1` and `b c := partner D.action c.1`.

- The roots `a c` and `b c` are distinct by `IsPaired.partner_ne`.
- Both pairings are `-1` by `IsPaired.pairing_partner D.isPairingCompatible`.
- The orientation hypothesis (the action on pairs keeps or swaps the two roots)
  is `D.smul_orientation`.

The five conclusions of that theorem fill the fields of `D.MergedGaloisData`
one to one. The coroot clause there has the unit `Units.map σ.toMonoidHom t`, and
the structure field has `Units.map (σ : K →* K) t`. These agree definitionally, and
the field is filled without conversion.

`evenChainGaloisData` introduces `k, K, G` and `D`. The statement supplies an
`IsAffineHom` instance for the base change, and the helper modules declare their
own local instance. `IsAffineHom` is a proposition, so the two instances agree by
proof irrelevance. The theorem then applies
`MergedGaloisData.exists_evenChainGaloisData` (module `EvenChainGaloisAssembly`)
to a chosen element of `D.MergedGaloisData`. That theorem's conclusion is
exactly the statement's conclusion for `D`. `IsGalois k K` is not used, so the
proof needs only `FiniteDimensional k K`.

## Supporting modules

The proof uses the following helper modules, each documented in its own
Markdown file:

- `Langlands.LinearAlgebra.RootDatumPathUniqueness`: two path-component
  enumerations that share a vertex are equal or reversed.
- `Langlands.LinearAlgebra.RootDatumPairedPaths`: paired simple roots, their
  partners, the index type of pairs with its Galois action, and the even
  paths through the pairs.
- `Langlands.Algebra.SortedOrbitBlocks`: Galois orbit blocks of a finite set,
  sorted by an invariant key.
- `Langlands.GroupScheme.Rational.EvenChainBlockCommutation`: blocks of distinct
  paths commute.
- `Langlands.GroupScheme.Rational.AdjacentSimpleRootCommutator` (Worker 90):
  reordering `x_a(1) x_b(1)` for adjacent simple roots `a, b` at the cost of a
  factor in `U_{a+b}`.
- `Langlands.GroupScheme.Rational.MergedRootGaloisData` (Worker 90): the
  Galois-compatible merged-root data, built with a Hilbert 90 twist.
- `Langlands.GroupScheme.Rational.EvenChainGaloisAssembly`: the even-path data,
  the middle-out ordering of the unmerged roots, and the Galois stability of the
  pattern set, given merged-root data.

## Sources and provenance

Robert Steinberg, *Regular elements of semi-simple algebraic groups*,
Publ. Math. IHÉS 25 (1965), 49–80, source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
PDF page numbers are printed page numbers minus 47. The unchanged target
Markdown `EvenChainGaloisDataStatement.md` (section *Sources and derived
provenance*) gives the full source account of the statement. The passages
behind the proof are:

- 9.3, printed p.72 (PDF p.25): a Galois cocycle with values in a rank-one
  torus is trivialized by Hilbert's theorem, so a reflection representative
  can be chosen over `k`.
- 9.4, printed pp.72–73 (PDF pp.25–26): this treats groups without
  components of type `A_n` (`n` even). The simple roots are grouped into
  Galois orbits, each orbit is handled over the field `k_1` of the stabilizer
  `Γ_1` of one root, and the factors of one orbit commute because its roots are
  orthogonal. This is the treatment of the unmerged simple roots here, as in
  the published orthogonal case `EvenChainOrthogonalGaloisData`.
- Notation before 9.11, printed p.74 (PDF p.27): in a component of type
  `A_{2m}`, the Galois action pairs `α_i` with `α_{2m+1-i}`. These roots are
  orthogonal unless `i = m`, so only the factors of the middle pair `α_m`,
  `α_{m+1}` are modified, using the root `α = α_m + α_{m+1}`. Theorem 9.11
  defines the modified products `N''` and `N'''`, and for several components
  their product.
- Proof of 9.16 b), d) and Remark 9.17, printed p.77 (PDF p.30): taking `u_m`
  and `u_{m+1}` in the opposite order produces a commutator term in the root
  group of `α`.
- Last paragraph of printed p.77 (PDF p.30), the proof of 9.7 e): the
  `k_1`, `Γ_1` argument of 9.4 reduces the proof to one component. `X_α` is
  formed over `k` by 9.3, and `u_m`, `u_{m+1}` are chosen by Hilbert's theorem
  so that the class of `u_m u_{m+1}` modulo `X_α` is over `k`.

The implemented proof is a derived argument in the rational-point formulation
of the target. It differs from Steinberg's proof in these ways:

- It shows that the set of `K`-rational pattern products is stable under every
  `rationalConjugate σ`. Steinberg instead proves that varieties are defined
  over `k`.
- It treats all components at once. Blocks of distinct paths commute
  (`EvenChainBlockCommutation`) and are permuted by the Galois action, which
  replaces the reduction to one component.
- It takes the unit points `u_a = x_a(1)` and `u_b = x_b(1)` of the supplied
  Galois-compatible root maps. The Galois action permutes them up to the order
  of the two factors. When an element swaps the pair, the reordering
  commutator lies in the root group of `α` (`AdjacentSimpleRootCommutator`)
  and is absorbed into the coordinate of `x_α`. Steinberg instead chooses
  `u_m` and `u_{m+1}` by Hilbert's theorem.
- The Hilbert 90 step for the merged root map is proved in
  `MergedRootGaloisData` for the stabilizers of all pairs at once, from
  Dedekind's independence of characters.

Steinberg works over a perfect field `k` with `G` simply connected and
semisimple. The statement and proof here assume neither: `K/k` is any finite
extension, and the pinning data `D` is supplied. A. Borel and T. A. Springer,
*Rationality properties of linear algebraic groups II* (1968), Theorem 8.2
and Corollary 8.3, provide such splitting fields. They are context only: the
proof takes `K` and `D` as given and uses no form of Borel–Springer 8.6.
