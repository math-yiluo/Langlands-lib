# Simple relative coroots and real fundamental weights

Worker 614, Task 6347. Module
`Langlands.GroupScheme.Rational.RelativeFundamentalWeightProof`, namespace
`Langlands.GroupScheme`.

The theorem `relativeFundamentalWeight.{u}` has type exactly
`RelativeFundamentalWeightStatement.{u}`, imported from
`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.3.12, printed p.112 / PDF p.118. The paragraph identifies the simple roots and
simple coroots as bases and defines the fundamental weights and coweights as
their dual bases. This proof supplies the coroot basis, both dual bases, and
uniqueness in the spaces of the published target.

The hypotheses are a field `k : Type u`, a connected reductive group scheme
`G` over `Spec k`, a maximal split torus `i : T.toGrp ⟶ G`, a generic
cocharacter `ν`, and any supplied integral reflection data
`D : RelativeRootReflectionData i`. The proof applies to every such `D`; it
does not assert existence of reflection data. The ambient real spaces are
`Vstar T = ℝ ⊗[ℤ] characterLattice T` and
`V T = ℝ ⊗[ℤ] cocharacterLattice T`, with pairing `pair T`.

Write

- `X = relativeRootSpanReal i` for the real root span;
- `C = LinearMap.range (rationalCharacterRestrictReal i)` for the restricted
  real rational characters of `G`;
- `N = cocharacterAnnihilator C` for the cocharacter space denoted
  `𝔞^G_∅` in the book;
- `Δ = simpleRelativeRoots i ν` for the simple-root index set.

The resulting bases are indexed by `Δ`. The coroot basis is a basis of `N`
whose vector at `α` is `D.realCoroot (simpleToRelativeRoot i ν α)`. The
fundamental weights form a basis of `X`, and the fundamental coweights form a
basis of `N`. Each vector has the membership and Kronecker pairing properties
in `D.IsRealFundamentalWeight` or `IsRealFundamentalCoweight`, respectively.
The final two clauses prove uniqueness among vectors satisfying these
predicates, including their subspace membership conditions. No reducedness or
nonemptiness hypothesis is added.

## Implemented proof

The two private helper theorems below are internal linear-algebra steps derived
from published Library results, rather than additional assertions attributed to
the source.

1. `fundamental_root_basis` obtains a rational simple-root basis from
   `relativeSimpleRootBasis`. It extends scalars to `ℝ`, identifies the tensor
   product of the rational root span with its base-change submodule, and maps
   through `rationalRealTensorEquiv`. The published equality
   `map_relativeRootSpan_baseChange` identifies the image with `X`. On basis
   vectors the cancellation equivalence takes `1 ⊗ (1 ⊗ α)` to `1 ⊗ α`, giving
   a basis `b` of `X` with these actual vectors.
2. `fundamental_pair_perfect` proves that `p = (pair T).domRestrict₁₂ X N`
   is a perfect pairing whenever `X` and `C` are complementary. A vector in
   the left kernel belongs to `C` by double annihilation, and is zero by
   disjointness. For the right kernel, decompose every ambient character as
   a vector of `X` plus a vector of `C`. Both pairings vanish, the first by
   the kernel condition and the second by membership in `N`; ambient perfect
   duality then forces the cocharacter to be zero. Finite-dimensionality and
   `LinearMap.IsPerfPair.of_injective` give perfectness. The main proof uses
   the real complement from `relativeCharacterRootComplement`.
3. The main proof chooses the published positive Weyl-invariant form
   `B = relativeWeylInvariantForm i hT`. Finiteness of the relative Weyl group
   is supplied by `hG.finite_relativeWeylGroup i hi`. Positivity makes both
   maps of the flipped restriction `Br = (B.restrict X).flip` injective,
   hence `Br` is perfect. The equivalence
   `e = Br.toPerfPair.trans p.flip.toPerfPair.symm : X ≃ₗ[ℝ] N` satisfies
   `p x (e y) = B x y`.
4. For each simple root, positivity and `D.one_tmul_ne_zero` show that
   `B (b α) (b α)` is nonzero. Rescale `b α` by the unit with value
   `2 / B (b α) (b α)`, then map this basis by `e` to obtain a basis `cB`
   of `N`. The theorem `D.restrictedCharacter_coroot` puts each actual real
   coroot in `N`. The formula `D.coroot_formula` shows that this coroot and
   `cB α` have equal pairing with every vector of `X`; injectivity of the
   right map of `p` identifies them.
5. The weight basis is `cB.dualBasis.map p.toPerfPair.symm`. The coweight
   basis is `b.dualBasis.map p.flip.toPerfPair.symm`. The dual-basis equations
   give pairing `1` at the matching simple root or coroot and `0` at every
   other one. `eval_eq_pair` converts the coweight equations to the target's
   evaluation convention.
6. For uniqueness, two fundamental weights have equal associated linear
   functionals on every vector of `cB`; basis extensionality and injectivity
   of the left map of `p` identify the weights. The coweight argument uses
   `b` and injectivity of the right map of `p` in the same way.

All imported statements and their paired Markdown remain unchanged. The proof
uses the published rational simple-root basis and character/root complement;
the private scalar-extension step does not depend on a separate publication
of the real simple-root basis or real-coroot statement.
