# Special blocks: identities, decomposition and classification

Worker 25 formalizes the Weil–Deligne block statement family of task
`f32f0f21-11a9-4bfd-9daa-e7541926d3be`. The entry proposition is
`Langlands.WeilDeligneRepresentation.Blocks.Statement`. It is the conjunction of the
fifteen targets below, with universe parameters `uK uG uV uW` (field, group, and
two independent carrier universes). The objects are the published actual pairs
of the construction companion: finite-dimensional carriers, nilpotent monodromy,
and covariance `r(g) N r(g)⁻¹ = ν(g) N`. The companion's uncentered blocks
`block ν σ m = zeroMonodromy ν σ ⊗ specialBlock ν m` are used unchanged, as are
its sums, tensors, duals, twists and monodromy kernels. Existence and uniqueness
of decompositions are conclusions. No decomposition, classification or chosen
normal form is supplied as data. These are proposition definitions; no proof is
claimed.

## Conventions

- `specialBlock ν m` is `S_m` on `Fin m → K`. The basis vector `e_j` has weight
  `ν^j` (`0 ≤ j < m`), the monodromy raises the index (`N e_j = e_{j+1}`,
  `N e_{m-1} = 0`), and so `ker N` is the top-weight line `K e_{m-1}`, of weight
  `ν^(m-1)`. This is Tate's `Sp(n)` and Henniart's `St_n`, whose restriction to
  the Weil group is `1 ⊕ ν ⊕ … ⊕ ν^(n-1)`; it is not a centered block. `m = 0`
  is allowed by the companion and gives the zero pair.
- `block ν σ m` has carrier `σ ⊗ K^m`, action `σ(g) ⊗ diag(ν(g)^j)` and monodromy
  `0 ⊗ 1 + 1 ⊗ N`. A `BlockDatum` is a Weil factor `σ` with a positive length,
  and `d.IsIrreducible` is Mathlib irreducibility of `σ`.
- The dual pair is `(r^∨, -Nᵀ)` with `r^∨(g) = r(g⁻¹)ᵀ`. The twist by a character
  `χ` multiplies the action by `χ` and keeps `N`.
- In the source setting, `degree` is the integer degree with geometric Frobenius
  of degree `+1`, inertia is `degree.ker`, and Worker 1's
  `Frobenius.NormCompatible (ν := ν) degree q` says `1 < q` and
  `ν(g) = q^(-degree g)`, so `ν(Φ) = q⁻¹`.
- `IsFrobeniusSemisimple degree` asks that `r(g)` be semisimple for every `g` of
  nonzero degree. It does not force `N = 0`.

## The targets

`IsIndecomposable A` (local predicate, complex pairs) says that the carrier is
nonzero and that any two complementary subspaces stable under the action and `N`
(Worker 1's `LinearAlgebra.IsStable`) include `⊥`.

### Block calculus over a general field

`SpecialBlockTensor` (characteristic zero) is the graded Clebsch–Gordan formula

```
S_m ⊗ S_n ≅ ⨁_{0 ≤ i < min m n} ν^i ⊗ S_{m+n-1-2i}.
```

The tensor monodromy is `N ⊗ 1 + 1 ⊗ N`. On `e_j ⊗ e_k` the weight is
`ν^(j+k)`. The chain indexed by `i` occupies weights `i, …, m+n-2-i`. Counting
chains through weight `w` gives `min(w+1, m, n, m+n-1-w)`, the dimension of that
weight space. Since `i < min m n`, the natural-number length `m+n-1-2i` is
positive and no truncation occurs. When `m = 0` or `n = 0` both sides are zero.
Characteristic zero is necessary: for `m = n = p` in characteristic `p`,
`(N ⊗ 1 + 1 ⊗ N)^p = N^p ⊗ 1 + 1 ⊗ N^p = 0`, so no chain of length `2p-1` exists.
This is Henniart 2002 §2.3, `St_n ⊗ St_m ≅ ⨁_{j=1}^{inf(n,m)} ν^(j-1) ⊗ St_{n+m+1-2j}`,
with `i = j-1`.

`BlockTensor` (characteristic zero) gives
`(σ ⊗ S_m) ⊗ (τ ⊗ S_n) ≅ ⨁_i (ν^i ⊗ σ ⊗ τ) ⊗ S_{m+n-1-2i}` with the same index
set. It follows from the previous identity by regrouping the tensor factors.
`σ` and `τ` may live in different universes.

`SpecialBlockDual` is `S_m^∨ ≅ ν^(1-m) ⊗ S_m` (integer power). Let `e*_j` be the
dual basis. Then `e*_j` has weight `ν^(-j)` and `-Nᵀ e*_j = -e*_{j-1}`. The basis
`f_k = (-1)^k e*_{m-1-k}` has weight `ν^(1-m+k)` and satisfies `-Nᵀ f_k = f_{k+1}`,
which is exactly the twisted block. This is Henniart 2002 §2.3,
`St_n^∨ ≅ ν^(1-n) ⊗ St_n`.

`BlockDual` is the corrected dual-block identity

```
(σ ⊗ S_m)^∨ ≅ (σ^∨ ⊗ ν^(1-m)) ⊗ S_m,
```

stated as `dual (block ν σ m) ≅ block ν (twist (ν^(1-m)) (dual σ)) m`. The dual
of a tensor is the tensor of the duals in finite dimension, and the dual
monodromy `-(0 ⊗ 1 + 1 ⊗ N)ᵀ` is `0 ⊗ 1 + 1 ⊗ (-Nᵀ)`.

`BlockTwist` is `χ ⊗ (σ ⊗ S_m) ≅ (χ ⊗ σ) ⊗ S_m`.

`BlockInvariants` collects the numerical and kernel consequences:

- `det(σ ⊗ S_m) = (det σ)^m · ν^(rank σ · m(m-1)/2)`, because
  `det(A ⊗ D) = det(A)^m det(D)^(rank σ)` and `det diag(ν^j) = ν^(m(m-1)/2)`
  (exact natural division). The rank formula `rank = rank σ · m` is already the
  companion theorem `rank_block`.
- `N^m = 0`, and if `σ ≠ 0` then `N^n ≠ 0` on the block of length `n+1`, so the
  nilpotency order is exactly the length.
- `block ν σ 1 ≅ zeroMonodromy ν σ`.
- The monodromy kernel of the block of length `n+1` is `ν^n ⊗ σ`: it is
  `σ ⊗ K e_n`, the top-weight copy. A twist keeps the carrier, so the kernel
  has dimension `rank σ`.

`BlockSumKernel` identifies the monodromy kernel of a finite sum of blocks with
`⨁_i ν^(m_i - 1) ⊗ σ_i`. This is the representation `(Ker N)` whose inertia
invariants define Tate's `V_N` (4.1.6), and it is the WD content of Henniart 2002
§2.4, `L(s, ρ ⊗ St_n) = L(s, ν^(n-1) ⊗ ρ)`.

`TensorBlockKernel` (characteristic zero) identifies the monodromy kernel of
`(σ ⊗ S_m) ⊗ (τ ⊗ S_n)` with `⨁_{i < min m n} ν^(m+n-2-i) ⊗ σ ⊗ τ`. The chain `i`
of `BlockTensor` has top weight `i + (m+n-1-2i) - 1 = m+n-2-i`. This matches the
exponents in Henniart 2002 §2.4,
`L(s, (ρ ⊗ St_n) ⊗ (ρ' ⊗ St_n')) = ∏_{j=1}^{inf(n,n')} L(s, ν^(n+n'-1-j) ⊗ ρ ⊗ ρ')`,
with `j = i+1`. The L-factor identity itself belongs to Worker 4's arithmetic
factor statements; only the representation isomorphism is stated here.

`FrobeniusSemisimpleBlocks` (any field, any degree) states that a block of
positive length is Frobenius-semisimple exactly when its Weil factor is, and that
a finite sum is Frobenius-semisimple exactly when each summand is. The block
action is `⨁_j ν(g)^j σ(g)`. Nonzero scalar multiples and finite direct sums of
semisimple endomorphisms are semisimple, and the weight-`1` summand `σ ⊗ e_0` is
an invariant subspace. A block of length at least two with a nonzero
Frobenius-semisimple Weil factor is therefore Frobenius-semisimple with nonzero
monodromy.

`RankOne` (any field) states that a rank-one pair has zero monodromy (a nilpotent
scalar is zero), is Frobenius-semisimple for every degree, and is isomorphic to
the zero-monodromy pair of its determinant line.

### Decomposition and criteria over `ℂ`, with no hypothesis on the group

`DecompositionExistence`: if the Weil representation of a complex pair is
semisimple, then the pair is isomorphic to a finite sum of blocks with
irreducible Weil factors. No hypothesis on `G` or `ν` is needed. The intended
argument is as follows. Let `m` be the nilpotency order, choose a Weil-stable
complement `C` of `ker N^(m-1)` and an irreducible Weil subrepresentation `σ ⊂ C`. Then `N^j|σ` is
injective for `j < m`, and `σ ⊕ Nσ ⊕ … ⊕ N^(m-1)σ` is a sub-pair isomorphic to
`σ ⊗ S_m`, via `v ⊗ e_j ↦ N^j v`, because `r(g) N^j = ν(g)^j N^j r(g)`. Take a Weil-equivariant projection `p` onto
`N^(m-1)σ`. Then `{v : p(N^j v) = 0 for all j}` is stable under the action and
`N`, meets the sub-pair trivially, and has dimension at least `dim V - m·dim σ`,
so it is a complement. Induction on dimension finishes the argument.

`DecompositionUniqueness`: two finite sums of irreducible blocks are isomorphic
if and only if some bijection of the index sets preserves lengths and Weil
factors up to isomorphism. The isomorphism invariant is the family of Weil
representations `(ker N ∩ im N^(k-1)) / (ker N ∩ im N^k)`. For a block of length
`m` it is `ν^(m-1) ⊗ σ` if `k = m` and zero otherwise, so the multiplicities
follow from Jordan–Hölder for semisimple representations. This is the
uniqueness half of Henniart 2002 §2.2: the map `ℕ[G2] - {0} → G` is a bijection.

`BlockCriteria` states four things.

- An irreducible block is indecomposable: complementary stable subspaces split
  `ker N = ν^(m-1) ⊗ σ`, which is irreducible, and a stable subspace meeting
  `ker N` trivially is zero. Its Weil representation is semisimple. It is
  irreducible as a pair, and has zero monodromy, exactly when its length is one
  (Tate 4.1.5).
- Two irreducible blocks are isomorphic exactly when their lengths agree and
  their Weil factors are isomorphic. This is the bijection `G0 × ℕ^× → G2` of
  Henniart 2002 §2.3.
- A pair with semisimple Weil representation is indecomposable exactly when it
  is isomorphic to an irreducible block.
- A finite sum of irreducible blocks has zero monodromy exactly when every length
  is one.

### Source setting: Frobenius semisimplicity and parameters

`FrobeniusSemisimpleClassification` assumes the source hypotheses: a surjective
degree, `NormCompatible`, finite inertia image (`HasFiniteInertiaImage degree.ker`)
and Frobenius semisimplicity. Under these, a pair decomposes into irreducible
blocks whose Weil factors have finite inertia image. Conversely, every such block
has finite inertia image and is Frobenius-semisimple. Finally, a pair is
indecomposable exactly when it is an irreducible block. This is Tate 4.1.5, "the
Φ-semisimple indecomposable representations of W'_F are those of the form
ρ ⊗ Sp(n) with ρ irreducible". The hypotheses are used as follows.

- Frobenius semisimplicity together with finite inertia image gives ordinary
  semisimplicity (Tate 4.1.3): a power of `r(Φ)` commutes with the finite group
  `r(I)`, the subgroup `degree⁻¹(kℤ)` has finite index, and Maschke's theorem
  applies on the eigenspaces. `DecompositionExistence` then applies, with
  summands inside the given pair, so they inherit finite inertia image.
- For an irreducible `σ` with finite inertia image, the same power of `r(Φ)` is
  scalar by Schur's lemma, so every `σ(g)` has a power that is scalar and is
  semisimple. `NormCompatible` is used only to make `ν` trivial on inertia.
  Without it, `ν` on `degree.ker` may have infinite image, and the block would
  not have finite inertia image.

`ParameterNormalForm` is the parameter-side normalization interface. It assumes
a topological group, surjective degree, `NormCompatible`, and compact inertia
`degree.ker`. Every Frobenius-semisimple parameter
(`IsFrobeniusSemisimpleParameter degree.ker degree`, that is, open inertia kernel
and Frobenius semisimplicity) is isomorphic to a finite sum of blocks whose Weil
factors are irreducible with open inertia kernel. Conversely, every such finite
sum, including the empty one, is a Frobenius-semisimple parameter.
`CompactSpace` is what turns an open inertia kernel into a finite inertia image:
an open subgroup of a compact group has finite index. The kernel of a summand
contains the kernel of the pair. Conversely, the block's inertia kernel is that of
`σ`, since `ν` is trivial on inertia, and a finite intersection of open subgroups
is open. Together with `DecompositionUniqueness`, this gives the existence and
uniqueness of the block normal form of a Frobenius-semisimple parameter. The
normal form is not used as a definition of parameter classes.
Finally, for every rank `n` the companion's set
`FrobeniusSemisimpleParameterClassesOfRank degree.ker degree n` of genuine
isomorphism classes is nonempty. A witness is the class of the trivial
representation of rank `n` with zero monodromy: its kernel is the whole group,
and the identity is semisimple. This is the honest rank-`n` nonemptiness
interface on the parameter side. It asserts nothing about representations of
`GL_n`.

## Provenance

The family is derived. The objects and formulas come from the sources listed
below. The exact Lean formulations are finite-dimensional linear algebra about
the companion's uncentered blocks: index ranges, natural-number exponents, the
integer twist `1-m`, the kernel exponents, the general-field and
characteristic-zero ranges, and the hypotheses of the existence statements.
Their derivations are given above. None is attributed as a literal numbered
statement in the sources. The following are derived additions that are not
displayed formulas in the sources:

- the determinant formula, the nilpotency order and `TensorBlockKernel`
  (Henniart displays only the corresponding L-factors);
- `FrobeniusSemisimpleBlocks` and `RankOne`;
- existence of the decomposition from ordinary semisimplicity without hypotheses
  on `G`.

| Declaration | Exact source input and derived step |
| --- | --- |
| `IsIndecomposable` | Tate 4.1.5 and Henniart 2002 §2.2 (indecomposable summands); ordinary definition with stable subspaces. |
| `SpecialBlockTensor`, `BlockTensor` | Henniart 2002 §2.3 `St_n ⊗ St_m`; Tate 4.1.5 tensor monodromy `N ⊗ 1 + 1 ⊗ N₁`; reindexed `i = j-1`; characteristic zero as in Tate 4.1.2 and Deligne 8.4.1. |
| `SpecialBlockDual`, `BlockDual` | Henniart 2002 §2.3 `St_n^∨ ≅ ν^(1-n) ⊗ St_n`, and §2.2 distributivity of duals; dual basis computation above. |
| `BlockTwist` | Tate 4.1.5 tensor of pairs, with a character as a zero-monodromy pair; derived regrouping. |
| `BlockInvariants` | Tate 4.1.4 basis and weights; derived determinant and kernel computation; Henniart 2002 §2.4 top weight `ν^(n-1)`. |
| `BlockSumKernel`, `TensorBlockKernel` | Henniart 2002 §2.4 L-factor exponents and Tate 4.1.6 `V_N = (Ker N)^I`; derived representation isomorphisms. |
| `FrobeniusSemisimpleBlocks`, `RankOne` | Tate 4.1.3 and Deligne 8.5–8.6 (Frobenius semisimplicity as an operator condition); derived. |
| `DecompositionExistence`, `DecompositionUniqueness` | Henniart 2002 §2.2 unique decomposition and §2.3 form of indecomposables; derived from ordinary semisimplicity by the argument above. |
| `BlockCriteria` | Tate 4.1.5 (kernel stability, irreducibility) and Henniart 2002 §2.3 (bijection `G0 × ℕ^× → G2`). |
| `FrobeniusSemisimpleClassification` | Tate 4.1.3 and 4.1.5, Deligne 8.4.1 and 8.5–8.6, with Worker 1's `NormCompatible` for `‖w‖ = q^(-v(w))`. |
| `ParameterNormalForm` | Tate 4.1.2(a) open inertia kernel, 4.1.3 and 4.1.5; Henniart 2002 §2.2–2.3; compact inertia as for local Weil groups. |

Original sources, read by Worker 25 for this family (locators re-verified on
2026-10-20):

- `henniart-2002-characterization`, retained PDF, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  §2.1–2.2, printed page 593 (PDF 7): sums, unique decomposition into
  indecomposables (`ℕ[G2] - {0} ≅ G`), and distributivity of tensor products and
  duals. §2.3–2.4, printed page 594 (PDF 8): `σ ≅ ρ ⊗ St_n`, `St_n|W_F ≅ 1 ⊕ ν ⊕ … ⊕ ν^(n-1)`,
  `St_n^∨ ≅ ν^(1-n) ⊗ St_n`, `St_n ⊗ St_m ≅ ⨁_j ν^(j-1) ⊗ St_{n+m+1-2j}`, the
  bijection `G0 × ℕ^× → G2`, and the L-factor formulas with exponents `ν^(n-1)` and
  `ν^(n+n'-1-j)`.
- `tate-1979-number-theoretic-background`, retained Corvallis `Part II.pdf`,
  SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Sections 4.1.2–4.1.5, printed page 20 (PDF 29): the pair `(ρ, N)` with open
  inertia kernel and `ρ(w) N ρ(w)⁻¹ = ‖w‖ N`; Φ-semisimplification and its
  equivalence with ordinary semisimplicity, via the finite-index argument;
  `Sp(n)` with `ρ(w) e_i = ‖w‖^i e_i`, `N e_i = e_{i+1}`, `N e_{n-1} = 0`; kernel
  stability, the irreducibility criterion, and the Φ-semisimple indecomposables
  `ρ ⊗ Sp(n)` with tensor monodromy. Section 4.1.6, printed page 20 (PDF 29):
  `V_N = (Ker N)^I`.
- `deligne-1973-local-constants`, retained original PDF, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  Definition 8.4.1 (internal/PDF page 68): pairs over a characteristic-zero field;
  8.5–8.6 (internal/PDF page 70): the unipotent part of Frobenius and
  F-semisimplification.

## Lean dependency map

All imports are Lean modules of the current Library (commit
`6700bb7581ced62a8982c39bcea021acff83aad7`); no artifact identity is imported.
Direct project imports and their transitive project closure:

| Module | Declarations used here | Lean SHA-256 |
| --- | --- | --- |
| `Langlands.WeilDeligne.SpecialBlocks` | `specialBlock`, `block`, `BlockDatum`, `BlockDatum.pair`, `BlockDatum.IsIrreducible` | `1280fb510bf4f1d71c707c3b142b404d1d2914d1aacdeee3dff67e81c6312e07` |
| `Langlands.WeilDeligne.DirectSum` | `directSum` (over `Fin k`) | `a8ec6276d9edcf0f8e811559c982e9ba03deaa2803c7ccaa22c77d26669e6907` |
| `Langlands.WeilDeligne.Dual` | `dual` (negative-transpose monodromy) | `f93dac4cc8e4a22401bff9a548fca0d3103439ae2c859bcd08d833c9d74f12e9` |
| `Langlands.WeilDeligne.Twist` | `twist` | `772f17a7cd090d61a70b7a410aff4b7a0ba14609b5687d378497f696f345faa0` |
| `Langlands.WeilDeligne.Determinant` | (brings `FiniteRepresentation.determinantCharacter`, `FiniteRepresentation.determinant`) | `c3f623a122f2154873d75bdedf195bffaf7ccf9b2abf31478ef8e4e0aa085091` |
| `Langlands.WeilDeligne.Kernels` | `kernelRepresentation` | `fc80f9ec895d5bfbc1ae4b397c799aa657eac45b2a4154be30a0fc8f5d560da6` |
| `Langlands.WeilDeligne.LinearAlgebraStatements` | `LinearAlgebra.IsStable`, `LinearAlgebra.IsIrreducible` | `31dab68f45eca19af6533a9ae09933e55a974a4027c20c990b066f07fc42eddc` |
| `Langlands.WeilDeligne.FrobeniusStatements` | `Frobenius.NormCompatible` only | `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa` |
| `Langlands.WeilDeligne.SumsTensor` | `tensor` | `b022cece208c2429280b3485628442f05da9e0097cb1fb558448a36bc6e0c06d` |
| `Langlands.WeilDeligne.Parameters` | `IsFrobeniusSemisimpleParameter`, `FrobeniusSemisimpleParameterClassesOfRank` | `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c` |
| `Langlands.WeilDeligne.Basic` | `WeilDeligneRepresentation`, `Equiv`, `monodromy`, `rank`, `zeroMonodromy`, `IsFrobeniusSemisimple` | `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf` |
| `Langlands.Weil.Representation.DirectSum` | `FiniteRepresentation.directSum` | `b0d730015d7456225937210ba69093a92e268cdde0454d4ed035742ed27e91e1` |
| `Langlands.Weil.Representation.Dual` | `FiniteRepresentation.dual` | `38cafaca417661df1fd2462cb71fcb880341c4fc561de35797c8b713229a8f74` |
| `Langlands.Weil.Representation.Twist` | `FiniteRepresentation.twist` | `cbeda9cff731f24d07c356c7e24e5e9a20a6e248fc9439bc0888cc909ab862c8` |
| `Langlands.Weil.Representation.Determinant` | `FiniteRepresentation.determinantCharacter`, `FiniteRepresentation.determinant` | `9a327d3755e33b6b585efc2f2545583a64239044cb0e9cb99a913fb7116ebac3` |
| `Langlands.Weil.Representation.Invariants` | (through `Kernels`) | `6b8ce494e92094357b8035f0a2c782cd67be997a7eb420f01a0ae0b7e78bd87f` |
| `Langlands.Weil.Representation.SumsTensor` | `FiniteRepresentation.tensor` | `d5ce49ecda33a85b025d201c0cb114a98bbed8c65d36050aa6fc1b55cf42275b` |
| `Langlands.Weil.Representation.Predicates` | `IsSemisimple`, `HasFiniteInertiaImage`, `HasOpenInertiaKernel` | `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148` |
| `Langlands.Weil.Representation.Basic` | `FiniteRepresentation`, `FiniteRepresentation.Equiv`, `rank` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Representation.Dual.Definitions` | (generic algebraic dual, through `Dual`) | `53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5` |
| `Langlands.Representation.Twist.Definitions` | (scalar character twist, through `Twist`) | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` |

The WD construction modules are authored by Worker 17 (construction companion
task `650de61a-84c3-40d1-b791-0544af5824e1`). `LinearAlgebraStatements` and
`FrobeniusStatements` are Worker 1's statement families (task
`4bcfd048-60a1-4be4-a737-2fb8c48efc46`). Only their predicates `IsStable`,
`IsIrreducible` and `NormCompatible` are used; none of their proposition targets
is assumed. Mathlib is pinned at `5ed2965256430c3649e86755f9576b54eca72435`;
`Representation.IsIrreducible` and `Module.End.IsSemisimple` come from Mathlib.

## Scope

The targets are generic: arbitrary groups, an explicit norm character and an
explicit integer degree. Specialization to the actual local Weil group (actual
inertia, geometric Frobenius degree and `ν = q^(-degree)`) is a separate family,
built on the arithmetic constructions. No L, epsilon or gamma identity and no
correspondence assertion is included.
