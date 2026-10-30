# Proof of the six decompositions for actual block subgroups

Author: Worker 76.

This module proves the proposition
`Langlands.Geometric.BlockParabolicSixDecomposable.{uR}` from
`Langlands.Representation.Geometric.BlockSixDecomposableStatement`.
The unapplied closing theorem is

```
Langlands.Geometric.blockParabolicSixDecomposable :
  BlockParabolicSixDecomposable.{uR}.
```

The arbitrary ring universe is retained. Every commutative ring is allowed,
including the trivial ring; every natural rank, including zero, every two
block shapes and every permutation are allowed. There are no topological
assumptions or hypotheses about minimal representatives, refinements,
projection stability, or decomposability. The statement is independently published in Library commit
`ced4d7320042961d7464496781184a2ce8f9a762`; its pair and all imported pairs
are preserved.

## Entrywise projection

For a block shape `B` and `g : B.parabolic R`, put

```
m = B.leviEmbedding R (B.leviProjection R g).
```

`embeddedLeviProjection_entry` proves, for actual ambient matrix indices
`a,b : Fin n`,

```
m a b =
  if blockIndex B a = blockIndex B b then g.val a b else 0.
```

It expresses both indices in the published sigma-type block coordinates.
In a common block the result is
`BlockShape.leviEmbedding_apply_same` followed by
`BlockShape.leviProjection_apply`. Between distinct blocks it is
`BlockShape.leviEmbedding_apply_ne`. These facts require only a commutative
ring and give the displayed formula in the actual ambient general linear
group.

For `s = GeneralLinear.permutation n R w`,
`inversePermutation_conjugate_entry` proves

```
(s⁻¹ * x * s) a b = x (w a) (w b).
```

It specializes the published `GeneralLinear.permutation_conjugate_entry`
to the inverse permutation and uses `GeneralLinear.permutation_inv`.
Combining this formula with the preceding projection identity gives
`conjugatedEmbeddedLeviProjection_entry`:

```
(s⁻¹ * m * s) a b =
  if blockIndex B (w a) = blockIndex B (w b)
  then (s⁻¹ * g.val * s) a b else 0.
```

Thus conjugating the projected matrix retains a subset of the entries of
the conjugated original matrix and zeros the other entries. In particular,
it never changes a diagonal entry.

## Preservation of the three actual conjugated subgroups

For a second block shape `C`, the three lemmas

- `embeddedLeviProjection_mem_conjugate_parabolic`;
- `embeddedLeviProjection_mem_conjugate_levi`;
- `embeddedLeviProjection_mem_conjugate_unipotent`

prove that if `g.val` belongs to `General.conjugate H s`, then `m` does too,
where `H` is respectively `C.parabolic R`, `C.leviSubgroup R`, or
`C.unipotentSubgroup R`. `General.mem_conjugate` reduces each claim to
membership of `s⁻¹ * m * s` in `H`.

For the parabolic, `mem_parabolic_iff_blockIndex` asks that entries below
the block diagonal vanish. The conjugated projection formula either
retains an entry that already vanishes or replaces it by zero.
For the Levi, `CuspidalSupport.levi_mem_iff` asks that entries between
distinct blocks vanish, and the same argument applies.

For the radical, `mem_unipotent_iff_blockIndex` asks for parabolic
membership and identity entries within every diagonal block of `C`.
The zero conditions follow as above. In a `C` diagonal block, an entry
retained by projection is the original identity entry. If the projection
sets it to zero, its two indices belong to different `B` blocks after
application of `w`; consequently the two original indices are distinct,
so the required identity entry is also zero. This proves the radical
claim without assuming a characterization of inverses or a choice of
factorization.

## The factors and their order

`isDecomposable_of_embeddedLeviProjection_stable` is a general helper for
an actual subgroup `H` whose membership is preserved by the displayed
projection. It proves

```
General.IsDecomposable H (B.leviSubgroup R) (B.unipotentSubgroup R).
```

The helper's stability hypothesis is discharged by the three preceding
lemmas in the final application. It is not a premise of the closing
theorem.

The proof uses the published `General.isDecomposable_iff`. Given
`g ∈ H ∩ (M * U)`, it first obtains `g ∈ B.parabolic R` because both the
actual Levi and radical are contained in that parabolic. Regard it as
`gp : B.parabolic R`. Use the embedded Levi factor

```
m = B.leviEmbedding R (B.leviProjection R gp)
```

and, inside the actual parabolic, the complementary factor

```
up = (B.leviInParabolic R (B.leviProjection R gp))⁻¹ * gp.
```

Projection is a homomorphism and
`BlockShape.leviProjection_section` is its section law. Hence the
projection of `up` is `1`, so `up` lies in the kernel
`B.unipotentRadical R`. Its ambient image `u` belongs to
`B.unipotentSubgroup R` by that subgroup's actual image definition.
Projection stability gives `m ∈ H`, and subgroup closure gives
`u = m⁻¹ * g ∈ H`. The Levi factor belongs to `B.leviSubgroup R`
by its range definition. Finally, group cancellation gives
`m * (m⁻¹ * g) = g`. These are precisely the two intersection factors
required by the literal set-product equality, in Levi-then-radical order.

Applying this helper to each of the three proved stability lemmas gives
`conjugate_blockParabolic_isDecomposable`,
`conjugate_blockLevi_isDecomposable`, and
`conjugate_blockUnipotent_isDecomposable`.
`blockParabolic_sixDecomposable` first applies them with target block
shape `C`, source shape `B`, and permutation `w`. It then applies them
with the shapes interchanged and permutation `w⁻¹`.
`GeneralLinear.permutation_inv` identifies the last three conjugating
matrices with the inverse of the first one. The resulting conjunction
has exactly the order in `General.SixDecomposable`. The unapplied theorem
introduces all the statement's quantifiers and invokes this result.

## Provenance and limits

This proof is an internal algebraic derivation from the Library's actual
block projection, embedding and subgroup membership formulas. It does not
use the source's root-subgroup argument. Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977),
section 5.1(4), printed page 460, gives the six conditions and their
product order; section 6.4, printed pages 468–469, supplies the motivating
parabolic application, referring to section 6.1. The registered source
is `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The exact arbitrary-ring, arbitrary-permutation formulation is an
internal strengthening specific to the explicit block matrix setting.
No applicable project erratum was found in the current notes or
literature index.

The proof establishes actual intersection decomposability only. It does
not establish Haar scaling, quotient integration, normalization
cancellation, a natural functor isomorphism, or
`Langlands.Geometric.PadicParabolicOrbitJacquetComparison`.
