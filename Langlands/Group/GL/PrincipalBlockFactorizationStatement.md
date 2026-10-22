# Positive principal congruence block factorization

Authors: Worker 96, with the target formulation supplied by Worker 70.

## Exact statement and API

The module `Langlands.Group.GL.PrincipalBlockFactorizationStatement` imports
`Langlands.Group.GL.BlockIwahoriDefinitions` and
`Langlands.Representation.Conductor.PrincipalCongruence` unchanged.
Its sole declaration,
`Langlands.GeneralLinear.BlockShape.PrincipalBlockFactorizationStatement`,
is a transparent `def` of type `Prop`, with universe parameter `u`.

Unfolding the definition universally quantifies, in this order, over:

1. `k : Type u` and supplied instances `[Field k]`, `[ValuativeRel k]`,
   `[TopologicalSpace k]`, and `[IsNonarchimedeanLocalField k]`;
2. `n : ℕ`, an arbitrary ordered `B : GeneralLinear.BlockShape (n + 1)`,
   and `a : ℕ`;
3. a proof of `0 < a`.

The conclusion is exactly
`Function.Bijective (B.iwahoriProduct k (Langlands.Conductor.principalLevelSubgroup k n a))`.
Thus a future proof `h` of this proposition specializes as `h k n B a ha`,
with the supplied instances inferred. The proposition uses every such field,
including both possible field characteristics; it does not choose a new
valuation or topology.

Write `O` for the integer ring of `ValuativeRel.valuation k`, `m` for its
maximal ideal, and `K` for `principalLevelSubgroup k n a`. By the imported
definitions, `K` is the image in the actual `GL_(n+1)(k)` of the kernel of
`GL_(n+1)(O) → GL_(n+1)(O / m^a)`. An integral representative is congruent
to the identity in every entry. Both it and its inverse are integral.

The domain of `iwahoriProduct k K` is exactly

```text
(K ∩ B.oppositeUnipotentSubgroup k)
  × (K ∩ B.leviSubgroup k)
  × (K ∩ B.unipotentSubgroup k).
```

These are the imported subgroup intersections, using the actual opposite
radical, embedded common Levi, and upper radical. The function takes
`(l, m, u)` to `l * m * u` as an element of `K`. Bijectivity asserts existence
and uniqueness of these factors. It is bijectivity of a map of sets, with
no claim that multiplication is a homomorphism for a direct-product group.

Every ordered block shape at positive ambient rank is retained, including
one-block shapes and rank one (`n = 0`). No factorization witness,
principal-minor condition, contracting scalar tuple, or representation
hypothesis is assumed. The statement has no ambient rank-zero case.
It requires positive level: at level zero the imported subgroup is the
entire integral general linear group, which generally has elements outside
this lower-Levi-upper cell.

## Source and derived specialization

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III: *Induced representations
and the Jacquet module*, revision April 29, 2019, section 4, page 5:
the definition of Iwahori factorization and Lemma III.4.1, particularly
its proof's use of congruence subgroups at levels at least one in the split
case. The retained source is registered as `casselman-2019-jacquet-module`,
SHA256 `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.

Casselman's multiplication condition has the same opposite-radical,
Levi, upper-radical order. This proposition isolates that algebraic
condition for the Library's concrete GL principal subgroups at each
positive level. It is a derived GL specialization; the original does not
state this Lean formulation with these definitions and quantifiers.
Casselman's additional contraction conditions and neighborhood-basis
assertion are not part of this proposition.

## Expected proof route, not proof evidence

A prospective proof can perform block elimination over `O`, preserving
congruence modulo `I = m^a`. Since `a > 0`, `I` lies in the maximal ideal.
For a matrix congruent to the identity, its first diagonal block `A` is
congruent to the identity modulo `I`; its determinant is therefore a unit
of the local ring and `A` is invertible over `O`. For a two-by-two block
decomposition with remaining blocks `B₁`, `C`, and `D`, the lower
off-diagonal factor is `C A⁻¹`, the upper one is `A⁻¹ B₁`, and the remaining
diagonal block is the Schur complement `D - C A⁻¹ B₁`.
The off-diagonal factors have entries in `I`, and the Schur complement
remains congruent to the identity modulo `I`. Iterating this argument
through the ordered blocks should produce all three factors in the
same principal subgroup. Uniqueness can then be established from the
triangular shapes and their identity diagonal blocks.

This paragraph describes the intended algebraic argument only. This
module supplies a proposition to be proved in a separate proof task; it
contains no proof of bijectivity. Lean compilation and declaration
inspection establish that the statement is well formed, not that it
holds. Weak-chamber entry preservation and cofinality of principal
subgroups belong to separate consumer arguments.
