# Pointwise block Weyl cancellation for Jacquet compatibility

Author: Worker 1186. Worker 320 supplied the exact proposition and its
source dictionary in the task contract.

`Langlands.Geometric.PointwiseJacquetCoefficientStatement` is a
parameter-free proposition definition. It quantifies internally over every
natural rank `n`, every ordered positive block shape `B` and `K` of rank
`n`, and every actual permutation `w : Equiv.Perm (Fin n)`. This module
states the coefficient identity; it supplies no proof of that identity.
There are no field, topology, representation, universe or theorem
parameters.

## Formula and indicators

Write `W_B = blockWeyl B` for the actual subgroup of permutations
preserving every consecutive block of `B`, and similarly for `C` and
`K`. Under the refinement hypothesis `W_K ≤ W_B`, the proposition is the
integer equality

```text
∑_C if IsMinimalRepresentative C B w ∧ W_B ∩ w W_C w⁻¹ = W_K
    then (-1)^(n - C.length) else 0
  = if w = B.reversePermutation then (-1)^(n - K.length) else 0.
```

The permutation `w` is fixed throughout this sum. The sum runs over all
ordered positive shapes `C : BlockShape n`, using the local instance
`Fintype.ofFinite` supplied by the finiteness result in
`CuspidalSupport.FiniteBlockShapes`. No new enumeration or coefficient
family is introduced. Classical decidability permits both indicators.

The first indicator has two conjuncts. In
`IsMinimalRepresentative C B w`, `C` is the source shape and `B` is the
target shape: `w` must be strictly increasing on each source `C`-block,
and `w.symm` must be strictly increasing on each target `B`-block.
These are the Library's minimal representatives of `W_B \ W / W_C`.
The other conjunct requires equality of actual subgroups, with precisely
the displayed standard subgroup `W_K`.

The Lean expression for the intersection is

```lean
Geometric.blockWeyl B ⊓
  (Geometric.blockWeyl C).comap (MulAut.conj w⁻¹).toMonoidHom
```

Indeed, membership of a permutation `x` in that comap means
`w⁻¹ * x * w ∈ W_C`. Thus the intersection is `W_B ∩ w W_C w⁻¹`,
in the target coordinates. It is also the existing
`intersectionTarget (blockWeyl C) (blockWeyl B) w`.
No subgroup is replaced by its cardinality, conjugacy class or an
abstractly isomorphic group.

The hypothesis `blockWeyl K ≤ blockWeyl B` expresses standard
refinement: every `K`-block lies inside a `B`-block. It retains every
such refinement. Since a block of size `s` contains `s - 1` adjacent
simple roots, a shape of rank `n` has `n - length` such roots.
`BlockShape.length_le` ensures that these natural subtractions are exact.
Consequently the source sign is `(-1 : ℤ)^(n - C.length)` and the
surviving coefficient is `(-1 : ℤ)^(n - K.length)`.

## The surviving permutation and rank zero

The existing `B.reversePermutation` is characterized by

```text
B.reversePermutation (B.reverse.index i a) = B.index i.rev a.
```

It sends coordinates numbered in the reversed list of `B`-blocks to the
original `B`-coordinates. It reverses the order of whole blocks while
preserving the internal order of every block. This is the explicit
type-A representative singled out by the fixed-permutation cancellation.
Its inverse sends original coordinates to reversed-shape coordinates
and is generally a different permutation. For example, for `B = (1,2)`
the images of `0,1,2` under `B.reversePermutation` are `1,2,0`;
the inverse has images `2,0,1`. Replacing the survivor by its inverse
would change the proposition.

No separate target-side minimality premise is imposed on `w`. If
`w.symm` fails to increase within some `B`-block, every summand fails
the first indicator. Such a permutation cannot be
`B.reversePermutation`, whose inverse increases within each original
`B`-block. Both sides are therefore zero in this additional case.

At rank zero there is one empty shape and one permutation of `Fin 0`.
Every order condition is vacuous, the subgroup equality holds, and the
unique permutation equals `B.reversePermutation`. The exponents are both
zero, so the formula reads `1 = 1`. Every positive rank and every
ordered positive shape are retained as well.

## Original source and derived type-A correspondence

The original source is Anne-Marie Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur
finie d'un groupe réductif p-adique*, Trans. Amer. Math. Soc. 347
(1995), 2179–2189, equation (1.9) and the following fixed-permutation
cancellation on printed pp.2182–2183 (one-based PDF pp.4–5).
These two pages were read directly as text and images.

Literature ID: `aubert-1995-duality`. Original PDF SHA-256:
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The registered retained copy is
[Aubert (1995)](</home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995.pdf>).

After (1.9), Aubert fixes a representative
`w ∈ 𝒟(J, ∅)`, so that `w⁻¹(J)` consists of positive roots, and
puts `S_w = {α ∈ S | wα ∈ Φ⁺}`. For each `K ⊆ J`, the
coefficient is the signed sum over `I ⊆ S_w` with `w(I) ∩ J = K`.
A free root cancels the sum unless `w(S_w) ⊆ J`; in the remaining
case the coefficient is `(-1)^|K|`. The continuation on p.2183
identifies the surviving representative as `w_J` and then assembles
the representation-theoretic Jacquet identity.

Here is the derived dictionary for the stated finite type-A formula:

| Source notation or condition | Library interpretation |
| --- | --- |
| `S`, the simple roots of type A | Adjacent-coordinate edges `e_a - e_(a+1)` |
| The fixed target subset `J` | The uncut edges within the `B`-blocks |
| Source subset `I ⊆ S` | The uncut edges within the varying `C`-blocks |
| `w⁻¹(J) ⊆ Φ⁺` | `w.symm` increases within every `B`-block |
| `I ⊆ S_w` | `w` increases within every `C`-block |
| `K ⊆ J` | The standard refinement `blockWeyl K ≤ blockWeyl B` |
| `w(I) ∩ J = K` under these order conditions | The actual target intersection `W_B ∩ w W_C w⁻¹ = W_K` |
| `|I|`, `|K|` | `n - C.length`, `n - K.length` |
| The distinguished representative `w_J` | `B.reversePermutation` |

For the intersection correspondence, the intersection of these Young
subgroups preserves each common cell of a target `B`-block and a
transported source `C`-block. Under the two increasing-order conditions,
those cells are consecutive within each target block, and their adjacent
edges are exactly `w(I) ∩ J`. This describes the actual standard subgroup
`W_K` in the target coordinates.

In type A the positive source edges whose images cross different target
blocks are the free roots. Toggling one such edge changes the source
sign while preserving the target intersection. When no such edge exists,
the target block labels along `w(0), …, w(n-1)` are weakly decreasing.
Together with target-side minimality this forces the reversed order of
target blocks and increasing internal order, which gives the displayed
`B.reversePermutation`. The remaining cuts are prescribed by `K`,
with the sign `(-1)^(n - K.length)`. Only the coarse `B`-blocks are
reversed; the contributing source shape need not be `K.reverse`.

This dictionary, the explicit coordinate direction of the survivor,
the equality of actual block subgroups, the rank-zero case and the
extension from Aubert's one-sided-minimal representatives to arbitrary
permutations are derived content. They are not attributed as verbatim
statements of the source. The discussion explains the intended
correspondence; the Lean module contains only the proposition definition.

## Dependencies and scope

The module imports exactly `Geometric.WeylDefinitions`,
`CuspidalSupport.FiniteBlockShapes` and `Group.GL.ReverseBlocks`.
Their existing definition pairs are unchanged. Their project import
closure consists of these modules, the lower GL block, matrix and
opposite-block modules, and the local-field definitions used by those
matrix modules. It contains no classification, exhaustion, special-head,
tempered-uniqueness or square-integrable-classification result.

The distinction from the total Solomon coefficient is essential: this
formula retains each actual permutation and its transported intersection
before summing, so it can serve as a finite combinatorial input to a later
Jacquet-compatibility assembly. It supplies no geometric lemma, functor
compatibility, irreducible-image statement, duality involution or
classification theorem. The corrected irreducibility-complex issues in
the 1996 erratum and the later source audit are separate from this
coefficient passage; no such representation-theoretic input is used here.
