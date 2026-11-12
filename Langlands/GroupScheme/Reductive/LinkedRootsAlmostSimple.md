# Almost simplicity from linked roots

This internal module gives a criterion for almost simplicity of a semisimple group over an
algebraically closed field, in terms of noncommuting root subgroups of a split maximal torus. It
is intended for concrete groups such as the split symplectic group, whose roots are known
explicitly.

Throughout, `k : Type u` is a field, `G` is a group scheme over `Spec k`, and `t : T ⟶ G` is a
homomorphism from a commutative group scheme `T`. `relativeRoots t` and `roots t` are the
Library's roots of `t` (the same set), and `RelativeRoot.subgroup t α` is the Library's root
subgroup functor of a character `α`.

## Linked roots

* `RootsLinked t α β`: `α` and `β` are roots of `t`, and on some test scheme `Z` some point of
  the `α`-root subgroup does not commute with some point of the `β`-root subgroup. The last
  condition is `RootPairNoncommutation.NotCommuteOver` from the Library. This requires
  `G` affine over `Spec k`.
* `RootsLinked.symm`: linking is symmetric.
* `strict_combinations_of_coordinate`: let `f` be an additive map from the character lattice to
  `ℤ`. Suppose `f β = -1`, `f β' = 2`, and `f ≥ -2` on every root. Then for all `n, m > 0` the
  character `n β - m β'` is neither zero nor a root, because `f` takes the value `-n - 2m ≤ -3` on it.
* `rootsLinked_of_pairing_eq_neg_one`: over an infinite field, let `G` be connected reductive
  with a split maximal torus `i` and a root datum `P` realizing it (`IsRootDatumOf i P`). Let
  `r`, `r'` be indices with `P.pairing r r' = -1`, such that no strict combination
  `n • P.root r - m • P.root r'` (`n, m > 0`) is zero or a root. Then `P.root r` and
  `P.root r'` are linked. This applies the Library's `RootPairNoncommutation.exists_not_commute`
  over `Spec k`, with a constant `c ∈ k` different from `0` and `-1`, which exists because `k`
  is infinite.

## Linked roots and normal subgroups

Let `h : H ⟶ G` be a homomorphism, and `F`, `F'` subgroup functors of `G` that do not commute
on some test scheme.

* `NotCommuteOver.false_of_le_range_of_le_fixedSubgroup`: it is impossible that `F` lies in the
  range of `h` while `F'` lies in the centralizer of the image of `h` in `G`. That centralizer is
  the fixed subgroup of `AutomorphicAction.conjugation h`, the conjugation action of `H` on `G`
  through `h`; it is a subgroup functor of `G`. Its points commute with the image of every point
  of `H` (Library lemma `mem_conjugation_fixedSubgroup_iff`).
* `NotCommuteOver.false_of_le_fixedSubgroup_of_le_range`: the same with the roles of `F` and
  `F'` exchanged.

## The criterion

`isAlmostSimple_of_rootsLinked`: let `k` be algebraically closed and `G` semisimple, and let
`t` be a split maximal torus (`IsSplitSubtorus t`, `IsMaximalTorus t`). Assume `G` is nontrivial
(the range of `𝟙 G` is not `⊥`). Assume also that any two roots `α`, `β` of `t` are joined by
a chain `α = α₀, α₁, …, α_m = β` with `α_j` and `α_{j+1}` linked (`Relation.ReflTransGen` of
`RootsLinked t`). Then `G` is almost simple in the Library's sense `IsAlmostSimple`.

Proof:

* Semisimplicity is assumed. Noncommutativity follows from nontriviality by the Library's
  `IsSemisimple.noncommutative_of_range_ne_bot`.
* Let `H` be a smooth connected closed normal subgroup with inclusion `h`. The Library's
  `semisimpleNormalRootDichotomy` says each root subgroup lies in the range of `h` or in the
  centralizer of the image of `h` in `G` (the fixed subgroup of `H` acting on `G` by conjugation
  through `h`).
* Containment in `H` propagates along links. If `α_j`'s root subgroup lies in `H` and
  `α_{j+1}`'s did not, then by the dichotomy the latter would centralize `H`. That contradicts
  the noncommutation of the two root subgroups (previous section).
* If some root subgroup lies in `H`, all do, because any two roots are joined by a chain. The
  Library's root generation `semisimpleRootGeneration` then gives `range h = ⊤`.
* Otherwise every root subgroup centralizes `H`. The Library's
  `fixedSubgroup_eq_top_of_rootGeneration` shows that all of `G` centralizes `H`, so `H` is
  commutative. `H` is semisimple as a closed normal subgroup of a semisimple group
  (`IsSemisimple.of_normalSubgroup`). A commutative semisimple group has trivial range
  (`IsSemisimple.noncommutative_of_range_ne_bot`), so the range of `𝟙 H` is `⊥`, and hence
  `range h = ⊥` (`SubgroupFunctor.range_comp_eq_bot_iff`). This last step follows the
  Library's proof in `Reductive/SeparablyClosedAlmostSimpleAbsoluteProof`.

## Provenance

This is an internal criterion. It combines the cited Library theorems and adds no assumptions
of its own. The argument is the usual one: a normal subgroup either contains or centralizes each
root group, and linked roots must be treated alike. The chain condition is a group-theoretic
form of irreducibility of the root system: for the symplectic group, a long root `2e_a` and a
short root `e_b - e_a` or `-e_a - e_b` have pairing `-1` with the coroot of `2e_a`, and their
strict combinations have `a`-coordinate at most `-3`.
