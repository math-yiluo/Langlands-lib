# Irreducible representations of finite `p`-groups have `p`-power dimension

This internal module proves, for a prime `p`, that every irreducible
finite-dimensional complex representation of a finite `p`-group has dimension
a power of `p`, and deduces the same for open-kernel irreducible
representations of a compact topological group in which every open subgroup
contains the `p^b`-th powers of all elements for some `b`. The first statement
is a consequence of J.-P. Serre, *Linear Representations of Finite Groups*
(1977), registered as `serre-1977-linear-representations`, §6.5, Corollary 2
to Proposition 16 (printed p. 52): the degree divides the order of the group.
The Lean proof computes the rank by Clifford theory along a normal subgroup of
index `p`.

## Finite `p`-groups

- `nonarchimedeanGroup_of_discrete`: a discrete group is a nonarchimedean
  topological group (the trivial subgroup is open).
- `exists_finrank_eq_pow_of_isPGroup`: for a prime `p`, every `n`, every group
  `Q` of order `p^n` and every irreducible finite-dimensional complex representation
  `ρ` of `Q` (carrier in any universe), `dim ρ = p^a` for some `a`. The proof
  is by strong induction on `n`. For `n = 0` the group is trivial, hence
  commutative, and irreducible representations are one-dimensional. For
  `n + 1`, Sylow theory gives a subgroup `N` of order `p^n`; it has index `p`,
  the smallest prime divisor of the order, so it is normal and `Q / N` is
  cyclic of order `p`. With the discrete topology, `Q` is compact and
  nonarchimedean, `CommutatorsIn N` and `CyclicOpenQuotients N` hold, and `ρ`
  is a type. By `exists_over` it lies over an irreducible representation `A`
  of `N`, and by `finrank_of_over` (module
  `Langlands.Representation.Clifford.Orbit`)
  `dim ρ = [Q : Stab [A]] · dim A`. The index divides `[Q : N] = p`, and
  `dim A` is a power of `p` by induction.

## Groups with the `p`-power property

- `PPowerOpen p N` says: for every open subgroup `M` of the topological group
  `N` there is `b` with `n^(p^b) ∈ M` for all `n ∈ N`. Here `p` is an arbitrary
  natural number. When `p` is prime and `N` is profinite, this says that `N` is
  pro-`p`.
- `PPowerOpen.char_pow`: a character with open kernel is then killed by some
  power of `p`.
- `PPowerOpen.of_continuous`: the property passes along a continuous group
  isomorphism `N ≃* N'`, by pulling open subgroups back.
- `PPowerOpen.finrank`: if moreover `p` is prime and `N` is a compact
  topological group, every irreducible finite-dimensional complex
  representation `ρ` with open kernel has dimension a power of `p`. The kernel
  is open, hence of finite index (`finiteIndex_of_isOpen`), the quotient `N / ker ρ` is a finite group in
  which every element has `p`-power order, hence a `p`-group of order `p^n`,
  and `ρ` factors through an irreducible representation of it.
- `PPowerOpen.rank`: under the same hypotheses (`p` prime, `N` compact), the
  same for the rank `openKernelIrreducibleRank` of every class in
  `OpenKernelIrreducibleClasses N`.
