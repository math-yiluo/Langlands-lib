# Statement: a solvable subgroup through a split maximal torus omits a root or its negative

Module `Langlands.GroupScheme.Absolute.RankOneSolvableStatement`, proposition
`Langlands.GroupScheme.RankOneSolvableObstructionStatement.{u}` (a `Prop`-valued `def`; no
proof). It imports only `Langlands.GroupScheme.Absolute.BorelStatement` and introduces no new
definitions.

## Statement

Let `k : Type u` be any field, of any characteristic and not necessarily perfect. Let `G` be a
connected reductive group over `k` (`IsConnectedReductive G`), and let `j : T ⟶ G` be a maximal
torus (`IsMaximalTorus j`) with `T` split (`IsSplitTorus T.toGrp`). Let `i : H ⟶ G` be a closed
subgroup (`IsClosedSubgroup i`) such that `H` is smooth over `k` (`Smooth H.X.hom`), has
connected underlying space (`ConnectedSpace H.X.left`) and is solvable
(`IsSolvableGroupScheme H`). Let `f : T ⟶ H` satisfy `f ≫ i = j`. Then for every root
`α ∈ roots j`, the following two conditions do not both hold:

- some nonzero `X ∈ weightSpace j α` is the image of an element of `Lie(H)`: there is
  `Y : lieKernel H k` with `Y.val ≫ i.hom.hom = X.toMul.val`;
- some nonzero `X ∈ weightSpace j (-α)` is the image of an element of `Lie(H)` in the same
  sense.

In words, the image of `Lie(H)` in `Lie(G)` has a nonzero vector in at most one of the root
spaces `𝔤_α` and `𝔤_{-α}`.

Here `lieKernel H k` is the actual Lie algebra of `H`, the kernel of reduction
`H(k[ε]) → H(k)`, and `Y.val ≫ i.hom.hom` is the image of the dual-number point `Y.val` under
`i`. An element `X` of the weight space is an element of `Additive (lieKernel G k)`, and
`X.toMul.val` is its underlying dual-number point of `G`. This is the same Lie-image form as in
`LieSubgroupEqualityStatement`. `weightSpace j χ` is the space of `X` with
`Ad(j(t)) X_A = χ(t) • X_A` for all `k`-algebras `A` and all `t ∈ T(A)`. `roots j` is the set
of nonzero characters with nonzero weight space. The library's `IsMaximalTorus` means
maximality among closed `k`-subtori. `IsSolvableGroupScheme H` means that the group of
`k̄`-points of the base change `H_{k̄}` is solvable.

## Source

Milne, *Algebraic Groups* (2017), §21.d (printed pp.433–435, PDF pp.449–451). The setting there
is a split reductive group `(G, T)` over a field `k`, so `T` is a split maximal torus. The base
field need not be algebraically closed. Over such a field, Milne calls an algebraic subgroup
Borel when it becomes Borel over `k^a` (§17.d, printed p.363, PDF p.379).

- **Lemma 21.28** (printed p.433, PDF p.449): every Borel subgroup of `G` containing `T`
  contains exactly one of `U_α` and `U_{-α}`. The proof sets `T_α = (Ker α)_t` and
  `G_α = C_G(T_α)`. Then `G_α` has exactly two Borel subgroups containing `T`, namely
  `U_α ⋊ T` and `U_{-α} ⋊ T` (20.20), and `B ∩ G_α` is a Borel subgroup of `G_α` (17.72).
- **Proposition 21.29** (printed pp.433–434, PDF pp.449–450): for a regular cocharacter `ν`
  of `T`, `P(ν)` is a Borel subgroup containing `T` with Lie algebra
  `𝔱 ⊕ ⨁_{⟨α,ν⟩>0} 𝔤_α`. Its proof applies the lemma in Lie-algebra form: the Lie algebra of a
  Borel subgroup containing `T` contains exactly one of `𝔤_α` and `𝔤_{-α}` for each root `α`.
- **Theorem 21.32** (printed pp.434–435, PDF pp.450–451): every Borel subgroup containing `T`
  is `P(ν)` for some regular cocharacter `ν`. Its Lie algebra is therefore
  `𝔱 ⊕ ⨁_{⟨α,ν⟩>0} 𝔤_α`, and for each root `α` it meets exactly one of `𝔤_α` and `𝔤_{-α}`
  nontrivially, since `⟨α,ν⟩ ≠ 0`.

## Derived reformulation

The present statement is a derived reformulation of these results, not a statement printed
by Milne. It differs from the source in three ways:

- it is stated over every field `k`, with the library's notions of maximal torus (maximal
  among `k`-tori) and of solvability (solvability of the `k̄`-points);
- it is about every smooth connected solvable closed subgroup `H` through which `T` factors,
  not only Borel subgroups;
- it speaks only about the image of `Lie(H)` in the weight spaces `𝔤_{±α}` of `Lie(G)`.

The intended derivation passes to an algebraic closure `k̄`. By Milne, Theorem 17.82 (printed
p.379, PDF p.395), the maximal `k`-torus `T` stays maximal after base change, so
`(G_{k̄}, T_{k̄})` is split reductive. The group `H_{k̄}` is smooth, connected and solvable and
contains `T_{k̄}`. It therefore lies in a Borel subgroup `B` of `G_{k̄}` containing `T_{k̄}`, the
step the proof of Proposition 21.29 uses for `P(ν)`. By Theorem 21.32, `B = P(ν)` for some
regular `ν`. The weight spaces of the split torus `T` and the Lie algebras of `H` and `G` are
compatible with the base change `k → k̄`, and base change sends nonzero vectors to nonzero
vectors. So nonzero vectors of `Lie(H)` in both `𝔤_α` and `𝔤_{-α}` would give nonzero vectors
of `Lie(B)` in both `𝔤_{k̄,α}` and `𝔤_{k̄,-α}`. That contradicts the description of `Lie(B)`. The
maximality of `T` matters: for a non-maximal `T`, a Borel subgroup can have roots of a larger
torus restricting to both `α` and `-α`. This derivation is not formalized here.

## Use

The proof of `RegularCocharacterBorelStatement` (task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`) uses this statement in two places. In clause 1, a
smooth connected solvable `B' ⊇ P(ν)` cannot have Lie weights of both signs, so
`Lie(B') = Lie(P(ν))`, and `LieSubgroupEqualityStatement` then gives `B' = P(ν)`. Clause 3 uses
it to bound the roots in the Lie algebra of a Borel subgroup through `T`. Because of this
dependency, a proof of the present statement must not use `RegularCocharacterBorelStatement` or
`ParabolicDynamicStatement`.
