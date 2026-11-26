# Types over one class of a normal subgroup with procyclic quotient

This internal module counts the types lying over one open-kernel irreducible
class of a normal subgroup, and those among them fixed by a continuous
automorphism. The setting is a compact nonarchimedean group `G` with a normal
subgroup `N` such that every commutator lies in `N` (`CommutatorsIn N`) and,
for every open subgroup `U` containing `N`, the powers of one element meet every
right coset of `U` (`CyclicOpenQuotients N`; then `G / U` is cyclic), from the
module `Langlands.Representation.Clifford.Procyclic`. In the application `G` is inertia and `N` wild inertia of a p-adic field: over a
Frobenius-stable orbit of wild classes there are exactly as many
Frobenius-fixed inertia types as Frobenius-fixed tame characters. This is the
role of H. Koch, *Bemerkungen zur numerischen lokalen Langlands-Vermutung*
(1984), registered as `koch-1984-numerical-langlands-remarks`, §8,
Lemmas 7 and 8 (PDF p. 6), where the representations with a fixed restriction
to the first ramification group are counted, by Schur's lemma, through
characters of the tame quotient.

## Compactness facts

`finiteIndex_of_isOpen` and `compactSpace_of_isOpen`: open subgroups of a
compact group have finite index and are compact.
`exists_pow_eq_one_of_isOpen_ker`: a character with open kernel on a compact
group has finite order. `tameCharacters_order`: if every open subgroup
containing `N` has index prime to `p`, a tame character of an open subgroup
`H ⊇ N` is killed by an exponent prime to `p`: its kernel `K`, viewed in `G`, is
an open subgroup containing `N`, hence normal, and `h^[G:K] ∈ K` for every `h`,
so the exponent `[G : K]` works.

## Coinduced types

Fix an open-kernel irreducible object `A` of `N`, its stabilizer
`H = MulAction.stabilizer G (wildClass A)` (open and of finite index,
instance `stabilizer_finiteIndex`), and an extension `θ` of `A` to `H` with
open kernel (`hθ`, `hθo`).

- `restrict_twist_eq`, `isIrreducible_twist_of_restrict`,
  `conjugatesDisjoint_twist`, `ker_twist_ge` and `isOpen_ker_twist`: a twist
  `twist χ θ` by a tame character `χ` of `H` still restricts to `A`, is
  irreducible, has conjugates disjoint from itself
  (`conjugatesDisjoint_of_stabilizer`) and has open kernel.
- `phiObj A θ hθ hθo χ hχ` is the type `coindObj H (twist χ θ)`: it is
  irreducible by `coind_isIrreducible` and continuous because the coinduction
  of an open-kernel representation from an open subgroup has open kernel
  (`isOpen_ker_induce`, module `Langlands.Weil.Representation.InductionTopology`).
- `over_phiObj`: it lies over `A`, through evaluation at one.
- `phiObj_injective`: distinct tame characters give distinct type classes. An
  equivalence of the coinductions gives, by `exists_ne_zero_of_coind`, a
  nonzero intertwiner between the twists, hence an equivalence, and
  `eq_of_twist_equiv` identifies the characters.
- `exists_phiObj_eq`: every type `B` over `A` is one of them. A nonzero
  intertwiner from `B|_N` to `A = θ|_N` yields, by `exists_twist_intertwining`,
  a character `χ` of `H` trivial on `N` and a nonzero intertwiner from `B|_H`
  to `twist χ θ`; the kernel of `χ` contains the open subgroup
  `ker B ∩ ker θ`, so `χ` is tame, and Frobenius reciprocity (`coindLift`)
  gives a nonzero intertwiner from `B` to `phiObj`, an equivalence between
  irreducible representations.

These are the irreducibility, injectivity and exhaustion statements of the
"little group" method (J.-P. Serre, *Linear Representations of Finite Groups*
(1977), registered as `serre-1977-linear-representations`, §8.2,
Proposition 25, printed pp. 62–63) for a normal subgroup with procyclic
quotient.

## Pullback along an automorphism fixing the class

Let `α` be a continuous automorphism of `G` preserving `N` whose pullback
fixes `[A]` (`wildPullback α hN [A] = [A]`); it preserves `H` (`mem_stabilizer_iff_of_fixed`), and
`continuous_restrictAut_stabilizer` and `comp_restrictAut_mem` show that
`χ ∘ α|_H` is again a tame character.

- `typeClass_pullback_phiObj`: if `θ ∘ α|_H` is equivalent to `θ`, the
  pullback of `phiObj χ` along `α` is `phiObj (χ ∘ α|_H)`, by
  `coindCompEquiv` and `coindEquivOfEquiv`.
- `nonempty_equiv_comp_restrictAut`: such an equivalence exists when `A` has
  dimension `p^a`, every open subgroup containing `N` has index prime to `p`,
  and `det θ` has `p`-power order. By `exists_twist_equiv`, `θ ∘ α|_H` is a
  twist of `θ` by a tame character, which is killed by an exponent prime to
  `p` by `tameCharacters_order`; both determinants have `p`-power order, so the
  character is trivial by `eq_one_of_detChar_pPower`.
- `exists_normalized_extension`: under `CommutatorsIn N` and
  `CyclicOpenQuotients N`, if `p` is prime, `A` has dimension `p^a` and every
  character of `N` with open kernel has `p`-power order, `A` has an extension
  to `H` with open kernel whose determinant has `p`-power order. Start from
  `exists_extension_stabilizer` and twist by the character of
  `exists_twist_detChar_pPower`.
- `dep_congr`, `dep_congr'` and `equivOfEq'` transport along equalities of
  characters; `char_comp_conj_trans`: characters are invariant under inner
  automorphisms.

## Fiber count

`encard_fixed_liesOver`: assume `CommutatorsIn N`, `CyclicOpenQuotients N`,
a prime `p` such that every open subgroup containing `N` has index prime to
`p` and every `d` prime to `p` is such an index, that every class of `N` has
rank a power of `p`, and that every character of `N` with open kernel has
`p`-power order. Let `α` be a continuous automorphism of `G` preserving `N`
and `c` a class of `N` with `α^*(c) = h • c` for some `h ∈ G` (the orbit of
`c` is `α`-stable). Then, in `ℕ∞`,
\[
  \#\{x \text{ type class} : \alpha^* x = x,\ x \text{ lies over } c\}
  = \#\{\psi \in \text{tameCharactersTop } N : \psi \circ \alpha = \psi\}.
\]

The proof replaces `α` by `α' = α ∘ conj h`, which fixes `c` and has the same
effect on type classes (`typePullback_conj_trans`) and on characters of `G`.
Choose a normalized extension `θ`; it is `α'`-invariant. Then
`χ ↦ phiObj χ` is a bijection from the `α'`-fixed tame characters of `H`
onto the `α`-fixed type classes over `c`, and the power-character map
`χ ↦ powChar χ` is a bijection from the same set onto the `α`-fixed tame
characters of `G` (`powChar_injective`, `exists_powChar_eq`,
`powChar_comp_restrictAut`). The two cardinalities agree by
`Set.encard_congr`.
