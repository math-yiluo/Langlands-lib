# Rank-ordered supports and their two-sided modified cores

This internal supporting construction is a generic version of the support chain
used in the corrected Aubert filtration. It works for any finite type `W` with a
natural-number rank function `rank : W → ℕ`. In the intended general reductive
application, `W` is the finite relative Weyl group and `rank` is its length
function. Neither identification is made here. The module contains no group
other than the abstract `W` and no representation. It applies when `W` has one
element, which covers relative semisimple rank zero.

## Sources

The definitions follow Aubert, *Erratum à « Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie d'un
groupe réductif p-adique »*, Trans. Amer. Math. Soc. 348 (1996), source
`aubert-1996-duality-erratum`, SHA-256
`d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f`. They also
follow Ban–Jantzen, *The Langlands quotient theorem for finite central extensions
of p-adic groups II* (2016), section 4, source `ban-jantzen-2016-duality`,
SHA-256 `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.

- Erratum printed p.4687: `Θ` is the set of subsets `θ ⊂ W` such that `w ∈ θ`
  and `l(w) < l(w')` imply `w' ∈ θ`. `IsRankUpper rank θ` is this condition with
  `l` replaced by `rank`.
- Erratum printed p.4689: a chain `θ_1 ⊃ θ_2 ⊃ ⋯ ⊃ θ_{t+1}` in `Θ` with
  `θ_1 = W`, `θ_{t+1} = ∅` and `θ_i − θ_{i+1} = {w_i}`. In the present
  increasing indexing, Aubert's `θ_i` is `rankOrderedSupport rank (t + 1 - i)`,
  where `t` is the cardinality of `W`.
- Ban–Jantzen printed p.161: `θ'` is the largest subset of `θ` that is
  left-invariant under `W_J` and right-invariant under `W_I`. If
  `θ_i' ≠ θ_{i+1}'` for `w = w_i`, then `W_J w W_I ⊂ θ_i'` and
  `W_J w W_I − {w} ⊂ θ_{i+1}`. Hence every element of `W_J w W_I` has length at
  least `ℓ(w)`.

The erratum's sentence on p.4689 says that the elements of `θ_{i+1}` have length
*less than* (« inférieure à ») that of `w`. With the definition of `Θ` on
p.4687, these elements have length at least `ℓ(w)`. The lemma
`rankOrderedElement_rank_le` proves this corrected direction. Ban–Jantzen p.161
justify `W_J w W_I ⊂ θ_i'` with the parenthetical "using `θ_i' ≠ θ_i`". The
hypothesis actually needed, and used here, is `θ_i' ≠ θ_{i+1}'`.

## Rank-ordered chain

`rankOrderedList rank` merge-sorts the exhaustive list of the finite type by
decreasing rank. It uses the same comparator as the Library's GL-specific
`lengthOrderedWeylList` in `LengthOrderedSupports`. Sorting preserves membership
and the absence of duplicates. Hence `rankOrderedEquiv rank` is a bijection from
list positions to `W`, and rank is antitone along it. Elements of equal rank may
appear in any order.

`rankOrderedSupport rank i` consists of the elements whose position is less than
`i`. The Lean proofs establish the following facts:

- the supports are monotone;
- the support at index `0` is empty;
- the support at any index at least the list length, the cardinality of `W`, is
  all of `W`;
- `rankOrderedSupport_step` proves that each step removes exactly the singleton
  `rankOrderedElement rank i hi`;
- `rankOrderedSupport_isRankUpper` proves that every prefix lies in `Θ`;
- `rankOrderedElement_rank_le` proves that the newly added element has minimum
  rank in the enlarged prefix.

## Two-sided modified supports

For subgroups `H K` of a finite group `W`, `modifiedRankSupport H K rank i` is
the public `twoSidedCore H K (rankOrderedSupport rank i)`. This is the largest
subset of the prefix that is left `H`-invariant and right `K`-invariant. In the
source orientation, `H = W_J` acts on the left and `K = W_I` on the right. This
is Ban–Jantzen's `θ'` for the chain above, and the module proves these
properties:

- it is contained in its prefix and is two-sided invariant;
- it is monotone, empty at index `0`, and all of `W` at the list length;
- `modifiedRankSupport_step` proves that the smaller modified support is the
  larger one minus the whole double coset `H w K` of the newly added element `w`;
- `modifiedRankSupport_succ_ne_iff` proves that consecutive modified supports
  differ exactly when `w` lies in the larger one;
- in that case, `modifiedRankSupport_succ_diff` proves that their difference is
  exactly `H w K`;
- otherwise, `modifiedRankSupport_succ_eq` proves that they are equal;
- `modifiedRankSupport_succ_minimal` proves double-coset minimality. If
  consecutive modified supports differ, then `rank w ≤ rank v` for every `v` in
  `H w K`.

The minimality proof applies the public `singleton_drop_forces_minimal` from
`TwoSidedSupport` to the enlarged prefix. Its hypothesis is
`rankOrderedElement_rank_le`. Minimality therefore comes from the rank filtration
and holds on the whole double coset, not only on a left coset.

## Scope

These are finite combinatorial lemmas. They assert nothing about a particular
Weyl group or length function. In particular, they do not prove that the
minimum-length element of a double coset is unique, or that it is the source's
representative in `D(J, I)`. Those are Coxeter-group facts about the actual
relative Weyl group and remain separate inputs. The module makes no claim about
Bruhat cells, induced or Jacquet modules, graded pieces, transition maps,
exterior signs or exactness. Proposition 3.2 of Aubert 1995 is not used. No
classification result is used.
