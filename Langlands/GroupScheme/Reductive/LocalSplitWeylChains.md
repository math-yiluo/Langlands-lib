# Rank-two chains of simple reflections and common rescalings along them

This module proves that conjugation by the simple Weyl points rescales the Weyl families of two
groups by common units (`WeylConjugationRelations`). It assumes partner uniqueness and inverse
rescaling in both groups. It imports `LocalSplitWeylBraid` and contains no `Prop`-valued
statement for the Library. Its definitions `RankTwoState.Admissible`, `TwoChains`,
`IsRankTwoState` and `WordBraids` are `Prop`-valued predicates used internally.

Notation is as in `LocalSplitWeylBraid`. `s_k g` is the index `P.reflectionPerm k g`. `ht` is
`b.height`. `v`, `v'` are the Weyl families of `u`, `u'`. `UnivRel` is the common-rescaling
relation.

## Numerical chains (section `Numeric`)

- `RankTwoState` records five integers `(h, x, y, a, b)`. They are meant as the height, the
  pairings with `c^∨` and `j^∨`, and the coefficients in `g = α + a c + b j`.
- `RankTwoState.step A B t` is the effect of `s_c` (`t = true`) or `s_j` (`t = false`), with
  `A = -⟨c, j^∨⟩` and `B = -⟨j, c^∨⟩`:
  - `s_c`: `(h, x, y, a, b) ↦ (h - x, -x, y + A x, a - x, b)`;
  - `s_j`: `(h, x, y, a, b) ↦ (h - y, x + B y, -y, a, b - y)`.
- `RankTwoState.run` applies a list of letters, head first. `RankTwoState.start p x y` is
  `(p, x, y, 0, 0)`.
- `RankTwoState.Admissible A B p l s`: at each step either the height before and after the step
  is `< p`, or the step is `s_j` at a state with `a = b = 0`.
- `altLetters t n` is the alternating list of `n` letters starting with `t`.
- `TwoChains A B m` says: for all integers `p`, `x ≥ 0`, `y > 0`, two runs are admissible for `p`.
  The first applies `altLetters false (m - 1)` to the state after one `s_c` step from
  `start p x y`; the second applies `altLetters false m` to `start p x y`. Their final states
  have the same coefficients `a` and `b`.
- `twoChains_a1a1 : TwoChains 0 0 2`, `twoChains_a2 : TwoChains 1 1 3`,
  `twoChains_b2 : TwoChains 1 2 4`, `twoChains_b2' : TwoChains 2 1 4`,
  `twoChains_g2 : TwoChains 1 3 6`, `twoChains_g2' : TwoChains 3 1 6`. They are proved by
  unfolding and `omega`, after splitting off the case `x = 0`.

## Roots (section `Roots`)

- `letter c j t` is `c` for `t = true` and `j` for `t = false`.
- `pairing_of_root_eq` gives `⟨g, k^∨⟩ = ⟨δ, k^∨⟩ + z ⟨ε, k^∨⟩` when `g = δ + z ε`.
  `root_reflectionPerm_eq` gives `s_k g = g - ⟨g, k^∨⟩ k` on roots.
- `IsRankTwoState b α c j g s` says: `g = α + s.a c + s.b j` on roots, `ht g = s.h`,
  `⟨g, c^∨⟩ = s.x` and `⟨g, j^∨⟩ = s.y`.
- `isRankTwoState_start`: `α` has the data `start (ht α) ⟨α, c^∨⟩ ⟨α, j^∨⟩`.
- `IsRankTwoState.step`: for simple `c`, `j`, applying `s_{letter c j t}` changes the data by
  `step (-⟨c, j^∨⟩) (-⟨j, c^∨⟩) t`.
- `IsRankTwoState.run` iterates the step; the root reached is
  `wordPerm P (l.map (letter c j)).reverse g`. `wordPerm_reverse_cons` is the induction step.
- `IsRankTwoState.not_mem_span`: if `α` is not an integral combination of `c` and `j`, neither
  is `g`. `ne_of_not_mem_span`: such a root is neither `c` nor `j`.

## Chains of rescalings (section `Chains`; finite reduced `P`)

- `univRel_chain`. Let `c`, `j` be simple and `α` not in the integral span of `c`, `j`. Assume:
  - for every letter `k ∈ {c, j}` and every positive `g` with `s_k g` positive and
    `ht g`, `ht (s_k g) < ht α`, there is `UnivRel` along `[k]` from `v (s_k g)` to `v g` (and
    the same with `v'`);
  - there is `UnivRel` along `[j]` from `v (s_j α)` to `v α`.

  Then for every positive `g` with data `s` and every list `l` admissible for `ht α`, there is
  `UnivRel` along `l.map (letter c j)` from `v (wordPerm (l.map …).reverse g)` to `v g`.
  Positivity along the chain follows from Mathlib's `IsPos.reflectionPerm`, because the roots
  avoid `c` and `j`.
- `altLetters_succ` is the defining recursion.
- `univRel_twoPath`. Same `c`, `j`, `α`; in addition `α` is positive, `⟨α, c^∨⟩ ≥ 0`,
  `⟨α, j^∨⟩ > 0`, `TwoChains (-⟨c, j^∨⟩) (-⟨j, c^∨⟩) m` holds for some `m ≥ 1`, and the
  alternating words of length `m` starting with `c` and with `j` give the same conjugation in
  both groups. Then there is `UnivRel` along `[c]` from `v (s_c α)` to `v α`. Both chains end
  at the same root, and conjugation along `c ::` (first chain) equals conjugation along the
  second chain; `UnivRel.cancel` then isolates the letter `c`.

## Rank-two types (section `Types`)

- `braidLength n` is `2`, `3`, `4` for `n = 0, 1, 2` and `6` otherwise; `one_le_braidLength`
  says it is at least `1`.
- `simple_pair_cases`: for distinct simple `c`, `j` of a finite reduced root datum over `ℤ`,
  `(⟨c, j^∨⟩, ⟨j, c^∨⟩)` is one of `(0, 0)`, `(-1, -1)`, `(-1, -2)`, `(-2, -1)`, `(-1, -3)`,
  `(-3, -1)`. Uses Mathlib's `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'` and
  `pairingIn_le_zero_of_ne`.
- `twoChains_of_cases`: in each case,
  `TwoChains (-⟨c, j^∨⟩) (-⟨j, c^∨⟩) (braidLength (⟨c, j^∨⟩ ⟨j, c^∨⟩))`.

## Positive roots (section `Positive`; `R` local, affine structure morphisms)

- `WordBraids P b u`: for distinct simple `c`, `j`, conjugation along
  `(altLetters true m).map (letter c j)` and along `(altLetters false m).map (letter c j)`
  agree, with `m = braidLength (⟨c, j^∨⟩ ⟨j, c^∨⟩)`.
- `weylFamily_descend`: if `W α = j :: W (s_j α)` with the same simple root, then
  `wordConj P u [j] (v (s_j α)) = v α`.
- `univRel_top_span`. Data `u`, `u'` are normal simple data for the same `P`, `b`, `W`. Let
  `c ≠ j` be simple and `α` positive and not simple. Assume `⟨α, c^∨⟩ ≥ 0`, `⟨α, j^∨⟩ > 0`,
  `α = x c + y j`, and `wordConj [j] (v (s_j α)) = v α` in both groups. Then there is
  `UnivRel` along `[c]` from `v (s_c α)` to `v α`. The rank-two classifications
  (`a1a1_coeffs`, `a2_coeffs`, `b2_coeffs`, `g2_coeffs`) leave these cases:
  - `A₂`, `α = c + j`: `κ = -1` by `wordConj_a2`;
  - `B₂` with `c` short, `α = c + j`: `κ = -1` by `wordConj_b2`;
  - `B₂` with `c` long, `α = c + 2j`; `G₂` with `c` short, `α = 3c + 2j`; `G₂` with `c` long,
    `α = c + 2j`: `κ = 1` by `wordConj_fix_of_coeffs`.
- `univRel_top`. Assume `WordBraids` for `u` and `u'`, normal data, `c` simple, `α` and `s_c α`
  positive, `⟨α, c^∨⟩ ≥ 0`. Assume the induction hypothesis: every simple step between
  positive roots of height `< ht α` has a common rescaling. Then there is `UnivRel` along `[c]`
  from `v (s_c α)` to `v α`. The cases are:
  - `α` simple: then `⟨α, c^∨⟩ = 0` and T1 applies;
  - otherwise the descending letter `j` of `α` is used: if `j = c` the claim is the
    definition; if `α` lies in the span of `c` and `j`, `univRel_top_span`; otherwise
    `univRel_twoPath`.
- `univRel_positive`: by strong induction on a height bound `n`. For every simple `c` and
  positive `α`, `s_c α` of heights `≤ n`, there is `UnivRel` along `[c]` from `v (s_c α)` to
  `v α`. The case `⟨α, c^∨⟩ < 0` reduces to `s_c α` and `UnivRel.inv_of_param`.

## Final assembly (section `Final`)

- `wordPerm_eq_of_root` identifies indices from roots.
- `wordBraids_of_partnerUnique`: normal data and `PartnerUnique P G i` give `WordBraids P b u`.
  In each type it applies `wordBase_braid` with these inputs:
  - `A₁ × A₁`: T1;
  - `A₂`: `conj_a2`;
  - `B₂`: `conj_b2`, for `c` short or for `j` short;
  - `G₂`: `conj_g2`, for `c` short or for `j` short.
- `IsNormalSimpleData.wordConj_weylFamily_simple`: `wordConj P u [c] (v c) = v (-c)` for simple
  `c`.
- `weylConjugationRelations_of_partner`: normal data `u` for `G` and `u'` for `H` with the same
  `P`, `b`, `W`, together with `PartnerUnique` and `PartnerRescales` in both groups, give
  `WeylConjugationRelations P b W u u'`. The cases for `d` are:
  - `d` positive, `d ≠ c`: `univRel_positive`;
  - `d = c`: `κ = 1`;
  - `d = -c`: `κ = 1`, by the square of `n_c` (sign `(-1)^2`);
  - `d = -α` with `α ≠ c` positive: `conj_neg` in both groups with the common unit `κ⁻¹`.

## Provenance

The induction on heights transposes SGA 3, Exp. XXI, 5.2 (construction along descending words)
to the comparison of two groups. The two-path argument for roots outside a rank-two span
corresponds to the braid relations of SGA 3, Exp. XXIII, 3.1.2(i), 3.2.1(i), 3.3.1(i) and
3.4.1(i), together with the Tits lemma Exp. XXI, 5.6. The orbit of `α` under the dihedral
group generated by `s_c` and `s_j` is traversed along its two alternating paths. The
numerical bookkeeping (`RankTwoState`, `TwoChains`) and the reduction of the braid relations
to partner uniqueness are this module's own.
