# Commutator relations of Weyl families from Weyl conjugation and rank two

This module proves the published `LocalSplitWeylCommutatorStatement` (module
`LocalSplitIsomorphismAssembly`) from two statements:

- `LocalSplitRankOneNormalStatement` (module `LocalSplitRankOneNormalStatement`): rank-one
  normalization of the simple roots;
- `LocalSplitWeylConjugationStatement` (module `LocalSplitWeylConjugationStatement`): common
  Weyl-conjugation units.

Neither statement is proved here. The proof reduces each pair of positive roots to a
rank-two subsystem. There it uses the commutator constants of types `A₂`, `B₂` and `G₂`
(modules `LocalSplitTypeA2`, `LocalSplitTypeB2`, `LocalSplitTypeG2`). The module also imports
`LocalSplitRankOneConsequences` and `Langlands.LinearAlgebra.RootDatumRankTwoBase`.

Notation:

- `rootPoint w Z x` is the point of `G` over `Z` given by `w : 𝔾ₐ ⟶ G` at the global function
  `x`.
- `weylFamily P W u` is the Weyl family of the simple-root data `u` along the words `W`.
- `rootWeylPoint P u c` is the Weyl point `n_c` of the simple root `c`.
- `wordConj P u l w` conjugates `w` by the Weyl points of the letters of `l`.
  For `l = [c₁, …, c_k]` it is `w ≫ Ad(n_{c_k}) ≫ ⋯ ≫ Ad(n_{c₁})`.
- `wordPerm P l d` is the matching index `s_{c₁} ⋯ s_{c_k} d` (module
  `RootDatumRankTwoBase`).
- `scaleHom κ` is multiplication by `κ` on `𝔾ₐ`.
- `baseScalar Z r` is the image of `r ∈ R` in the global functions of `Z`.
- `[g, h] = (g h)⁻¹ (h g)`.

## Main statement

`LocalSplitWeylCommutatorReductionStatement.{u}` is the proposition

`LocalSplitRankOneNormalStatement.{u} → LocalSplitWeylConjugationStatement.{u} →
LocalSplitWeylCommutatorStatement.{u}`.

The module proves it as `localSplitWeylCommutatorReduction`, by the theorem
`localSplitWeylCommutator_of_weylConjugation`, which has the same type.

## Commutator formulas (namespace `Langlands.GroupScheme.LocalSplitCell`)

The base ring `R` is commutative, and `G` is a group scheme over `Spec R`.

- **Points along words.**
  - `wordPoint u l Z` is the product of the pulled-back Weyl points of the letters of `l`.
  - `rootPoint_wordConj` writes `rootPoint (wordConj P u l w) Z x` as the conjugate of
    `rootPoint w Z x` by `wordPoint u l Z`.
  - `wordConj_scaleHom` moves `scaleHom κ` out of `wordConj`.
- **Iterated Weyl conjugation.** `WeylConjugationRelations.wordConj_weylFamily`: under
  `WeylConjugationRelations P b W u u'`, let `l` have letters in `b.support`. Then for every
  `d` there is one unit `κ` with
  `wordConj P u l (v_d) = scaleHom κ ≫ v_{wordPerm P l d}` for `v = weylFamily P W u`, and
  the same for `u'` with the same `κ`.
- **Terms and formulas.**
  - A *term* (`CommTerm R G`) is a triple `(w, c, i, j)` of a map `w : 𝔾ₐ ⟶ G`, a constant
    `c ∈ R` and two exponents. Its point (`termPoint`) over `Z` at `x, y` is
    `w(baseScalar Z c · x^i · y^j)`.
  - `CommRel w₁ w₂ L` says: over every `s : Spec B → Spec R` (`B` a commutative ring in
    universe `u`), for all global functions `x, y`, `[w₁(x), w₂(y)]` is the product of the
    points of the terms of `L`, in order.
  - `PointsCommute w w'` says that the points of `w` and `w'` commute over every such `s`;
    `commRel_nil` then gives `CommRel w w' []`.
- **Operations on formulas.**
  - `CommRel.map_terms` replaces terms by terms with the same points.
  - `CommRel.rescale` passes from `w₁ = scaleHom κ₁ ≫ w₁'`, `w₂ = scaleHom κ₂ ≫ w₂'` to `w₁'`,
    `w₂'`. The constants become `c · (κ₁⁻¹)^i · (κ₂⁻¹)^j`.
  - `CommRel.symm` exchanges `w₁`, `w₂`: the list is reversed, the constants negated and the
    exponents swapped.
  - `CommRel.conj_word` conjugates everything along a word.
  - `CommRel.swap` exchanges two adjacent terms whose maps satisfy `PointsCommute`.
- **Reversed rank-two formulas.**
  - `CommRel.b2_reverse`: from `[w_a(x), w_c(y)] = p₁(x y) p₂(x² y)` and commuting `p₁`, `p₂`,
    it gives `[w_c(x), w_a(y)] = p₁(-x y) p₂(-x y²)`.
  - `CommRel.g2_reverse`: from
    `[w_a(x), w_c(y)] = p₁(x y) p₂(x² y) p₃(-x³ y) p₄(-x³ y²)`, from
    `[p₁(x), p₂(y)] = p₄(-3 x y)`, and from pairwise commutation of `p₁, …, p₄` except `p₁`,
    `p₂`, it gives
    `[w_c(x), w_a(y)] = p₁(-x y) p₂(-x y²) p₃(x y³) p₄(-2 x² y³)`.
  - The group identity `reorder_four` is used for this.

## Universal coordinates

`IsUnivComm v pos k l E` (module `LocalSplitCommutatorPolynomials`) says that the
commutator of the factors at positions `k`, `l` of the enumeration `pos` has the universal
coordinates `E`.

- `prod_ofFn_eq_prod_map` reduces an ordered product over `Fin n` to the factors at a
  strictly increasing list of positions, when the others are trivial.
- `isUnivComm_of_commRel`: if `CommRel (v (pos k)) (v (pos l))` holds with terms at strictly
  increasing positions, then `IsUnivComm v pos k l E` holds for `E` the matching monomials
  `c S^i T^j` (zero elsewhere).
- `exists_common_isUnivComm`: if the same list of terms, indexed by roots `L` and positions
  `q` with `pos (q t) = t` and strictly increasing, gives formulas for `G` and for `H`, then
  one `E` works for both.

## Conversion and transport

- `wordTerms u v WL` turns entries `(m, d, c, i, j)` into the terms
  `(wordConj P u m (v d), c, i, j)`. `indexTerms v L` turns `(d, c, i, j)` into
  `(v d, c, i, j)`.
- `WeylConjugationRelations.commRel_convert`: under `WeylConjugationRelations`, suppose a
  formula `CommRel (wordConj l₁ v_{d₁}) (wordConj l₂ v_{d₂}) (wordTerms WL)` holds in `G` and
  in `H` with the same `WL`, all words having letters in `b.support`. Then there is one list
  `L` with
  `CommRel v_{wordPerm l₁ d₁} v_{wordPerm l₂ d₂} (indexTerms L)` in both groups. Its indices
  and exponents are those of `WL` (index `wordPerm m d` for an entry `(m, d, …)`). Only the
  constants change, by the common units.
- `WeylConjugationRelations.transport` combines this with `CommRel.conj_word` along a further
  word `l`: the indices become `wordPerm (l ++ m) d`.

## Rank-two input

- `IsNormalSimpleData i P b W u` bundles the hypotheses on one group:
  - `G` is reductive, `i` is fibrewise maximal, `P` is a fibrewise root datum;
  - `u a`, `u (-a)` are root parametrizations and `rootWeylPoint P u a` is a Weyl point
    acting by `s_a`, for every simple `a`;
  - `W` is descending (`IsDescendingWords`);
  - `RankOneNormal i P u a` holds for every simple `a`.
- Consequences: `weylFamily P W u a = u a` for simple `a`; every `weylFamily P W u α` is a
  root parametrization; there is a family `v` of root parametrizations of all roots that
  agrees with `u` at `a`, `c`, `-a`, `-c`. The squares of the simple Weyl points act on root
  groups by `(-1)^⟨β, a^∨⟩` (`conj_sq`, from `conj_sq_rootPoint`).
- `IsNormalSimpleData.g2_commRels`: in type `G₂` (`⟨a, c^∨⟩ = -1`, `⟨c, a^∨⟩ = -3`), the five
  formulas of `g2_constants`, written with `p₁ = wordConj [c] v_a`, `p₂ = wordConj [a, c] v_a`,
  `p₃ = wordConj [a] v_c`, `p₄ = wordConj [c, a] v_c`:
  - `[v_a(x), v_c(y)] = p₁(x y) p₂(x² y) p₃(-x³ y) p₄(-x³ y²)`;
  - `[v_a(x), p₁(y)] = p₂(2 x y) p₃(-3 x² y) p₄(-3 x y²)`;
  - `[v_a(x), p₂(y)] = p₃(-3 x y)`;
  - `[v_c(x), p₃(y)] = p₄(-x y)`;
  - `[p₁(x), p₂(y)] = p₄(-3 x y)`.
- `IsNormalSimpleData.b2_commRels`: in type `B₂` (`⟨a, c^∨⟩ = -1`, `⟨c, a^∨⟩ = -2`), with
  `p₁ = wordConj [c] v_a` and `p₂ = wordConj [a] v_c`:
  `[v_a(x), v_c(y)] = p₁(x y) p₂(x² y)` and `[v_a(x), p₁(y)] = p₂(2 x y)`.
- `IsNormalSimpleData.a2_commRel`: in type `A₂` (both pairings `-1`):
  `[v_a(x), v_c(y)] = (wordConj [a] v_c)(-x y)`.

## Pairs of positive roots

Here a second base `b'` of `P` measures positivity and height, while the words and simple roots
are those of `b` (the base of `W`). The main theorem uses `b' = b`; other choices, such as a
base whose positive roots are the negative roots of `b`, give formulas for other pairs.

- `PairFormula b' W u u' q β ε` says that there is a list `L` of entries `(δ, c, i, j)` such
  that:
  - every `δ` is positive for `b'`;
  - the positions `q δ` strictly increase along `L`;
  - `CommRel (v_β) (v_ε) (indexTerms L)` holds for both Weyl families.
- `WeylConjugationRelations.pairFormula_of_standard` derives `PairFormula` from a formula in
  standard position, transported along a word `l`. It assumes:
  - every term root `wordPerm (l ++ m) d` is `i β + j ε` with `i, j ≥ 1`;
  - for each pair of terms, in order, either the exponent pairs increase componentwise
    (strictly), or the positions `q` increase;
  - `q` is strictly monotone in the `b'`-height on `b'`-positive roots.
- `pairFormula_of_commute_std` and `pairFormula_of_commute_coeffs` treat pairs with no root
  in their cone. The formula is empty, by the imported `rootPoint_commute_of_forall_ne`.
- Pair lemmas. In each, `β = wordPerm l s₁` with `s₁` simple, and `ε = wordPerm l ε₀` with
  `ε₀ = p₀ a + q₀ c`, `p₀, q₀ ∈ ℕ`, `ε₀ ≠ s₁`:
  - `pairFormula_g2_short` and `pairFormula_g2_long` (type `G₂`, `s₁ = a` short or `s₁ = c`
    long);
  - `pairFormula_b2_short` and `pairFormula_b2_long` (type `B₂`);
  - `pairFormula_a2` (type `A₂`) and `pairFormula_a1a1` (`⟨c, a^∨⟩ = 0`).

  `pairFormula_g2_short` also assumes that `q` is injective on positive roots.
- `pairFormula_of_pos`: under `IsNormalSimpleData` for `G` and `H` and
  `WeylConjugationRelations` (for the base `b`), let `q` be strictly monotone in the
  `b'`-height and injective on `b'`-positive roots. Then every two distinct `b'`-positive roots
  `β`, `ε` satisfy `PairFormula b' W u u' q β ε`.

## Proof

**Formulas and universal coordinates.** `CommRel.rescale`, `symm`, `conj_word` and `swap`
are direct rewritings of the products, with Mathlib's `group` tactic for the abstract group
identities. `isUnivComm_of_commRel` evaluates a formula over `Spec R[S][T]` at `x = S`,
`y = T`. It then uses `prod_ofFn_eq_prod_map` to identify the ordered product with the
product of the terms. `exists_common_isUnivComm` builds `E` from the list
(`exists_fun_of_list`).

**Conversion.** `wordConj_weylFamily` is an induction on the word: each letter contributes
the unit of `WeylConjugationRelations`, and units multiply (`scaleHom_comp_scaleHom`). In
`commRel_convert`, each term `wordConj m v_d` is `scaleHom κ ≫ v_{wordPerm m d}`, which
multiplies its constant by `κ`. The two outer maps are rescaled by `CommRel.rescale`. The same
units occur in `G` and `H`, so the constants agree.

**Standard formulas.** `g2_commRels`, `b2_commRels` and `a2_commRel` apply the imported
`g2_constants`, `b2_constants` and `a2_constants` to the family of `exists_family`. Its Weyl
points are the given ones. The rank-one identities come from `RankOneNormal` and the
square actions from `conj_sq`. The conclusions are rewritten into `CommRel` form
(`commRel_of_forall`). The roots of the terms are computed by `g2_roots` and `b2_roots`, from
`⟨β, a^∨⟩` via Mathlib's `reflection_apply_root`.

**A pair in standard position.** `transport` moves the formula along `l`. Each term root is
`i β + j ε`, so its height is `i h(β) + j h(ε)` (`height_of_root_eq_combo`). Hence it is
positive, and componentwise increasing exponents give strictly increasing heights, hence
increasing positions.

**The rank-two cases.**
- *Commuting pairs.* The imported classifications `a1a1_coeffs`, `a2_coeffs`, `b2_coeffs` and
  `g2_coeffs` list the roots `m a + n c`. `noOpp_cone_of_coeffs` shows that `s₁ ≠ -ε₀` and
  that no `dS s₁ + dT ε₀` with `dS, dT ≥ 1` is a root, by `omega`.
- *Formulas.* The other cases use the standard formulas:
  - `G₂`, `s₁ = a`: `ε₀ = c` uses the first `G₂` formula; `ε₀ = a + c` the second;
    `ε₀ = 2 a + c` the third.
  - `G₂`, `s₁ = c`: `ε₀ = a` uses `CommRel.g2_reverse`; `ε₀ = 3 a + c` the fourth formula.
  - `B₂`, `s₁ = a`: `ε₀ = c` and `ε₀ = a + c` use the two `B₂` formulas.
  - `B₂`, `s₁ = c`: `ε₀ = a` uses `CommRel.b2_reverse`.
  - `A₂`: `ε₀ = c` uses the `A₂` formula.
- *Commutations in the reversed formulas.* These come from `pointsCommute_wordConj`: by
  `wordConj_weylFamily` the word conjugates are rescaled Weyl-family members, whose roots have
  no root in their cone.
- *The tie in `G₂`.* For `ε₀ = a + c`, the terms at `2 β + ε` and `β + 2 ε` have incomparable
  exponents. Their positions differ, since `q` is injective and `wordPerm l` is injective
  (`wordPerm_injective`). If the second comes first, the two terms are exchanged by
  `CommRel.swap`: their root groups commute.

**Moving a pair to standard position.** In `pairFormula_of_pos`:
- Two distinct `b'`-positive roots are linearly independent (Mathlib's
  `IsReduced.eq_or_eq_neg` and `IsPos.neg_iff_not`).
- The imported `exists_word_rankTwo` gives a word `l` in `b.support` and distinct simple roots
  `s₁`, `s₂` with `β = w_l(s₁)` and `ε = w_l(p₀ s₁ + q₀ s₂)`.
- Put `ε₀ = wordPerm l.reverse ε`. Its root is `p₀ s₁ + q₀ s₂` (`wordReflect_reverse`), and
  `wordPerm l ε₀ = ε` (`wordPerm_reverse`).
- Mathlib's `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'` and
  `Base.pairingIn_le_zero_of_ne` leave six possibilities for `(⟨s₁, s₂^∨⟩, ⟨s₂, s₁^∨⟩)`:
  - `(0, 0)` gives `A₁ × A₁`, and `(-1, -1)` gives `A₂`;
  - `(-1, -2)` and `(-2, -1)` give `B₂` with `s₁` short or long;
  - `(-1, -3)` and `(-3, -1)` give `G₂` with `s₁` short or long.

**The main theorem.**
- The hypotheses of `LocalSplitWeylCommutatorStatement` and the statement
  `LocalSplitRankOneNormalStatement`, applied to `G` and to `H`, give `IsNormalSimpleData` for
  both.
- `LocalSplitWeylConjugationStatement` gives `WeylConjugationRelations`.
- The imported `commutatorRelations_of_isUnivComm` reduces `CommutatorRelations` to common
  universal coordinates for every pair of positions `k < l`.
- Take `q = pos⁻¹` on positive roots. It is strictly monotone in the height, because `pos` is
  monotone in the height, and it is injective.
- `pairFormula_of_pos` for `β = pos k` and `ε = pos l` and `exists_common_isUnivComm` give the
  coordinates.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. The reduction of commutation relations to rank-two subsystems by Weyl conjugation
follows SGA 3, Exp. XXIII, Lemma 2.1.4 and its use of Exp. XXI, Proposition 3.5.4. Conrad,
*Reductive group schemes* (2014), Lemma 6.2.3 and Lemma 6.2.8, use the same reduction. Here
no homomorphism between the groups is given. The common Weyl-conjugation units of
`LocalSplitWeylConjugationStatement` take the role of the compatibility of a homomorphism
with conjugation. The rank-two constants are those of SGA 3, Exp. XXIII, 3.2–3.4, as
computed in the imported modules. The tie-breaking in type `G₂` and the bookkeeping of
positions are this module's own. The two statements assumed here are not proved in this
module, and the Isomorphism Theorem is not proved.
