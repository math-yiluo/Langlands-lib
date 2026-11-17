# Common rescalings along words, rank-two Weyl actions and braid relations

This module provides the single-group and two-group tools that the proof of
`LocalSplitWeylConjugationStatement` in `LocalSplitWeylChains` and
`LocalSplitWeylConjugationReduction` uses. It imports the published modules
`LocalSplitWeylCommutatorReduction`, `LocalRootParametrizationRigidity` and
`LocalSplitFieldComparison`. It contains no `Prop`-valued statement for the Library; its
definitions `UnivRel`, `PartnerUnique` and `PartnerRescales` are `Prop`-valued predicates used as
interfaces.

Notation. `R` is a commutative ring, `G`, `H` are group schemes over `Spec R`, `P` is a root
datum on `I → ℤ`, `b` a base, `W` words for `b`, `u : J → (𝔾ₐ ⟶ G)` and `u' : J → (𝔾ₐ ⟶ H)`.
`n_a = rootWeylPoint P u a = weylPoint (u a) (u (-a))`, where `-a` is the index
`P.reflectionPerm a a`. `wordConj P u l w` is conjugation of `w` along the word `l`. The head
letter of `l` is applied last. `v = weylFamily P W u` is the Weyl family. `κ ≫ w` abbreviates
`scaleHom κ ≫ w`. `IsNormalSimpleData i P b W u` is the published bundle of hypotheses: `G` is
reductive, `i` is fibrewise maximal, `P` is a fibrewise root datum, `u` gives root
parametrizations at `±a` for simple `a`, the points `n_a` are Weyl points for `s_a`, `W` is
descending, and `u` is rank-one normal at every simple root.

## Basic tools (section `Basic`)

- `signUnit R k : Rˣ` is the image of `(-1)^k`. Lemmas: `signUnit_val`, `signUnit_add`,
  `signUnit_neg`, `signUnit_even`, `signUnit_odd`, `signUnit_mul_self`, `negOnePow_smul_eq`.
- `baseTest R` is `Spec R` over itself. `baseScalar_baseTest_injective` and
  `baseScalar_baseTest` describe its scalars.
- `eq_scaleHom_of_base` (rigidity at the base point). Let `R` be local and `G` have affine
  structure morphism. If `w` and `z` parametrize the same root of a fibrewise root datum and
  `w(1) = z(κ)` over `baseTest R`, then `w = κ ≫ z`.
- `wordBase u l` is the product of the Weyl points of the letters of `l`.
  `wordConj_eq_innerIso` shows `wordConj P u l w = w ≫ Ad(wordBase u l)`.
  `wordConj_congr_of_wordBase` turns equal products into equal conjugations.
- `wordConj_sq`: if `u` is rank-one normal at `a`, then for every parametrization `w` of a root
  `β`, `wordConj P u [a, a] w = signUnit R ⟨β, a^∨⟩ ≫ w`.

## Common rescalings (section `Univ`)

`UnivRel P u u' l w₁ w₂ z₁ z₂` says: for some unit `κ`,
`wordConj P u l w₁ = κ ≫ w₂` and `wordConj P u' l z₁ = κ ≫ z₂`.
Lemmas:
- `UnivRel.of_eq` and `UnivRel.refl` take `κ = 1`.
- `UnivRel.trans` composes rescalings along `l₁` and then `l₂` into one along `l₂ ++ l₁`.
- `UnivRel.cancel` recovers the `l₂` part from the composite and the `l₁` part.
- `UnivRel.rescale` rescales both targets by a common unit. `UnivRel.congr_word` changes the
  word when both conjugations agree.
- `UnivRel.inv`: from rescalings along `[k]` and along `[k, k]`, one along `[k]` in the opposite
  direction.
- `scaleHom_cancel`: `κ ≫ X = Y` implies `X = κ⁻¹ ≫ Y`.

## Rank two (section `RankTwo`; `R` local, affine structure morphisms)

- `pairingIn_eq_pairing`: for root data over `ℤ`, `pairingIn ℤ` equals `pairing`.
- `IsNormalSimpleData.isRootParametrization_wordConj`: conjugating a parametrization of `β`
  along a word `l` in simple letters gives a parametrization of `w_l(β)`.
- `univRel_sq`: given normal data `u`, `u'` and parametrizations of the same root `β` in `G` and
  `H`, `UnivRel` along `[k, k]` from each to itself, for simple `k`. The common unit is
  `signUnit R ⟨β, k^∨⟩`.
- `UnivRel.inv_of_param`: inversion of one-letter rescalings between root parametrizations.
- `IsNormalSimpleData.wordConj_fix` (T1). Let `β` satisfy `⟨β, c^∨⟩ = 0` for a simple `c`.
  Suppose `β ≠ ∓c`, and no root equals `dS β + dT c` or `dS β - dT c` with `dS, dT ≥ 1`. Then
  `wordConj P u [c] w = w` for every parametrization `w` of `β`.
  `IsNormalSimpleData.wordConj_fix_of_coeffs` derives the same conclusion from coefficients
  in a basis `c`, `j` of simple roots and a classification of the coefficients of roots.
- `IsNormalSimpleData.wordConj_a2` (T2). For simple `c ≠ j` with Cartan entries `-1, -1`:
  `wordConj P u [c] (u j) = (-1) ≫ wordConj P u [j] (u c)`.
- `IsNormalSimpleData.wordConj_b2` (T3). For simple `a` short and `c` long (entries
  `⟨a, c^∨⟩ = -1`, `⟨c, a^∨⟩ = -2`):
  `wordConj P u [a] (wordConj P u [c] (u a)) = (-1) ≫ wordConj P u [c] (u a)`.

## Weyl points (section `WeylPoints`)

- `IsWeylPoint.mul'`: if `n` is a Weyl point for `f` and `m` one for `g`, then `n * m` is one
  for `f.trans g`.
- `IsWeylPoint.inv'`: `n⁻¹` is a Weyl point for `f.symm`.
- `weylPoint_innerIso`:
  `weylPoint (w ≫ Ad x) (z ≫ Ad x) = x * weylPoint w z * x⁻¹`.
- `isWeylPoint_wordBase_conj`: if every letter of `l` and `k` give Weyl points `n_j` for `s_j`,
  then `wordBase u l * n_k * (wordBase u l)⁻¹` is a Weyl point for `s_{w_l(k)}`.

## Braids (section `Braids`)

- `PartnerUnique P G i` says: for every root `a`, a parametrization `xp` of `a` and
  parametrizations `xm`, `xm'` of `-a` such that `weylPoint xp xm` and `weylPoint xp xm'` are
  Weyl points for `s_a` satisfy `xm' = xm`.
- `wordBase_append`: products along `l ++ l'` multiply.
- `IsNormalSimpleData.wordBase_braid`. Assume `PartnerUnique P G i`, a word `l` in simple
  letters and simple `k`, `k'` with `w_l(k) = k'` and `wordConj P u l (u k) = u k'`. Then
  `wordBase u (l ++ [k]) = wordBase u (k' :: l)`.

## Negative roots (section `Negative`)

- `PartnerRescales P G i` says: for every root `a`, parametrizations `xp` of `a` and `xm` of
  `-a` with `weylPoint xp xm` a Weyl point for `s_a`, and every unit `κ`,
  `weylPoint (κ ≫ xp) (κ⁻¹ ≫ xm)` is a Weyl point for `s_a`.
- `IsWeylPoint.conj_reflection`: conjugating a Weyl point for `s_k` by one for `s_j` gives one
  for `s_{s_j k}`.
- `IsNormalSimpleData.wordConj_simple_self`: `wordConj P u [s] (u s) = (-1) ≫ u (-s)` for simple
  `s`.
- `oppositeFamily W u g = wordConj P u (W g).word (u (-(W g).simple))`. `reflectionPerm_neg_self`
  states `-(-g) = g` on indices.
- `IsNormalSimpleData.weylFamily_neg`: for positive `g`, `v (-g) = (-1) ≫ oppositeFamily W u g`.
- `IsNormalSimpleData.isRootParametrization_opposite`: `oppositeFamily W u g` parametrizes
  `-g`.
- `IsNormalSimpleData.isWeylPoint_opposite`: `weylPoint (v g) (oppositeFamily W u g)` is a Weyl
  point for `s_g`.
- `IsNormalSimpleData.conj_neg`. Assume `PartnerUnique P G i` and `PartnerRescales P G i`. Let
  `c` be simple and `α`, `s_c α` positive. If `wordConj P u [c] (v α) = κ ≫ v (s_c α)`, then
  `wordConj P u [c] (v (-α)) = κ⁻¹ ≫ v (s_c (-α))`.

## Rank-two conjugations (section `RankTwoConj`)

- `neg_one_units_mul_inv`: `(-1) * (-1)⁻¹ = 1` for units.
- `IsNormalSimpleData.conj_a2`: in type `A₂`, `wordConj P u [c, j] (u c) = u j`.
- `IsNormalSimpleData.conj_b2`: in type `B₂` with `a` short and `c` long,
  `wordConj P u [a, c, a] (u c) = u c`.
- `IsNormalSimpleData.conj_g2_fix` and `IsNormalSimpleData.conj_g2`: in type `G₂` with `a`
  short and `c` long, `n_a` fixes `wordConj P u [c] (wordConj P u [a] (u c))`, and
  `wordConj P u [a, c, a, c, a] (u c) = u c`.

## Proofs

Map equalities that come from formulas on affine tests are obtained by `eq_scaleHom_of_base`.
The published rigidity theorem `IsRootParametrization.existsUnique_unit_of_rootDatum` gives a
unit `κ₀` with `w = κ₀ ≫ z`. Injectivity of `rootPoint z` over the base and of `baseScalar`
then forces `κ₀ = κ`.

- T1: the family `v` is updated at `-c` by `u (-c)` and at `β` by `w`. The published
  `rootPoint_commute_of_forall_ne` makes `w(1)` commute with `u_c(1)` and `u_{-c}(-1)`, hence
  with `n_c = u_{-c}(-1) u_c(1) u_{-c}(-1)`.
- T2: the published `a2_constants`, applied to `(c, j)` and to `(j, c)` at `x = y = 1`. The two
  commutators are inverse to each other, so `(n_c u_j n_c⁻¹)(1) = (n_j u_c n_j⁻¹)(-1)`.
- T3: the third conclusion of the published `b2_constants` at `x = 1`.
- `wordConj_sq` is the published `conj_sq_rootPoint` (`n_a² = a^∨(-1)`), on all tests.
- The Weyl-point lemmas pass through `IsNormalizingPoint` (`IsWeylPoint.isNormalizingPoint`,
  `isWeylPoint_of_isNormalizingPoint`) and use `exponentHom_comp`. The word lemma is an
  induction with Mathlib's `reflection_reflectionPerm`.
- `wordBase_braid`: `x n_k x⁻¹ = weylPoint (wordConj l (u k)) (wordConj l (u (-k)))` by
  `weylPoint_innerIso`. This equals `weylPoint (u k') (wordConj l (u (-k)))`, a Weyl point for
  `s_{k'}`. Since `n_{k'}` is one too, `PartnerUnique` gives `wordConj l (u (-k)) = u (-k')`.
  Hence `x n_k x⁻¹ = n_{k'}`.
- `conj_neg`: by the descending-word rule for negative roots, `v(-α)` is
  `wordConj (W α).word (wordConj [s] (u s))`, which `wordConj_simple_self` turns into
  `(-1) ≫ oppositeFamily W u α`. Conjugation by `n_c` turns the Weyl point of
  `(v α, oppositeFamily α)` into one for `s_β`, `β = s_c α`, with first factor `κ ≫ v β`.
  `PartnerRescales` makes `(κ ≫ v β, κ⁻¹ ≫ oppositeFamily β)` another such pair, and
  `PartnerUnique` identifies the two second factors.
- `conj_a2`: T2 and `wordConj_sq` (sign `(-1)^{-1}`).
- `conj_b2`: T1 fixes `wordConj [a] (u c)`, a parametrization of `c + 2a`, under `n_c`;
  `wordConj_sq` then gives sign `(-1)^{-2} = 1`.
- `conj_g2`: T1 fixes the parametrization of `2c + 3a` under `n_a`; two squares give signs
  `(-1)^{-1}` and `(-1)^{-3}`.

## Provenance

The rank-two Weyl actions and the braid relations of the simple Weyl points correspond to
SGA 3, Exp. XXIII, 3.1.2, 3.2.1, 3.3.1 and 3.4.1. There they are explicit computations in the
Chevalley groups. Here they are derived from the published rank-two commutator constants and
from partner uniqueness. The treatment of negative roots via partner uniqueness and inverse
rescaling, the common-rescaling calculus `UnivRel`, and rigidity at the base point are this
module's own devices for comparing two groups without a homomorphism between them.
