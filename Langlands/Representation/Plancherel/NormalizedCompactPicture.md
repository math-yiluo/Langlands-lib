# Fixed compact pictures for actual normalized induction

Let `G` be a locally compact nonarchimedean group and let `P`, `M`, `U` be
actual subgroups with a semidirect decomposition `h : P = M ⋉ U`. Assume
`U` and `P` are closed. Let `K` be a compact open subgroup and assume the
explicit structural factorization

\[
  \forall g\in G,\quad g=pk\quad(p\in P,\ k\in K).
\]

For a canonical complex smooth representation `A` of `M`, this module
constructs the compact picture of actual normalized induction. It also
identifies every actual unramified twist with the same compact carrier.
All equivalences intertwine the actual right action of `K`.

## Provenance and retained hypotheses

This is a derived prerequisite for Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, VI.1, printed
pp.295–296 (PDF pp.61–62), especially the restriction identification on
p.296. The source uses induction from `P × P` and the tensor of an inducing
representation with its smooth contragredient. This module supplies the
single-group normalized restriction and unramified-twist comparison.
Its actual subgroup formulation, inverse formulas and naturality laws are
derived content.

The ambient-group, character-index and coefficient-carrier universes are
independent; the coefficient field is `ℂ`. The representation carriers and
smooth induction are the existing `SmoothRep` and `SmoothFunctions`.
The action on `P` is the existing full-parabolic normalization

\[
  \sigma_A(p)v=\delta_U(p)^{1/2}A(r(p))v,
\]

where `r = h.projection : P →* M` is the actual Levi projection and
`δ_U` is the Haar modulus of conjugation on `U`. No alternative
representation category or assumed compact-picture equivalence is introduced.

For the unramified comparison, let `ν : I → (M →* ℝ≥0ˣ)` be a family of
continuous positive characters and suppose the actual projection `r` is
continuous. An unramified character here is the existing continuous complex
unit-valued character trivial on the common kernel of `ν`. To specialize to
Waldspurger's group, `ν` must be the family of absolute values of all rational
algebraic characters. No rational-point realization or complex torus
structure is asserted. The construction works for all these unramified
characters; it does not need their unitary restriction.

Closedness, compactness and `G = P K` are explicit structural hypotheses,
not representation-theoretic conclusions. The general reductive realization
of these data, the source's Levi-inflated normalization comparison, product
coefficient pictures, finite self-twist descent, smooth parameter families
and the analytic Plancherel theorem remain separate obligations. No
admissibility, irreducibility, quotient measure, second countability or
compact-quotient hypothesis is needed for this unit.

## The fixed carrier and half-modulus removal

Write `J = P.comap K.toSubgroup.subtype`, the literal subgroup `P ∩ K`
inside `K`. Its canonical homomorphism into `P` is
`K.toSubgroup.subtype.subgroupComap P`. The definition
`compactPictureInducingRepresentation h K A` composes `A` with this
homomorphism and `r`, without any normalizing character.
`CompactInductionPicture h K A` is the existing space of smooth functions
on `K` with covariance

\[
  f(jk)=A(r(j))f(k),\qquad j\in J,\ k\in K.
\]

Smoothness means that a single open subgroup of `K` fixes the entire
function under right translation.

`Langlands.HaarModulus.closedHalfCharacter_eq_one_of_mem_compactOpen`
proves `δ_U(p)^(1/2) = 1` whenever `p ∈ P` also belongs to `K`.
It first views `p` in `conjOpenSubgroup P K 1`. This intersection is compact
in `P` because `P` is closed and `K` is compact, by
`isCompact_conjOpenSubgroup`. The full positive modulus character has open
kernel and hence is continuous by `Weil.continuous_of_open_kernel`.
`RankinSelberg.LastRowReduction.eq_one_of_isCompact` makes that character
trivial on the compact intersection. Finally the existing identity
`halfCharacter_ker` identifies its kernel with that of the positive
half-character. Thus triviality of the normalizing character is proved.

`normalized_compactPictureInducing_eq` applies this pointwise to prove
equality of the actual normalized inducing action on `J` with
`compactPictureInducingRepresentation`.

`normalizedInductionCompactEquiv` composes the existing
`openSubgroupInductionEquiv` under `G = P K` with smooth induction of this
equality of actions. Its forward map is literally restriction:

\[
  (\mathcal R_A f)(k)=f(k).
\]

`normalizedInductionCompactEquiv_eval` records this formula. Its inverse
is the covariance extension already proved well-defined and globally
smooth by the open-subgroup equivalence:

\[
  (\mathcal R_A^{-1}f)(pk)=\sigma_A(p)f(k).
\]

This holds for every factorization, as exposed by
`normalizedInductionCompactEquiv_symm_mul`.

## Removal of an actual unramified twist

For `χ : unramifiedCharacters ν`, the existing
`unramifiedCharacter_isOpen_ker` supplies the smooth twist
`A.twist χ.val.toMonoidHom …`. Its actual action is
`χ(m) • A(m)`.

`unramified_compactPictureInducing_eq` proves that this twist has exactly
the original action on `J`. For `j ∈ J`, compactness of the same actual
intersection and continuity of `r` and of all `ν i` allow
`unramifiedPullback_eq_one_of_mem_conjOpenSubgroup` to prove
`χ(r(j)) = 1`. Equality of the actions then follows by linear-map
extensionality and `one_smul`. This triviality is proved from the
unramified-kernel condition, rather than assumed as additional input.

`unramifiedNormalizedInductionCompactEquiv` composes
`normalizedInductionCompactEquiv` for the twisted inducing object with
smooth induction of that action equality. Its target is always
`CompactInductionPicture h K A`, independently of `χ`. The evaluation and
inverse evaluation theorems give

\[
  (\mathcal R_{\chi,A}f)(k)=f(k),\qquad
  (\mathcal R_{\chi,A}^{-1}F)(pk)=\sigma_{A\otimes\chi}(p)F(k).
\]

Neither a tensor decomposition of the function nor a choice of a
representation equivalence between `A` and its twist is needed.

## Representative compatibility

For an actual equivalence `e : A.representation.Equiv B.representation`,
`compactInductionPictureEquiv h K e` is smooth induction of `e`
restricted through the actual Levi projection. It sends `F(k)` to
`e(F(k))`, as recorded by its evaluation theorem. The source and target
coefficient-carrier universes are independent.

`normalizedInductionCompactEquiv_natural` says that inducing `e` and
then restricting agrees with restricting and then applying this
pointwise compact-picture map.
`unramifiedNormalizedInductionCompactEquiv_natural` gives the same
commuting identity after twisting both representatives by the same `χ`;
the induced equivalence is the existing `twistEquiv`, whose underlying
linear equivalence is still `e`. Both equalities follow by extensionality
of the actual induced functions and literal pointwise evaluation.
