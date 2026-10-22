# Existence and uniqueness of the supercuspidal support

Author: Worker 23.

This module states Zelevinsky's Proposition 1.10 for `GL_n` over every p-adic
field, in terms of the support relations of `Classification/SupercuspidalSupport`.
It contains three proposition definitions and no proofs.

- `Langlands.GLSupercuspidalEmbeddingStatement`: for every prime `p`, every p-adic
  field `F : PadicField.{uF} p`, every realization `T : F.TopologicalData`, every
  `n > 0` and every irreducible smooth representation `π` of `GL_n(F)` with
  carrier in `Type (max uF uV)`, there are cuspidal data `ρ_1, …, ρ_k` with
  `T.IsCuspidalSubrepresentation ρ π`. So `π` is an irreducible subrepresentation
  of `A_1 × ⋯ × A_k` for supercuspidal representatives `A_i` (carriers in
  `Type uV`) of the `ρ_i`, and the ranks of the `ρ_i` add up to `n`.
- `Langlands.GLSupercuspidalSupportUniquenessStatement`: for the same data, any two
  multisets `s` and `s'` of cuspidal data with `T.IsSupercuspidalSupport π s` and
  `T.IsSupercuspidalSupport π s'` are equal.
- `Langlands.GLSupercuspidalSupportStatement` is the conjunction of the two.

The two halves are separate closed propositions, so each can be the exact
target of its own proof task.

Together they give Zelevinsky's three claims. The embedding gives a list `ρ`
with `T.IsSupercuspidalEmbeddingSupport π (List.ofFn ρ)`, and hence, by the
published `IsSupercuspidalEmbeddingSupport.isSupercuspidalSupport`, a support. By
uniqueness this multiset is the support, and it equals the chosen
`T.supercuspidalSupport π` (`IsSupercuspidalSupport.eq_supercuspidalSupport`).
These consequences are explained here, not proved in this module.

## Source

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), 165–210
(registered source `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`), section 1.10,
printed p. 174 (PDF page 11):

> PROPOSITION. — Let ω ∈ Irr G_n. There exists a partition (n_1, …, n_r) of n and
> cuspidal representations ρ_i ∈ Irr G_{n_i} such that ω ∈ JH(ρ_1 × … × ρ_r). The
> multiset {ρ_1, …, ρ_r} on 𝒞 (cf. list of notations) is determined by ω; it is
> called the support of ω (notation supp ω = {ρ_1, …, ρ_r}). One can choose an
> ordering (ρ_{i_1}, …, ρ_{i_r}) of supp ω such that ω can be embedded into
> ρ_{i_1} × … × ρ_{i_r} (see [I], 2.5, 2.9).

| Zelevinsky 1980, 1.10 | Lean |
| --- | --- |
| ω ∈ Irr G_n | `π : SmoothRep ℂ (GeneralLinear n F.Carrier)`, `π.IsIrreducible`, `0 < n` |
| partition (n_1, …, n_r), cuspidal ρ_i ∈ Irr G_{n_i} | `ρ : Fin k → CuspidalDatum`, ranks summing to `n` (inside the relations) |
| ω can be embedded into ρ_{i_1} × … × ρ_{i_r} | `T.IsCuspidalSubrepresentation ρ π` in `GLSupercuspidalEmbeddingStatement` |
| ω ∈ JH(ρ_1 × … × ρ_r) | follows from the embedding (`IsCuspidalSubrepresentation.isCuspidalConstituent`) |
| the multiset is determined by ω | `GLSupercuspidalSupportUniquenessStatement` |

Zelevinsky's reference "[I], 2.5, 2.9" is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472 (registered source `bernstein-zelevinsky-1977-induced-i`):

- Theorem 2.5, printed p. 447 (PDF page 8): "Let ω ∈ Irr G. Then there exists a
  subgroup M < G and a cuspidal representation ρ ∈ Irr M such that ω can be
  embedded into i_{G,M}(ρ); in particular, ω is admissible."
- Example 2.7, printed p. 447: for `M = G_α`, `N = G_β` and
  `ρ = ⊗ ρ_i`, `ρ' = ⊗ ρ'_i`, "ρ ~ ρ' iff the sets (ρ_1, …, ρ_r) and
  (ρ'_1, …, ρ'_s) are equal up to a permutation."
- Theorem 2.9(a), printed p. 448 (PDF page 9): for cuspidal `ρ ∈ Irr M` and
  `ρ' ∈ Irr N`, "M ~ N and ρ ~ ρ'" is equivalent to "JH(π) ∩ JH(π') ≠ ∅", where
  `π = i_{G,M}(ρ)` and `π' = i_{G,N}(ρ')`.

## Relation to the published Levi-level statements

Worker 14's published `Langlands.CuspidalSupport.PadicCuspidalInductionTheorems`
(`CuspidalSupport/NormalizedCuspidalInductionStatement`) states these BZ77
theorems at the level of a standard Levi. In it:

- `CuspidalEmbeddingTheorem` embeds `π` into the normalized induction of an
  irreducible Levi-cuspidal representation `σ` of `B.Levi`;
- `CuspidalInductionAssociationTheorem` makes association of two such inducing
  data equivalent to having a common irreducible subquotient.

The present statements are the multiset form of Zelevinsky 1.10. Deriving them
from the Levi-level statements needs further steps that neither module states:

- an irreducible Levi-cuspidal `σ` is an external tensor product of supercuspidal
  representations of the blocks;
- the induction from `B.Levi` agrees with the published product induction
  `T.cuspidalProductInduced`;
- association of tensor products is a permutation of the factors (BZ77 2.7);
- the supercuspidal predicate of `Classification/Supercuspidal`, which includes
  every conjugate radical, agrees with Levi cuspidality on a single block. The
  published `Langlands.CuspidalSupport.PadicCuspidalityComparisonTheorems`
  (`CuspidalSupport/CuspidalityComparisonStatement`) states this comparison.

This module makes no claim about the relation between the two formulations.

## Universes and scope

The statements quantify `p`, the field, the realization and `n > 0` inside the
proposition. The universes `uV` (supercuspidal factors) and `uF` (the field) are
parameters of the definitions, so a proof must work for all of them. The
represented `π` has carriers in `Type (max uF uV)`, the universe of the
published product induction. No admissibility or finite length is assumed for
`π`; Bernstein and Zelevinsky derive admissibility from Theorem 2.5. The
statements are expected to hold in every universe because every irreducible
smooth representation of `GL_r(F)` has countable dimension and so has a
realization with carrier in `Type uV`. That is a remark for provers, not part of
the statement.
