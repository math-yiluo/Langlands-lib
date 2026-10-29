# Towers of block embeddings for unequal-rank rigidity

Module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicTower`,
namespace `Langlands.RankinSelberg.UnequalRankTower`.

This is a helper module for the proof of
`Langlands.RankinSelberg.UnequalRankMirabolicPairingRigidityStatement`
(JPSS 1983, Section 2.11, Lemma on printed p.399). It states no new
proposition. Its constructions are internal. JPSS argue on the side of `η`
through the classification of irreducible representations and finite length
of the restriction to a mirabolic subgroup. The Lean proof does not use
that argument. It repeatedly applies the unnormalized
Bernstein–Zelevinsky functor `Φ⁻` on both sides of a mirabolic pairing.
This module records how the quotients of the `GL_(N+1)`-representation `η`
that appear on the second side are linked to `η` itself.

Notation: `P_j = mirabolic j F ⊂ GL_(j+1)` (radical `F^j`, Levi `GL_j`),
`U_(N+1) = upperUnipotent (N + 1) F`, and
`θ_N = standardCharacter ψ N`, the character `u ↦ ψ(Σ_i u_(i,i+1))` of `U_(N+1)`.
The field is an arbitrary field `F`. Only the `Character` and `Tower`
sections use a topology on `F`, through `standardCharacter`.

## Matrices

- `towerEmbedding (h : j ≤ N) : GL_(j+1) →* GL_(N+1)` is the block embedding
  `g ↦ diag(g, I_(N-j))`. It is the published `appendIdentity j (N - j)` followed by
  `GeneralLinear.reindex` along `finCongr (j + (N - j) + 1 = N + 1)`.
  `towerEmbedding_entry` gives its entries:
  `g_(a,b)` if `a, b ≤ j`, `0` if exactly one of `a, b` is `≤ j`, and `δ_(a,b)` otherwise.
- `radicalElement_entry` gives a uniform entry formula
  `u(v)_(a,b) = δ_(a,b) + [a < n ∧ b = n] v_a` for the published radical element
  `Mirabolic.radicalElement v` of `P_n`. `levi_entry` gives the entries of
  `Mirabolic.levi g = diag(g, 1)`.
- `towerEmbedding_self`: `towerEmbedding (le_refl N) g = g`.
- `towerEmbedding_levi (h' : j + 1 ≤ N) (h : j ≤ N) g`:
  `towerEmbedding h' (levi g) = towerEmbedding h g`, i.e. embedding `diag(g, 1)`
  one level higher is the same as embedding `g`.
- `towerEmbedding_radical_entry` computes the entries of
  `diag(u(c), I_(N-j))` for `c : Fin j → F`. `towerEmbedding_radical_mul_entry`
  shows that left multiplication by this element adds `c_a` times row `j` to
  row `a` for each `a < j`:
  `(diag(u(c), I) · g)_(a,b) = g_(a,b) + [a < j] c_a g_(j,b)`.
- `towerEmbedding_radical_mem` shows that the embedded radical element lies in
  `U_(N+1)`. `towerRadical h c` is this element as a member of `U_(N+1)`, with
  `towerRadical_val`, `towerRadical_add` (`c ↦ towerRadical h c` is additive)
  and `towerRadical_zero`.
- `IsLeading j u` says that the leading `(j+1)`-square block of `u ∈ U_(N+1)`
  is the identity. `isLeading_zero`: every `u` is leading at level `0`.
- `towerColumn (h : j + 1 ≤ N) u : Fin (j + 1) → F` reads the entries
  `u_(a, j+1)`, `a ≤ j`, of column `j+1` above the diagonal.
- `exists_towerRadical_mul`: if `IsLeading j u` and `j + 1 ≤ N`, then
  `u = towerRadical h (towerColumn h u) * u'` with `IsLeading (j+1) u'`.
  The witness is `u' = towerRadical h (-towerColumn h u) * u`. Its entries in
  the leading `(j+2)`-block are computed with
  `towerEmbedding_radical_mul_entry`; the first factor clears column `j+1`
  above the diagonal.

## Character

- `standardCharacter_towerRadical (h : j + 1 ≤ N) (c : Fin (j + 1) → F)`:
  `θ_N(towerRadical h c) = ψ(c_j)`. The only nonzero superdiagonal entry of
  `diag(u(c), I)` is the entry `(j, j+1)`, which equals `c_j`.
- `standardCharacter_eq_mul`: for a factorization
  `u = towerRadical h (towerColumn h u) * u'`,
  `θ_N(u) = ψ(u_(j,j+1)) θ_N(u')`. This follows from multiplicativity of `θ_N`.

## Tower data

For a representation `η` of `GL_(N+1)` on `W`, `h : j ≤ N`, a representation
`ρ` of `P_j` on `A` and a linear map `q : W → A`, the structure
`IsTower ψ η h ρ q` has three fields:

- `surjective`: `q` is surjective;
- `levi`: `q(η(diag(p, I_(N-j))) w) = ρ(p) q(w)` for `p ∈ P_j` and `w ∈ W`;
- `unipotent`: `q(η(u) w) = θ_N(u) q(w)` for every `u ∈ U_(N+1)` with
  `IsLeading j u` and every `w ∈ W`.

Results:

- `eq_one_of_isLeading`: a matrix leading at level `N` is the identity.
- `isTower_top ψ η`: `IsTower ψ η (le_refl N) (η.comp (mirabolic N F).subtype) id`.
  The restriction of `η` to `P_N`, with the identity map, is a tower datum at
  the top level.
- `IsTower.descend (h' : j + 1 ≤ N) hT ρ' π hπ hsucc hrad`: let
  `hT : IsTower ψ η h' ρ q` be a tower datum at level `j+1`. Let
  `π : A → B` be a surjective linear map and `ρ'` a representation of
  `P_j` on `B`. Suppose
  `π(ρ(successor p) x) = ρ'(p) π(x)` (`hsucc`) and
  `π(ρ(u(c)) x) = ψ(c_j) π(x)` for the radical elements `u(c)`, `c : Fin (j+1) → F`,
  of `P_(j+1)` (`hrad`). Then `IsTower ψ η _ ρ' (π ∘ q)` is a tower datum at
  level `j`. This applies to the quotient map `phiMinusQuotient` of `Φ⁻`.
  The Levi law uses `towerEmbedding_levi`, since `successor p = levi p`. The
  unipotent law factors a level-`j` leading matrix with
  `exists_towerRadical_mul`. It then applies the level-`(j+1)` unipotent law to
  `u'`, the Levi law to the embedded radical element, `hrad`, and
  `standardCharacter_eq_mul`.
- `IsTower.functional_apply`: at level `0`, every leading condition holds
  (`isLeading_zero`). So for each functional `ℓ` on `A`,
  `ℓ(q(η(u) w)) = θ_N(u) ℓ(q(w))` for every `u ∈ U_(N+1)`.
- `IsTower.hasFunctional`: a nonzero functional `ℓ` on a level-`0` tower
  quotient gives `Whittaker.HasFunctional (N := upperUnipotent (N + 1) F)
  (θ := standardCharacter ψ N) η`, with witness `ℓ ∘ q`, which is nonzero
  because `q` is surjective.

## Provenance

The covariance groups and characters are those of JPSS (1983), Section 2.11,
(2.11.2) and (2.11.4), printed pp.398–399 (literature ID
`jpss-1983-rankin-selberg`). The tower data, the factorization
`exists_towerRadical_mul` and the descent lemma are internal constructions of
this proof route. JPSS have no corresponding statement. They replace the
source's use of finite length of `η` restricted to the mirabolic subgroup
(in the proof of the Lemma, printed pp.399–403) by an explicit iteration of `Φ⁻` on the `η` side. Author: Worker 895.
