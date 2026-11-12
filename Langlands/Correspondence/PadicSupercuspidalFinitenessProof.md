# Bernstein–Zelevinsky finiteness of supercuspidal classes over p-adic fields

Author: Worker 4803. Module `Langlands.Correspondence.PadicSupercuspidalFinitenessProof`,
namespace `Langlands.Henniart.CompactOpenFiniteness`. Universes: `uK` (p-adic fields)
and `uV` (supercuspidal carriers), independent; the generic lemmas also use `uG`
(groups) and `uW` (a second carrier).

## Statement: `PadicSupercuspidalCompactOpenFinitenessStatement.{uK, uV}`

For every prime `p` and every p-adic field `K : PadicField.{uK} p`, equipped with the
topology, valuative relation and local-field structure of
`K.canonicalTopologicalData`, every `n : ℕ`, every character
`χ : Z(GL_(n+1)(K)) →* ℂˣ` of the centre and every open subgroup `N` of
`GL_(n+1)(K)` that is compact, the set
`GeneralLinear.SupercuspidalClass.centralFixedStratum.{uK, uV} χ N.toSubgroup` is
finite. That set consists of the isomorphism classes of supercuspidal
representations of `GL_(n+1)(K)` on carriers in `Type uV` (irreducible smooth complex
representations that are supercuspidal) which have central character `χ` and a
nonzero `N`-fixed vector.

It is proved, with no hypotheses, by `padicSupercuspidalCompactOpenFiniteness`.

Comparison with the Library statement
`Henniart.SupercuspidalCompactOpenFinitenessStatement.{uF, uV}` (module
`SupercuspidalFinitenessStatement`, the target of Task 5585): the conclusion is the
same, but that statement quantifies over every nonarchimedean local field `F` with
arbitrary instances, including fields of positive characteristic. This one covers
only p-adic fields with their canonical structure, the case used by Henniart's route
(every field in `SupercuspidalCorrespondenceStatement` and in Henniart's candidate
sets is a `PadicField`). It does not prove the Library statement.

## Other results

- `centralFixedStratum_finite K n χ N hN`: the same finiteness for one p-adic field,
  stated with this module's local instances (the canonical ones).
- `centralLevelStratum_finite K n χ b`: for every bound `b : ℕ`,
  `SupercuspidalClass.centralLevelStratum χ b` (central character `χ` and first
  nonzero newvector level at most `b`) is finite. This is the bounded-level form,
  the p-adic case of `Henniart.SupercuspidalBoundedLevelFinitenessStatement`.

## Provenance

Bernstein and Zelevinsky (1976), Corollary 4.15, printed p. 41: for a congruence
subgroup `N` of `G = GL(n, F)` and a character `θ` of the centre `Z`, `G` has only
finitely many non-isomorphic irreducible cuspidal representations `ω` with
`ω(ε_N) ≠ 0` and `ω(z) = θ(z)` on `Z`. They deduce it "from 4.14 with the help of
3.20b), 3.21, and 3.29" and give no further argument. BZ76 3.18, printed p. 34,
calls a representation cuspidal if it is admissible and all its Jacquet modules for
proper partitions vanish; for `GL_(n+1)` this is the Library's `IsSupercuspidal`
(admissible, with vanishing coinvariants for every proper standard parabolic and its
conjugates). A nonzero `N`-fixed vector means `ω(ε_N) ≠ 0`. Every compact open
subgroup `N` contains a congruence subgroup `N'`, and an `N`-fixed vector is
`N'`-fixed, so the corollary for `N'` implies the statement for `N`. Thus the
statement above is Corollary 4.15 for p-adic `F` and rank `n + 1`. The Lean proof
does not pass through congruence subgroups: the Library form of 4.14 already allows
any compact open subgroup of `G°`.

The ingredients, with their Library forms:

- BZ76 3.20, printed p. 34: `G° = {g : |det g| = 1}` is open and normal, `G/G°` is
  abelian and `G°Z` has finite index in `G`
  (`determinantUnitQuotient_mul_comm`, `determinantUnit_sup_center_finiteIndex`).
- BZ76 3.21 (Harish-Chandra), printed p. 34: a quasi-cuspidal representation
  restricts to `G°` with compactly supported matrix coefficients
  (`leviHarishChandraTheorem`).
- BZ76 3.26, printed p. 36: the restriction of an irreducible representation to
  `G°` is a finite direct sum of irreducible ones
  (`FiniteRestriction.leviFiniteRestriction`).
- BZ76 3.29, printed p. 36: irreducible `ω, ω'` whose restrictions to `G°` share an
  irreducible submodule satisfy `ω' ≅ ψω` for a character `ψ` trivial on `G°`
  (`exists_twistIntertwiningMap_of_restrictedHom_nonzero` and
  `twistEquivOfNonzeroIntertwiner`, modules `CuspidalSupport/NormKernelTwistAlgebra`
  and `CuspidalSupport/NormKernelTwistElementary`).
- BZ76 Theorem 4.14 (proof 4.16), printed p. 41: for a compact open subgroup `L` of
  `G°`, only finitely many classes of irreducible representations of `G°` with
  compactly supported coefficients have a nonzero `L`-fixed vector
  (`CuspidalSupport.compactCoefficientFixedLevelFiniteness`, the published p-adic
  product-Levi form; used for the one-block Levi).

The averaging step and the passage from a constituent to an intertwiner are the
routine details that BZ76 leaves to the reader.

## Proof

All groups act on complex vector spaces. `GL_(n+1)(K)` is handled through the
one-block Levi `fullBlock n` (`LeviAdmissibility.oneBlock (n + 1)`), whose Levi
embedding onto `GL_(n+1)(K)` is a bijective homeomorphism
(`singleBlock_leviEmbedding_surjective`, `singleBlockLeviEquivContinuous`).
`unitGroup K n` is `G°` in that Levi (`determinantUnitSubgroup`), `leviRep` pulls a
representation back to the Levi and `unitRep` restricts it to `G°`.
`twistKernel K n = G° ⊔ Z` and `twistQuotient K n` is the quotient by it.

Generic lemmas (any group `G`):

- `inclusion`, `projectionOnto`: the inclusion of an invariant subspace and the
  projection onto it along an invariant complement, as intertwiners (the latter
  from the published `equivariantProjection`).
- `isCompl_toSubmodule`: complements of subrepresentations are complements of their
  submodules.
- `exists_ne_zero_of_equiv`: a nonzero complemented invariant subspace of `ρ`
  equivalent to an invariant subspace of `σ` gives the nonzero intertwiner
  `inclusion ∘ E ∘ projection : ρ → σ`.
- `finite_monoidHom_units`: a finite group `Q` has finitely many homomorphisms to
  `ℂˣ`, since each takes values in the `|Q|`-th roots of unity.
- `isSmooth_subrepresentation`: invariant subspaces of smooth representations are
  smooth.
- `exists_fixedVectors_ne_bot`: if invariant subspaces `S_1, …, S_m` span a smooth
  `ρ`, and `L` is a compact open subgroup with `ρ^L ≠ 0`, then some `S_i^L ≠ 0`.
  The averaging map `P` over `L` (`Compact.CharZero.averageMap`) commutes with the
  inclusions; if every `S_i^L` were zero, `P` would vanish on each `S_i`, hence on
  their span `V`, whereas `P` is the identity on `ρ^L`.
- `IsConstituent hρ c`: `c` is the class of an irreducible invariant subspace with
  compact coefficients and an invariant complement.
- `exists_ne_zero_of_isConstituent`: two representations with a common constituent
  class have a nonzero intertwiner between them (`ofRep_eq_iff` gives the
  equivalence, then `exists_ne_zero_of_equiv`).

p-adic part (`K` fixed, local instances from `K.canonicalTopologicalData`):

- `finite_twistQuotient`: `GL_(n+1) / G°Z` is finite (BZ76 3.20 b)).
- `unitLevel K n N`, `isCompact_unitLevel`: the preimage of `N` in `G°`, an open
  subgroup, compact because the Levi embedding is a homeomorphism and `G°` is closed.
- `isSmooth_leviRep`, `isSmooth_unitRep`, `isIrreducible_leviRep`: pullback along a
  continuous map preserves smoothness, and pullback along a surjection preserves
  irreducibility.
- `leviEmbedding_mem_center`: the embedding maps the centre into the centre.
- `fixedVectors_unitRep_ne_bot`: a nonzero `N`-fixed vector is fixed by
  `unitLevel K n N`.
- `exists_isConstituent`: a supercuspidal `A` whose restriction to `G°` has a nonzero
  `L`-fixed vector has a constituent class in
  `CompactCoefficientClass.fixedStratum L`. Its pullback to the Levi is irreducible
  and quasi-cuspidal (`singleBlockCuspidalityClause`), so its restriction to `G°` has
  compact coefficients (`leviHarishChandraTheorem`, BZ76 3.21) and is semisimple and
  spanned by finitely many irreducible subrepresentations
  (`leviFiniteRestriction`, BZ76 3.26). By `exists_fixedVectors_ne_bot` one of them,
  `S_i`, has a nonzero `L`-fixed vector. It has an invariant complement by
  semisimplicity and compact coefficients by
  `hasCompactSmoothDualCoefficients_subrepresentation`.
- `exists_twist_equiv`: if supercuspidal `A₁, A₂` have central character `χ` and
  their restrictions to `G°` admit a nonzero intertwiner, then the twist of `A₁` by
  `φ ∘ mk` is equivalent to `A₂` on the Levi for some `φ : GL_(n+1)/G°Z →* ℂˣ`.
  BZ76 3.29 (`exists_twistIntertwiningMap_of_restrictedHom_nonzero`, with the
  commutator of the Levi contained in `G°`) gives a character `χ'` trivial on `G°`
  and a nonzero intertwiner from the `χ'`-twist of `A₁` to `A₂`, an equivalence by
  `twistEquivOfNonzeroIntertwiner`. Comparing the central actions on a nonzero
  vector and its image shows that `χ'` is trivial on `Z`. So `χ'` factors through
  `GL_(n+1)/G°Z`.
- `isoClass_eq_of_twist_equiv`: if the same twisted representation of the Levi is
  equivalent to the pullbacks of `A₁` and `A₂`, then `A₁` and `A₂` have the same
  class (the composite equivalence is an equivalence of `GL_(n+1)`-representations
  because the Levi embedding is surjective).
- `centralFixedStratum_finite`: let `s` be the stratum and `L = unitLevel K n N`.
  Choose a representative of each class in `s`, a constituent class `cl a` in the
  finite set `fixedStratum L` (`exists_isConstituent`, finite by
  `compactCoefficientFixedLevelFiniteness`, BZ76 4.14), and, comparing with the
  chosen element `a₀ = invFun cl (cl a)` having the same constituent class, a
  character `tw a` of `GL_(n+1)/G°Z` such that the `tw a`-twist of `a₀` is `a`
  (`exists_ne_zero_of_isConstituent` then `exists_twist_equiv`). The map
  `a ↦ (cl a, tw a)` is injective by `isoClass_eq_of_twist_equiv`, and its codomain
  is finite by 4.14, `finite_twistQuotient` and `finite_monoidHom_units`.
- `centralLevelStratum_finite`: rewrite the bounded-level stratum as the fixed-vector
  stratum of `Conductor.levelOpenSubgroup K n b` (`centralLevelStratum_eq`) and use
  its compactness (`isCompact_levelOpenSubgroup`).
- `padicSupercuspidalCompactOpenFiniteness`: `centralFixedStratum_finite` for each
  `K`.

Standard axioms only.
