# Proof of the representative fixed-vector criterion (Renard VI.10.6, Corollary, first claim)

## What is proved

`Langlands.CuspidalSupport.standardRepresentativeFixedVectorCriterion` has type
exactly `StandardRepresentativeFixedVectorCriterionStatement.{uF, uV}`, the
published statement in
`Langlands.Representation.CuspidalSupport.StandardLeviFixedVectorSupportStatements`.
In words: let `G` be connected reductive over the nonarchimedean local field
`F`, with the standard Bernstein family `family := standardBernsteinFamily i ν hG hi hν`.
Let `K₀` be a subgroup with the minimal standard Iwasawa decomposition
`G(F) = M_∅ N_∅ K₀`. Let `K` be a compact open subgroup normalized by `K₀` with
the Iwahori decomposition along every standard parabolic. Then for every
standard cuspidal datum `a = (M_I, σ)` the following are equivalent:

* some smooth representation `π` of `G(F)` with inertial support
  `[M_I, σ]_G` (`IsBernsteinInertialSupport`) has a nonzero `K`-fixed vector;
* the literal Levi representation `bernsteinLiteralLeviRep i ν a.roots a.representation`
  has a nonzero vector fixed by `K ∩ M_I(F)`, i.e. by
  `K.toSubgroup.comap (levi i ν a.roots).subtype`.

The proof is unconditional. It imports only published Library results, adds no
premise, and does not use `CompactOpenInertialFinitenessStatement`, Renard
VI.5.4, inertial-support invariance or any other unproved statement. The axioms
are `propext`, `Classical.choice` and `Quot.sound`. Three hypotheses of the
target are not needed by the proof: the standard-cocharacter hypothesis
`_hstandard`, compactness of `K₀` (`_hK₀`) and the inclusion `K ≤ K₀` (`_hKK₀`).
The proof uses compactness and openness of `K`, `K₀ ≤ normalizer K`, the Iwasawa
decomposition with `K₀`, and the Iwahori decompositions.

## Source and route

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`),
VI.10.6, Corollary and its proof, printed page 215 (PDF page 221). There, for
`𝔰 = [M, (σ, E)]_G`, the first step shows `𝔰 ∈ B(G)_K` iff `E^{K_M} ≠ 0`. For
(⇐) Renard uses the Jacquet lemma and the geometric lemma on `i_P^G(σ)`. For (⇒)
he takes `E^{p(K_g)} ≠ 0` for some `g`, writes `g = pk` with `p ∈ P` and
`k ∈ K₀`, and uses normality of `K` in `K₀` to get `K_g = p (K ∩ P) p⁻¹`.
Every `p(K_g)` is therefore conjugate to `K_M` in `M`.

The Lean proof follows this (⇒) argument, with the published normal-level
Mackey criterion `Jacquet.nontrivial_standardInduction_fixedVectors_iff` in
place of Jacquet modules. It also handles an arbitrary representative of the
inertial class, which may sit on a different standard Levi `M_J`. Modifying
the conjugating point by the Levi part of `p` makes this
step free of VI.5.4. The (⇐) direction is a published helper (module
`StandardRepresentativeFixedVectorHelpers`).

## Declarations

### Abstract group-theoretic lemmas

These are stated over arbitrary groups. Isolating them keeps the kernel from
unfolding the Levi scheme constructions when it compares `M_I(F)` with `M_J(F)`.

* `levi_conj_mem_of_projection_mem`: let `D` be a semidirect decomposition
  `P = M ⋉ U` of subgroups of a group `H`, let `K₀ ≤ normalizer K`, and suppose
  the Levi projection `P → M` maps `K ∩ P` into `K`. Take `p ∈ P`, `k ∈ K₀`, `m`
  the Levi part of `p`, and `x ∈ K` with `y = (pk) x (pk)⁻¹ ∈ M`. Then
  `m⁻¹ y m ∈ K`. Proof: put `u = m⁻¹ p ∈ U` and `z = m⁻¹ y m ∈ M`. Then
  `k x k⁻¹ = u⁻¹ z u` (a `group` computation) lies in `K` by normality and in
  `P`. Its Levi projection is `z`, by `IsSemidirectDecomposition.projection_eq_iff`
  and the fact that `M` normalizes `U`. So `z ∈ K` by the projection hypothesis.
* `representation_conj_fixed_of_levi_conj_mem`: the algebraic core of the
  transport. Take subgroups `L_I, L_J, K` of a group `Γ`, a map `t : H_J → L_J`
  with a multiplicative left inverse `s`, and `φ : L_I → H_J` with
  `t (φ x) = g x g⁻¹`. Let `m ∈ L_J` conjugate `g (K ∩ g⁻¹ L_J g) g⁻¹` into `K` as
  above. If `v` is fixed by `ρ (s z)` for all `z ∈ K ∩ L_J`, then `ρ (s m) v` is
  fixed by `ρ (φ x)` for every `x ∈ K ∩ L_I`.
* `representation_apply_ne_zero`: group elements act injectively.
* `exists_ne_zero_of_nontrivial_fixedVectors_pullback` and
  `nontrivial_fixedVectors_pullback_pullback`: move between nontrivial fixed
  spaces of `SmoothRep.pullback` along topological group isomorphisms and
  explicit nonzero fixed vectors of the original representation.

### Statements about the standard family

* `leviRationalPointHomeomorph_rationalPointIso_coe`: for an actual Levi
  conjugacy `c : RationalLeviConjugacy (leviHom I) (leviHom J)`, the induced map
  on rational points is conjugation by `c.point` inside `G(F)`. This follows
  from `c.commutes`, applied on rational points, and the published
  `rationalPoints_map_innerIso`.
* `exists_leviPoint_conj_mem_of_normalLevel`: for every `g ∈ G(F)` there is
  `m ∈ M_J(F)` with `m⁻¹ (g x g⁻¹) m ∈ K` whenever `x ∈ K` and
  `g x g⁻¹ ∈ M_J(F)`. It writes `g = p k` with
  `standard_parabolic_factorization_of_minimal` (`p ∈ P_J`, `k ∈ K₀`), takes `m`
  to be the Levi part of `p`, and applies `levi_conj_mem_of_projection_mem`. The
  projection hypothesis comes from `standard_projection_mem_of_iwahoriIntersection`.
* `nontrivial_literalLeviFixedVectors_rationalIsoPullback`: if
  `B : SmoothRep ℂ M_J(F)` has a nonzero `K ∩ M_J`-fixed vector, then
  `rationalIsoPullback c.iso B` has a nonzero `K ∩ M_I`-fixed vector. That
  vector is `B(m) v`, with `m` from the previous lemma for `g = c.point`.
* `nontrivial_literalLeviFixedVectors_of_inertialSupport`, direction (⇒).
  Suppose `π` has inertial support `[a]` and a nonzero `K`-fixed vector. Then
  `π` is an irreducible subquotient of the induction of a datum `b` with
  `bernsteinInertialClass b = bernsteinInertialClass a`. By
  `bernsteinInertialClass_eq_iff` this gives a conjugacy `c : M_a → M_b` and an
  unramified twist relating `a.representation` and
  `rationalIsoPullback c.iso b.representation`. The published
  `exists_bernsteinCuspidalSupport_fixedVectors_iff` gives `b^{K ∩ M_b} ≠ 0`.
  The transport lemma gives `(c.iso^* b)^{K ∩ M_a} ≠ 0`. The Mackey criterion
  `nontrivial_standardInduction_fixedVectors_iff` lifts this to nonzero
  `K`-fixed vectors of the induction of `c.iso^* b` from `P_a`.
  `nontrivial_inductionFixedVectors_iff_of_rationalInertiaRelated` (unramified
  twists) moves this to the induction of `a.representation`. Mackey once more
  returns to `a^{K ∩ M_a} ≠ 0`.
* `representativeFixedVectorCriterion`: the equivalence for one
  `BernsteinStandardFamily`. (⇒) is the previous lemma. (⇐) is the
  published `exists_bernsteinInertialSupport_fixedVectors_of_literalLevi`
  (module `StandardRepresentativeFixedVectorHelpers`).
* `standardRepresentativeFixedVectorCriterion`: the target. It introduces the
  statement's binders and the instances its `letI`s fix (point topology,
  topological group, `T2Space F`, local compactness, nonarchimedean group).
  Then it applies `representativeFixedVectorCriterion` to
  `standardBernsteinFamily i ν hG hi hν`.

## Technical notes

The module sets `backward.isDefEq.respectTransparency.types false`, as many
Library modules do, and makes `Standard.leviScheme` locally irreducible, as in
`Jacquet.BernsteinFixedVectorVisibility`. Local instances give `M_I(F)` its
affine and finite-type structure and its topology
`rationalPointTopology F (bernsteinLeviScheme i ν I).X`, the same topology the
imported modules `BernsteinData` and `RationalInducedFixedVectors` use. None of
these choices changes the target statement, which fixes its own instances.
