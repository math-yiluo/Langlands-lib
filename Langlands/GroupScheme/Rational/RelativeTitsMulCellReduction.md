# The relative Tits multiplication axiom from the rank-one factorization

This internal auxiliary module supports the proof task for
`Langlands.GroupScheme.RelativeTitsSystemStatement`. It derives the multiplication axiom
`mul_mem_cell` of the relative Tits data from the following inputs:

- the published rank-one factorization `RelativeRoot.HasRankOneFactorization i` (module
  `Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement`, Kaletha–Prasad 2.11.17);
- a new predicate `HasSimpleRootParabolicFactorization`;
- uniqueness of the relative reflection of a simple root;
- the minimal endpoint identity.

It applies the abstract lemma `Langlands.Group.TitsSystem.mul_mem_cell_of_rankOne`
(module `Langlands.Group.TitsSystemMulCell`). At the level of the published statements it
reduces `RelativeTitsSystemStatement` to the following inputs:

- `RelativeWeylCoxeterStatement`;
- `StandardParabolicEndpointsStatement`;
- `RationalBruhatStatement`;
- `RootRankOneFactorizationStatement`;
- `HasSimpleRootParabolicFactorization` for all data;
- the nondegeneracy field `conj_not_le` for all data.

None of these inputs is proved here, so the module does not prove the target. It adds no
axioms.

## Notation

Write `B = standardParabolicPoints i ν ∅` (that is, `P_∅(k)`), `N = normalizerPoints i`,
`π = QuotientGroup.mk'` from `N` onto `relativeWeylGroup i = N(k)/Z(k)`, and
`S = simpleRelativeReflections i ν`. For a character `a`, `U_a(k)` is the group of `k`-points
`(RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))` of the published root subgroup.

## The predicate `HasSimpleRootParabolicFactorization`

`HasSimpleRootParabolicFactorization i ν` is a new internal predicate. It says: for every simple
relative root `a`, every relative reflection `s` in `a` and every `b ∈ B`, there are `b'` and
`u ∈ U_a(k)` with `b = b' * u` and `n * b' * n⁻¹ ∈ B` for every representative `n ∈ N` of `s`.

Its classical content is in the proof of Borel–Tits, *Groupes réductifs* (1965), Proposition
5.16 (printed p. 101). There `U = V_a ⋊ U_(a)`, where `V_a` is the unipotent radical of the
standard parabolic subgroup attached to `{a}`. So `P_∅(k) = Z(k) V_a(k) U_(a)(k)`, and the
representatives of `r_a` normalize `Z(k) V_a(k)`. Classically one takes `b'` in the subgroup
`Z(k) V_a(k)`, which is contained in `B`. The predicate only asks for the conjugation property of
`b'`. It does not ask `b' ∈ B` and makes no claim about `V_a`. It is not proved here.

## Elementary lemmas

- `IsRelativeReflection.of_neg`: if `a` is a relative root, a relative reflection in `-a` is a
  relative reflection in `a`. The functional `f` with `f(-a) = 2` is replaced by `-f`. The
  reflections `x ↦ x - f(x)(-a)` and `x ↦ x - (-f)(x) a` agree.
- `IsRelativeReflection.inv`: the inverse of a relative reflection in `a` is a relative
  reflection in `a`, by Mathlib's `Module.reflection_inv`.
- A private lemma: for a split torus, a representative `n` of a relative reflection in `a`
  satisfies `weylAction i n a = -a`. It applies `IsRelativeReflection.relativeWeylAction_apply_self`
  and the injectivity of `toRat` on characters of a split torus
  (`IsSplitTorus.character_toRat_injective`).
- `HasRelativeWeylCoxeterSystem.eq_of_isRelativeReflection_of_mem_simple`: under the published
  Coxeter realization and a split torus, two relative reflections in the same simple root are
  equal. Both equal the Coxeter generator, by
  `IsRelativeWeylCoxeterRealization.eq_simple_of_isRelativeReflection`.

## The main theorem

`relativeTits_mul_mem_cell_of_rankOneFactorization` assumes the following:

- `hT`: `T` is a split torus;
- `hν`: `ν` is generic;
- `hB`: the minimal endpoint identity `B = P(ν)(k)`, with `P(ν)` the dynamic parabolic of `ν`;
- `hrank : RelativeRoot.HasRankOneFactorization i`;
- `hfac : HasSimpleRootParabolicFactorization i ν`;
- `huniq`: each simple relative root has at most one relative reflection.

It proves the `mul_mem_cell` field for `S`. Fix `s ∈ S`, a simple root `a` with `s` a
reflection in `a`, representatives `n` of `s` and `m ∈ N`, and `b ∈ B`. The proof applies
`mul_mem_cell_of_rankOne` with these data:

- `B' = {b' | n' b' n'⁻¹ ∈ B for every representative n' of s}`. This set need not be contained
  in `B`, and it is larger than the classical factor `Z(k) V_a(k)`;
- `U = U_a(k)`;
- `P = {w | 0 < ⟨w⁻¹ · a, ν⟩}`, where `w⁻¹ · a` is `relativeWeylCharacterAction i w⁻¹ a`.

The hypotheses of the abstract lemma are checked as follows:

- `s * s = 1`: `s⁻¹` is also a reflection in `a` (`IsRelativeReflection.inv`), so `s⁻¹ = s`
  by `huniq`.
- Every `b ∈ B` is a product `b' * u` with `b' ∈ B'` and `u ∈ U`, that is `B ⊆ B' U`: this is
  `hfac`. The reverse inclusion can fail for this `B'` and is not used. For example, in
  `SL₂(ℚ)` with `B` upper triangular, `n = [[0,-1],[1,0]]` and `x = [[1,0],[1,1]]`, every
  representative of `s` conjugates `x` into `B`, but `x ∉ B`.
- `B'` is conjugated into `B` by every representative of `s`: this is the definition of `B'`.
- Rank one: let `n` represent `s` and `u ∈ U_a(k)`. By `RelativeRoot.normalizer_conj_mem`,
  `v = n u n⁻¹` lies in `U_{weylAction n a}(k) = U_{-a}(k)`. If `v = 1` then `v ∈ B`.
  Otherwise `-a` is a relative root (`IsRelativeReflection.neg_mem_relativeRoots`), and `hrank`
  applied to `-a` and `v` gives `p` with `p.1, p.2 ∈ U_a(k)` and `m₀ = p.1 v p.2 ∈ N`. The class
  of `m₀` is a relative reflection in `-a`, hence in `a` (`of_neg`), hence equal to `s` by
  `huniq`. Since `a` is simple, `U_a(k) ⊆ B`
  (`RelativeRoot.subgroup_le_standardParabolic_empty`). So `v = p.1⁻¹ m₀ p.2⁻¹` lies in the cell
  of `s`.
- `P`: let `π m = w ∈ P` and `u ∈ U_a(k)`. Then `m⁻¹ u m ∈ U_{weylAction m⁻¹ a}(k)` by
  `normalizer_conj_mem`, and `weylAction i m⁻¹ a = w⁻¹ · a` pairs positively with `ν`. So
  `m⁻¹ u m` lies in the dynamic unipotent subgroup of `ν`
  (`RelativeRoot.subgroup_le_dynamicUnipotent`). That subgroup lies in the dynamic parabolic,
  which is `B` by `hB`.
- Covering: `w⁻¹ · a` is a relative root (`weylAction_mapsTo_relativeRoots`), so its pairing
  with the generic `ν` is nonzero. If the pairing is positive, `w ∈ P`. If it is negative, then
  `(s w)⁻¹ · a = w⁻¹ · (s · a) = -(w⁻¹ · a)`, using `s⁻¹ = s` and `s · a = -a`. So `s w ∈ P`.

`hasRelativeTitsCellAxioms_of_rankOneFactorization` adds the nondegeneracy field `hconj` and
concludes `HasRelativeTitsCellAxioms i ν`.

## Statement-level reduction

`relativeTitsSystemStatement_of_rankOneFactorization` assumes the following:

- `RelativeWeylCoxeterStatement.{u}`;
- `StandardParabolicEndpointsStatement.{u}`;
- `RationalBruhatStatement.{u}`;
- `RootRankOneFactorizationStatement.{u}`;
- `hfac` and `hconj`: `HasSimpleRootParabolicFactorization i ν` and the `conj_not_le` field, for
  every field `k`, connected reductive `G`, maximal split torus `i` and generic `ν`, with the
  `haveI` instances of the target statement.

It proves `RelativeTitsSystemStatement.{u}` via `relativeTitsSystemStatement_of_statements`
(module `RelativeTitsBorelReduction`). For fixed data:

- the split torus comes from `hi.isSplitSubtorus.1`;
- `hB` comes from the first conjunct of the endpoint statement;
- `huniq` comes from the Coxeter statement through
  `HasRelativeWeylCoxeterSystem.eq_of_isRelativeReflection_of_mem_simple`.

## Provenance

The results are internal and derived. They compose published modules with the abstract lemma in
`Langlands.Group.TitsSystemMulCell`. The published modules are the rank-one factorization
statement, root-subgroup conjugation, positivity of root subgroups, the character action of the
relative Weyl group, reflection negation and the Coxeter realization. The argument is the proof
of Borel–Tits 5.16 (i) (printed p. 101), checked against the central-library scan. In that
proof, the rank-one Bruhat decomposition of `Z(S_a)` plays the role that the rank-one
factorization plays here.

The reflection-on-character step reuses
`IsRelativeReflection.weylAction_apply_self` from `RelativeTitsNondegeneracy`.
