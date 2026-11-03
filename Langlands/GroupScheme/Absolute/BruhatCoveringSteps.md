# Steps of the absolute Bruhat covering: cocharacter, quotient and normalizer point

This module collects the group-theoretic steps of the dynamic-limit proof of the absolute
Bruhat covering `G(k) = B(k) N_G(T)(k) B(k)`
([`BruhatCoveringStatement`](BruhatCoveringStatement.md)). Throughout, `k` is an
algebraically closed field, `S = Spec k`, `G` and `B` are group schemes over `S`, and `T` is a
commutative group scheme over `S`. A Borel pair `(i, j)` (`IsBorelPair`) is a Borel subgroup
`i : B ⟶ G` together with a maximal torus `j : T ⟶ G` that factors through `i`.

The steps are conditional: each unproved structural input enters as a hypothesis of
`Prop`-valued Library statement type, named in the declaration. The geometric steps (the
limit of a cocharacter orbit in the proper quotient, its fixedness, and the opposite-cell
argument) are in other modules.

## Sources and provenance

The covering itself is Borel–Tits 1965, §2.3–§2.4 (see the statement's Markdown). The proof
assembled from this module and its companions is an internal route, not a transcription of a
source proof: a cocharacter `λ` of `T` with `P(λ) = B` and `Z(λ) = T`, the limit at `0` of the
orbit `t ↦ λ(t)·gB` in the proper quotient `G/B`, which is a `λ`-fixed point `nB` with `n`
normalizing `T`, and an opposite-cell chart at that point. The lemmas below are its
group-theoretic steps, stated in the Library's actual-object vocabulary. The unproved inputs are
the following Library statements, each taken as an explicit hypothesis; their sources are
recorded in their own Markdown:

- `TorusFiniteGaloisSplittingStatement`, used through
  `IsTorus.isSplitTorus_of_finiteGaloisSplitting`;
- `RegularCocharacterBorelStatement`;
- `GenericCentralizerStatement`;
- `MaximalTorusCentralizerStatement`;
- `ParabolicSubgroupQuotientProperStatement`;
- `CentralizerBorelIntersectionStatement`;
- `SolvableMaximalTorusConjugacyStatement`.

None of these is the rational Bruhat decomposition, Borel–Tits 1965 Proposition 4.18,
`TwoBorelCommonMaximalTorusStatement`, `ParabolicIntersectionGeometryStatement` or
`ParabolicIntersectionTorusStatement`.

## Declarations

All declarations are in the namespace `Langlands.GroupScheme.BruhatCovering`.

- `exists_cocharacter`: assume `TorusFiniteGaloisSplittingStatement`,
  `RegularCocharacterBorelStatement`, `GenericCentralizerStatement` and
  `MaximalTorusCentralizerStatement`. Let `G` be connected reductive and `(i, j)` a Borel pair.
  Then there is a homomorphism `ν : 𝔾_m ⟶ T` such that the dynamic parabolic subgroup
  `P(ν ≫ j)` is represented by `i` and the dynamic centralizer `Z(ν ≫ j)` equals the range of
  `j`.
  Proof: `T` is split by the splitting hypothesis (over an algebraically closed field a torus is
  split by a finite Galois extension). Clause 3 of `RegularCocharacterBorelStatement` applied
  to the factorization `f ≫ i = j` gives a regular cocharacter `ν` with `P(ν ≫ j)` represented
  by `i`. Since `j` is a maximal torus with `T` split, it is a maximal split torus
  (`IsMaximalTorus.isMaximalSplitTorus`), and a regular cocharacter is generic, so
  `GenericCentralizerStatement` gives `Z(ν ≫ j) = torusCentralizer j`, which equals the range of
  `j` by `MaximalTorusCentralizerStatement`.

- `isParabolicSubgroup_of_isBorelSubgroup`: over an algebraically closed field, a Borel subgroup
  `i` is a parabolic subgroup. Proof: the identity of `k` is an algebraic closure, and the Borel
  property is preserved by the base change along it
  (`IsBorelSubgroup.baseChange_of_bijective`), which is the witness required by
  `IsParabolicSubgroup`.

- `exists_proper_quotient`: assume `ParabolicSubgroupQuotientProperStatement`. If `G` is smooth,
  affine and connected and `i` is a Borel subgroup, then there are `Q` over `S` and
  `q : G ⟶ Q` with `Q` separated and proper over `S`, `q` smooth, surjective and quasi-compact,
  and with the fibers of `q` exactly the cosets of the range of `i`: on every test scheme `V`,
  `g ≫ q = h ≫ q` if and only if `g⁻¹ h` lies in the range of `i`.
  Proof: the proved `smoothSubgroupQuotientExistence` gives a separated quotient of finite type
  with these properties of `q`; it is proper by the hypothesis, since `i` is parabolic
  (`isParabolicSubgroup_of_isBorelSubgroup`).

- `range_le_conj_of_range_conj_le`: for homomorphisms `a : H ⟶ G`, `b : K ⟶ G` and a rational
  point `g`, if the range of `a` followed by conjugation by `g⁻¹` lies in the range of `b`, then
  the range of `a` lies in the range of `b` followed by conjugation by `g`. Proof: pointwise,
  using `innerIso_inv_hom` and `Iso.inv_hom_id`.

- `comp_innerIso_comp`: for `a : H ⟶ G` and a rational point `p` of `H`, conjugation by the
  image `a(p)` after `a` equals `a` after conjugation by `p` in `H`. Proof: pointwise on test
  points (`hom_ext_points`), since `a` is a homomorphism compatible with multiplication and
  inversion.

- `exists_normalizerPoint_of_fixed_coset`: assume `CentralizerBorelIntersectionStatement` and
  `SolvableMaximalTorusConjugacyStatement`, and let `G` be smooth, affine and connected with a
  Borel pair `(i, j)`. Let `χ : 𝔾_m ⟶ G` have dynamic centralizer equal to the range of `j`,
  let `q : G ⟶ Q` have fibers the cosets of the range of `i`, and let `h₀` be a rational point
  of `G` whose coset is fixed by `χ`: for every test point `t` of `𝔾_m`,
  `(χ(t) h₀) ≫ q = h₀ ≫ q`. Then there is `n` in `normalizerPoints j` with `n ≫ q = h₀ ≫ q`.
  Proof:
  1. The fixed coset gives `h₀⁻¹ χ h₀ ⊆ B` (`range_conjugate_le_of_fixed_coset`), hence
     `χ ⊆ h₀ B h₀⁻¹` (`range_le_conj_of_range_conj_le`).
  2. `CentralizerBorelIntersectionStatement` for the Borel subgroup `h₀ B h₀⁻¹` and the
     centralizer `Z(χ) = T` gives a Borel subgroup `c : C ⟶ T` whose image lies in
     `h₀ B h₀⁻¹`. A torus is smooth, connected and commutative, hence solvable, so the
     maximality clause of `IsBorelSubgroup` for `c` makes `c` an isomorphism. Hence
     `h₀⁻¹ T h₀ ⊆ B`, and the corresponding factorization `f' : T ⟶ B`
     (`SubgroupFunctor.factorOfRangeLE`) satisfies `f' ≫ i = j ≫ int(h₀⁻¹)`.
  3. Both `f` (from the Borel pair) and `f'` are maximal tori of `B`
     (`IsMaximalTorus.of_comp`). `B` is smooth, affine, connected and solvable, so
     `SolvableMaximalTorusConjugacyStatement` and
     `subgroupConjugate_iff_exists_commGroupSchemeIso` give a rational point `b` of `B` and an
     automorphism `e` of `T` with `f ≫ int_B(b) = e ≫ f'`.
  4. Put `n = h₀ · i(b)`. Then `j ≫ int(n) = f ≫ i ≫ int(i(b)) ≫ int(h₀)
     = f ≫ int_B(b) ≫ i ≫ int(h₀) = e ≫ f' ≫ i ≫ int(h₀) = e ≫ j ≫ int(h₀⁻¹) ≫ int(h₀) = e ≫ j`
     (`innerIso_mul_hom`, `comp_innerIso_comp`, `innerIso_one_hom`), so `n` is in
     `normalizerPoints j`; and `n ≫ q = h₀ ≫ q` because `h₀⁻¹ n = i(b)` lies in the range
     of `i`.

- `exists_normalizerPoint_of_isFixed`: under the hypotheses of the previous declaration, let
  `q` moreover be locally of finite type and surjective, and let `a` be an action of `G` on `Q`
  compatible with `q`: `a.act g (h ≫ q) = (g h) ≫ q` on all test points. If a rational point
  `y` of `Q` is fixed by the restriction of `a` along `χ` (`SchemeAction.IsFixed`), then there
  is `n` in `normalizerPoints j` with `n ≫ q = y`.
  Proof: since `k` is algebraically closed and `q` is surjective and locally of finite type,
  `y` lifts to a rational point `h₀` of `G`
  (`Langlands.exists_point_lift_of_locallyOfFiniteType_surjective`). Fixedness of `y` evaluated
  at the test points of `𝔾_m`, together with the compatibility of `a` with `q`, is the fixed-coset
  hypothesis of `exists_normalizerPoint_of_fixed_coset` for `h₀`. This is the same pattern as
  `IsBorelSubgroup.of_fixedQuotientPoint`.
