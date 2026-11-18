# Normal subgroups meet parabolic and Borel subgroups well, given the normalizer theorem

Author: Worker 87.

This supporting module proves clauses (ii) and (iii) of
`NormalSubgroupIntersectionStatement`, which formalizes Conrad, *Reductive group schemes*,
Exercise 5.5.1. The proof assumes the published statement
`BorelContainingSubgroupSelfNormalizerStatement` (Milne, *Algebraic Groups*, Theorem 17.48 and
Corollary 17.49). Every theorem that needs it takes it as an explicit hypothesis `hI1`. The
module does not prove clause (i), on maximal tori. The final theorem
`normalSubgroupIntersection_of_torusClause_of_borelSelfNormalizer` takes clause (i) as a
hypothesis and returns the full target statement.

Throughout, `G` is a smooth connected affine group over a field and `h : H ⟶ G` is a smooth
connected closed subgroup with normal all-test range. The intersection `H ∩ P` is the published
scheme-theoretic intersection `subgroupIntersection h p`, the pullback of `h` and `p`. Its first
projection to `H` is `subgroupIntersectionFst h p`.

## General lemmas

These hold over an arbitrary base scheme.

- `mem_range_of_comp_mem_range_comp`: if `h` is a monomorphism on underlying objects and
  `u ≫ h` lies in the range of `z ≫ h`, then `u` lies in the range of `z`. The proof cancels
  the monomorphism.
- `range_comp_le`: the all-test range of `z ≫ h` lies in the range of `h`.

## Over an algebraically closed field `K`

`range_carrier_base_le_reducedSubgroupι`: for `Q` locally of finite type over `K`, every
`K`-rational point in the range of `r : Q ⟶ G` is already in the range of
`reducedSubgroupι Q ≫ r`. The proof lifts the point through the reduced subscheme
(`ReducedSubgroup.liftOver`), since `Spec K` is reduced.

`exists_borel_parabolicIntersection_algClosed`: assume `p : P ⟶ G` is a smooth closed subgroup
and a Borel subgroup `j : B ⟶ G` factors through `p`. Then `H ∩ P` is smooth and connected, and
some Borel subgroup `c : C ⟶ H` factors through it. The Lean proof has five steps.

1. Let `Q = H ∩ P`, let `Z = reducedSubgroup Q`, and let `z : Z ⟶ H` be the composite inclusion.
   Then `z` and `z ≫ h` are closed subgroups.
2. A Borel subgroup of `H` factors through `Z`. Take a Borel `c₀ : C₀ ⟶ H` (`borelConjugacy`).
   By `solvableSubgroupBorelContainment`, `c₀ ≫ h` lies in a Borel `B'` of `G`. Conjugacy of
   Borel subgroups (`borelConjugacy`) gives a rational point `g` with
   `i' ≫ innerIso g = φ ≫ j`. Since `H` is normal, conjugation by `g` restricts to an
   automorphism of `H` (`IsRepresentedBy.conjugateIso`). Then `c := c₀ ≫ conjugateIso` is a
   Borel subgroup of `H` (`IsBorelSubgroup.comp_iso`). Moreover `c ≫ h` factors through `p`, so
   `c` factors through `Q` (`pullback.lift`). Since `C₀` is smooth, it is reduced, so the
   factorization lifts to `Z` (`ReducedSubgroup.liftHom`).
3. The hypothesis `hI1`, applied to `z : Z ⟶ H`, shows that `Z` is connected and that the range
   of `z` is its own normalizer in `H`. The geometric Borel property of `c` comes from
   `borelAlgClosedFieldExtensionStatement`.
4. `P` normalizes `Z ≫ h`. First this holds on `K`-points. For a point `x` of `P` and a point
   `y` of `Z`, the conjugate `x y x⁻¹` lies in `H` because `H` is normal. It lies in `P` because
   `y` lies in `P`. Hence it lies in `Q`, and by `range_carrier_base_le_reducedSubgroupι` in `Z`.
   Next, the normalizer of the range of `z ≫ h` has a closed representative
   (`hasClosedRepresentative_normalizer_centralizer_range`). Its `K`-points are the abstract
   normalizer (`normalizer_range_carrier_base_eq_algClosed_points`). Since `P` is smooth, hence
   reduced, containment on `K`-points gives containment on all tests
   (`range_le_of_algClosed_points`).
5. On every test, a point of `Q` maps to a point of `P`, so it normalizes `Z ≫ h` in `G`. By
   `mem_range_of_comp_mem_range_comp` it normalizes `Z` in `H`. By step 3 it lies in `Z`. So the
   ranges of `z` and of `Q ⟶ H` are equal, and `IsClosedSubgroup.sourceIsoOfRangeEq` gives an
   isomorphism `Z ≅ Q`. Smoothness of `Q` follows from that of the reduced subgroup over the
   perfect field `K` (`smooth_of_over_iso`). Connectedness of `Q` follows from step 3 through
   the homeomorphism of underlying spaces.

`isBorelSubgroup_borelIntersection_algClosed`: if `j : B ⟶ G` is a Borel subgroup, then
`subgroupIntersectionFst h j` is a Borel subgroup of `H`. The proof applies the previous
theorem with `P = B` and `f = 𝟙`. The intersection is solvable: its second projection to `B` is
a closed immersion (a pullback of `h`), so its `K`-points embed into those of `B`
(`isSolvableGroupScheme_iff_rationalPoints`). Maximality of the Borel subgroup `C` of `H` then
makes the factorization `e : C ⟶ H ∩ B` an isomorphism. So the first projection is
`inv e ≫ c`, which is Borel by `IsBorelSubgroup.iso_comp`.

## Over an arbitrary field `k`

`normalSubgroupParabolicIntersection_of_borelSelfNormalizer` proves the second conjunct of
`NormalSubgroupIntersectionStatement` for a given `k` and `G`. Let `K` be the algebraic closure
of `k`, with base change `F = GroupScheme.baseChange (toAlgebraicClosure k)`. Base change keeps
`G` and `H` smooth, affine and connected (`connectedSpace_baseChange_of_smooth_affine`). It also
keeps `h` closed (`IsClosedSubgroup.baseChange`) and normal (`range_baseChangeHom`,
`IsNormal.baseChange`).

- Clause (ii). Let `p` be parabolic. Its definition supplies a Borel subgroup of `G_K` that
  factors through `p_K`. Take `Q = H ∩ P` and `q = subgroupIntersectionFst h p`. The
  algebraically closed theorem, applied to `F.map h` and `F.map p`, shows that the intersection
  over `K` is smooth and connected and contains a Borel subgroup of `H_K`.
  - `q` is a closed subgroup by `isClosedSubgroup_subgroupIntersectionFst`.
  - `Q` is smooth by fpqc descent (`smooth_pullback_of_smooth_pullback_baseChange`).
  - `Q` is connected by `connectedSpace_baseChange_pullback` and `connectedSpace_of_baseChange`,
    using surjectivity of `Spec K → Spec k`.
  - The Borel subgroup of `H_K` factors through `F.map q`, via the inverse of the comparison
    isomorphism `subgroupIntersectionBaseChangeIso` and `PreservesPullback.iso_inv_fst`.
  - The range identity is `range_subgroupIntersectionHom`.
- Clause (iii). Let `b` be a geometric Borel subgroup, so `F.map b` is a Borel subgroup of
  `G_K`. Take `C = H ∩ B` and `c = subgroupIntersectionFst h b`. The map `F.map c` is the
  comparison isomorphism followed by the first projection of `H_K ∩ B_K`
  (`PreservesPullback.iso_hom_fst`). That projection is Borel by the algebraically closed
  theorem, so `F.map c` is Borel. Then `isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure`
  gives the geometric Borel property of `c`. The range identity is again
  `range_subgroupIntersectionHom`.

`normalSubgroupIntersection_of_torusClause_of_borelSelfNormalizer` combines the previous theorem
with a supplied proof of clause (i) to give `NormalSubgroupIntersectionStatement`.

## Relation to the literature

Conrad, Exercise 5.5.1(ii)–(iii) (p.182), hints that one should work over `k̄` and use that a
parabolic subgroup is its own scheme-theoretic normalizer (his Corollary 5.2.8). The Lean proof
follows this hint. Over `K = k̄`, `BorelContainingSubgroupSelfNormalizerStatement` plays the
role of Corollary 5.2.8 for the reduced subgroup `Z = (H ∩ P)_red` of `H`. The normality of `Z`
in `P`, a step in Conrad's hint, becomes step 4 above. Step 5 turns self-normalization into
the equality `H ∩ P = Z`, which gives smoothness and connectedness. Conrad deduces
connectedness differently, from his Theorem 1.1.9. Descent from `k̄` to `k` uses fpqc descent
of smoothness and surjectivity of `Spec k̄ → Spec k`.
