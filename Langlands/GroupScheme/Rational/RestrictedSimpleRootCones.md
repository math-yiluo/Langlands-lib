# Actual restricted simple roots and positive root-combination cones

Author: Worker 1416.

This unit constructs the restricted simple roots `Δ(P)` of Renard V.3.14 and the
first two cones of V.3.15. They are built on the existing actual group schemes,
character lattices, simple relative roots and full real character spaces. It is a
definition unit with short intrinsic proofs. It does not define a new root system,
and it does not prove any structural theorem about reductive groups.

## Source correspondence

Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, source `renard-2026-representations-groupes-reductifs-padiques`,
V.3.14 and V.3.15, printed p.113 (PDF p.119). The cones are consumed in VII.2.1,
printed p.227 (PDF p.233).

- **V.3.14.** For a parabolic subgroup `P = MN` with split component `A_M ⊂ A_∅`,
  the source defines
  `Δ(P) := {α|_{𝔞_M} | α ∈ Δ_∅ \ Δ_∅^M}`,
  where `𝔞_M ⊂ 𝔞_∅` comes from the inclusion `A_M ⊂ A_∅`. Here
  `restrictedSimpleRoots i ν J f` is the image of `simpleRelativeRoots i ν \ J`
  under `restrictedRootVector f`. That map sends `α` to
  `rationalCharacterRestrictReal (CommGroupScheme.groupHom f) (1 ⊗ α)`.
  The dictionary is:
  - `T` is `A_∅`, with its actual inclusion `i : T.toGrp ⟶ G`;
  - `A` is `A_M`, and the actual morphism `f : A ⟶ T` is the inclusion
    `A_M ⊂ A_∅`;
  - `simpleRelativeRoots i ν` is `Δ_∅`;
  - `J` is `Δ_∅^M`;
  - `RealTorusSpace.Vstar A = ℝ ⊗[ℤ] characterLattice A` is `𝔞_M^*`.

  Restricting a real linear form on `𝔞_∅` to `𝔞_M` is pullback along `f`.
  `pair_restrictedRootVector` makes this exact: for every `v : V A`,
  `pair A (restrictedRootVector f α) v = eval T α (cocharacterMapReal f v)`.
  The proof rewrites with the existing real-pairing naturality theorem
  `pair_cocharacterMapReal` and `eval_eq_pair`. By `restrictedRootVector_eq_tmul`,
  the vector is definitionally `1 ⊗ (f ≫ α)`. So
  `restrictedSimpleRoots_eq_image_restrictedSimpleCharacters` identifies the real
  set with the images `1 ⊗ χ` of the integral restricted characters
  `restrictedSimpleCharacters i ν J f = {f ≫ α | α ∈ simpleRelativeRoots i ν \ J}`.
- **V.3.15, first formula.**
  `+[𝔞^*]_P^G = {χ = ∑_{α ∈ Δ(P)} c_α α, c_α > 0}`.
  This is `restrictedRootPositiveCone i ν J f hfin`: every vector of the whole
  finite set `restrictedSimpleRoots i ν J f` occurs once, with a strictly positive
  real coefficient.
- **V.3.15, second formula** (the overlined `+[𝔞^*]_P^G`).
  `{χ = ∑_{α ∈ Δ(P)} c_α α, c_α ≥ 0}`.
  This is `restrictedRootNonnegCone i ν J f hfin`, the same sums with nonnegative
  coefficients.

Like the source, the cones are indexed by `Δ(P)`, which is the set of distinct
restricted vectors. Both cones are instances of the generic `RootCombination.positive S hS`
and `RootCombination.nonneg S hS` for a finite set `S` of vectors. These generic
sets require a coefficient for every member of `S` and sum over
`hS.toFinset`. Hence the strict cone is not the set of combinations with some
nonempty subset of positive coefficients. The finiteness proof is a proposition,
so the definitions do not depend on it.

### The derived formulation of the simple roots

`simpleRelativeRoots i ν` is the existing derived formulation from
`Rational.StandardParabolic`. Positivity is positive integer pairing with the
cocharacter `ν`. Simplicity means that a positive relative root is not a sum of two
positive relative roots. All relative roots are used, so nonreduced systems are
allowed. The source instead fixes a minimal parabolic `P_∅` and takes `Δ_∅` to be
the simple roots of `Σ(P_∅)`.

The definition by itself excludes only doubles. Suppose a simple root `α` equals
`2β` for a relative root `β`. Then `β` pairs positively with `ν`, so `α = β + β`
is decomposable, a contradiction. It does not exclude other integer multiples.
Renard's `Δ_∅` is the set of simple roots of the reduced positive roots
`Σ(P_∅)`, and reduced means that `α/n` is not a root for every `n ≥ 2` (V.3.4,
printed p.110, PDF p.116; V.3.12, printed p.112, PDF p.118). In the generality
of this unit the two conditions differ. For example, over `ℚ` take
`G = GL_2 × GL_2`, `T = G_m`, `i(t) = (diag(t,1), diag(t^3,1))` and `ν = id`,
and write `χ(t) = t`. The nonzero weights of `T` on `Lie(G)` are `±χ` and
`±3χ`, so the positive relative roots are `χ` and `3χ`. Neither is a sum of two
of them, so both are simple, although `3χ = 3 · χ`. This `T` is not a maximal
split torus, and the unit does not require one. The example was supplied by the
review of an earlier version of this unit and is not formalized here.

The existing target `RelativeSimpleRootBasisStatement` (in
`Rational.RelativeRankStatement`) covers a generic `ν`. It states that these
actual simple roots are finite and form a rational basis of the relative root
span. Identifying them with the simple roots of the minimal parabolic determined
by `ν`, which are indivisible by Renard's definition, is a further structural
comparison. In particular, indivisibility of the actual simple roots for a
maximal split `T` and generic `ν` would come from that comparison, not from the
definition. This unit neither uses nor proves that comparison. It also does not
claim that the result is independent of the initial minimal parabolic.

## Scope and inputs

The construction holds over every field `k : Type u`. It applies to actual
commutative group schemes `A`, `A'` and `T` over `Spec k`, and to an actual group
scheme `G` with `[IsAffineHom G.X.hom]`. The other inputs are a morphism
`i : T.toGrp ⟶ G`, a cocharacter `ν` and a morphism `f : A ⟶ T`. `J` is any set
of characters of `T`. Only `simpleRelativeRoots i ν \ J` enters, so the source
convention `J ⊆ simpleRelativeRoots i ν` is a special case. `J` and the simple-root
set may be empty. The unit assumes no maximal splitness, genericity, reductivity,
characteristic zero, perfectness, splitness of `G`, positive rank, `GL_n`
structure, reducedness, or root-system property of the restricted roots.

**Finiteness premise.** The cone definitions take the explicit input
`hfin : (simpleRelativeRoots i ν).Finite`.

- `finite_restrictedSimpleRoots` proves from `hfin` that the restricted set is
  finite. This is the image of the finite set difference.
- The existing proved theorem `IsSplitTorus.finite_simpleRelativeRoots`
  (`Rational.RootSupportFiniteness`) supplies `hfin` when `T` is split and
  `[LocallyOfFiniteType G.X.hom]` holds.
  `finite_restrictedSimpleRoots_of_isSplitTorus` records this route.
- Alternatively, `HasRelativeRootSystem.finite_simpleRelativeRoots`
  (`Rational.RootFiniteness`) supplies `hfin` under its own premises.

No other premise is required.

**Standard-Levi specialization.** Let `j : L ⟶ G` be an actual closed
representative of `standardLevi i ν J` and `a : A.toGrp ⟶ L` a split component.
Suppose `f : A ⟶ T` satisfies `CommGroupScheme.groupHom f ≫ i = a ≫ j`, the
factorization in `StandardLeviSplitCentralDirectionsStatement`. Then the
constructions apply directly to this `f`. This unit does not prove that such an
`f` exists, nor the image equality of that statement.

`eq_of_groupHom_comp_eq` proves that `f` is determined by `a` when
`i.hom.hom.left` is a monomorphism. The proof cancels the mono on underlying
morphisms and uses extensionality of group-scheme morphisms. The
`…_splitComponentIso` theorems change the split component by a torus isomorphism
`e : A ≅ A'` with `groupHom e.hom ≫ a' = a`. The two factorizations then satisfy
`e.hom ≫ f' = f`, so the cones correspond as in the naturality laws below.

## Implemented laws

**Generic layer (`RootCombination`).** Membership is stated in each of these
forms:

- the defining sum over `hS.toFinset`;
- an enumeration-free `finsum` over `S`;
- any finset with underlying set `S`;
- any `Fintype`-indexed family with range `S`;
- any finset-indexed family with image `S`, with repetitions allowed
  (`mem_positive_iff_family` and `mem_nonneg_iff_family`).

All of these follow from one private fiberwise reindexing lemma. To pass from
family coefficients `d` to vector coefficients, add `d` over each fiber. To go
back, split `c (v i)` equally over the fiber of `v i`. Strict positivity and
nonnegativity are stable under sums and under division by a positive integer.
This proves that the definitions do not depend on the enumeration.

The intrinsic laws are:

- `positive_subset_nonneg`;
- `zero_mem_nonneg`, `add_mem_nonneg` and `smul_mem_nonneg` for `r ≥ 0`;
- `add_mem_positive`, `smul_mem_positive` for `r > 0`, and
  `add_mem_positive_of_mem_nonneg`;
- `subset_nonneg`;
- `positive_empty` and `nonneg_empty`, which give the value `{0}` for the empty
  index set (the empty sum).

These laws bundle the sets as `positiveCone : ConvexCone ℝ M` and
`nonnegCone : PointedCone ℝ M`. `nonnegCone_eq_hull` identifies the latter with
Mathlib's `PointedCone.hull ℝ S`. `image_positive` and `image_nonneg` show that
any linear map `L` carries each cone of `S` exactly onto the cone of `L '' S`.
Injectivity is not needed, because coefficients of vectors with equal images add.

**Restricted roots.** For the restricted roots the unit proves:

- `mem_restrictedSimpleRoots`, the image-membership law;
- `restrictedRootVector_mem_restrictedSimpleRoots`;
- `finite_restrictedSimpleRoots`;
- `restrictedSimpleRoots_eq_empty_iff`, which says the set is empty exactly when
  `simpleRelativeRoots i ν ⊆ J`;
- the comparison with `restrictedSimpleCharacters`.

**Cones.** For the cones the unit proves:

- `mem_restrictedRootPositiveCone` and `mem_restrictedRootNonnegCone`, as finite
  sums in `Vstar A` over the restricted set;
- the `…_iff_finset` versions;
- the `…_iff_roots` versions. These index by any finset of actual roots with
  underlying set `simpleRelativeRoots i ν \ J`, with one coefficient per root,
  even when two roots have the same restriction;
- `restrictedRootPositiveCone_subset_nonnegCone`;
- zero, addition and scaling laws for both cones;
- `restrictedSimpleRoots_subset_nonnegCone`;
- `restrictedRootNonnegCone_eq_hull`;
- `restrictedRootPositiveCone_of_subset` and `restrictedRootNonnegCone_of_subset`,
  which give the value `{0}` when `J` contains every simple root.

**Naturality.** Let `g : A ⟶ A'` and `f' : A' ⟶ T` satisfy `g ≫ f' = f`.

- `rationalCharacterRestrictReal_restrictedRootVector` proves the vector formula
  on each actual root. Pulling back the restriction along `f'` by
  `rationalCharacterRestrictReal (groupHom g)` gives the restriction along `f`.
  The proof uses `rationalCharacterRestrictReal_tmul` and definitional
  associativity of composition.
- `image_restrictedSimpleRoots`, `image_restrictedRootPositiveCone` and
  `image_restrictedRootNonnegCone` give the resulting exact set equalities. The
  cone equalities use the linear-image laws.
- For a torus isomorphism `e : A ≅ A'` with `e.hom ≫ f' = f`, the `…_iso`
  theorems give both directions: along `e.hom` from `f'` to `f`, and along
  `e.inv` from `f` to `f'`.

## Outside this unit

This unit constructs only the root-positive linear-combination cones. The
following remain separate obligations:

- the coroot-inequality chambers `_P^G[𝔞^*]^+` and their closures;
- the projected coroots `β̌` and the fundamental weights `ϖ_α`;
- orthogonal projections and the central direct sums `𝔞_M^* = 𝔞_G^* ⊕ (𝔞_M^G)^*`;
- the V.3.16 cellular decomposition and the V.3.17–18 combinatorics.

Naming the nonnegative set after the source's overlined notation does not prove
that it is the topological closure of the strict cone. The unit proves no
openness or closedness. It also does not establish any of these:

- independence of the initial minimal parabolic, or Weyl-conjugacy comparisons;
- the existence of the split-component factorization;
- the exponent definition of temperedness or its analytic comparison;
- any representation-theoretic classification or generic irreducibility.

Provenance: the restricted roots and cones apply the source formulas to the
published actual interfaces (`Rational.StandardParabolic`,
`Rational.RelativeCentralDirections`, `Building.RealTorusSpace`,
`Building.RealTorusDuality`, `Rational.RootSupportFiniteness`). The generic
`RootCombination` layer, the reindexing lemma, the naturality theorems and the
split-component uniqueness lemma are internal derivations.


## Additional enumeration and annihilator laws

The shared definitions also support the following independently established
finite-sum and transport laws. `RootCombination.positive` and
`RootCombination.nonneg` are the single generic cone definitions, and
`restrictedRootPositiveCone` and `restrictedRootNonnegCone` are the single
restricted cone definitions used throughout.

`mem_positiveCombinations` and `mem_nonnegCombinations` give the defining sums.
Their `_iff_finset` variants use any repetition-free finset with the specified
underlying set; their `_iff_equiv` variants use any equivalence `ι ≃ S` with
`Fintype ι`. `positiveCombinations_congr` and `nonnegCombinations_congr` express
independence of the set presentation and its finiteness proof. The
`positiveCombinations_subset_nonnegCombinations`, `zero_mem_nonnegCombinations`,
addition, scaling and `_of_eq_empty` laws retain their explicit finite-set
formulations. `image_positiveCombinations` and `image_nonnegCombinations` retain
their injectivity hypotheses; the `RootCombination.image_positive` and
`RootCombination.image_nonneg` laws above apply to arbitrary linear maps.

For restricted roots, `restrictedSimpleRoots_eq_image` displays the real
character restriction explicitly, `restrictedSimpleRoots_eq_image_characters`
displays the integral character image, and `restrictedSimpleRoots_finite`
records finiteness from the supplied finite simple-root set.
`restrictedSimpleRoots_eq_empty_iff_sdiff` uses the conclusion
`simpleRelativeRoots i ν \ J = ∅`; `restrictedSimpleRoots_eq_empty_iff` retains
the equivalent subset formulation. Neither statement has been replaced by a
different hypothesis or conclusion.

`mem_restrictedPositiveCone` and `mem_restrictedNonnegCone` express membership
in the shared restricted cones by sums over the finiteness witness's
`toFinset`. Their `_iff_finset` and `_iff_equiv` variants retain the explicit
enumerations. The corresponding subset, zero, addition, scaling and
`restrictedPositiveCone_of_eq_empty` / `restrictedNonnegCone_of_eq_empty`
laws use the same definitions, including the empty-set value `{0}`.

`restrictReal_restrictedRootVector` and
`restrictReal_image_restrictedSimpleRoots` express pullback along a supplied
factorization `g ≫ f' = f`. `restrictReal_hom_injective` proves injectivity
for a torus isomorphism using its inverse. The
`restrictReal_image_restrictedPositiveCone` and
`restrictReal_image_restrictedNonnegCone` laws retain the isomorphism
specialization of the cone transport.

If the range of `cocharacterMapReal f` lies in `rootAnnihilator T J`,
`pair_restrictedRootVector_eq_zero` proves that the restriction of every
`α ∈ J` pairs to zero with every real cocharacter of `A`. When `A` is split,
`restrictedRootVector_eq_zero` uses the perfect real pairing to conclude that
the restricted vector itself is zero. These statements retain the range and
splitness hypotheses. For a standard Levi, the published
`range_cocharacterMapReal_le_rootAnnihilator_standardLevi` supplies the range
containment under its own hypotheses; no factorization existence or central
direct-sum result is inferred here.

Renard VII.2.1 (printed p.227, PDF p.233) uses the nonnegative cone in the
exponent condition for temperedness, together with admissibility and
quantification over all parabolics and normalized exponents. The present
construction and laws do not prove that representation-theoretic condition.
