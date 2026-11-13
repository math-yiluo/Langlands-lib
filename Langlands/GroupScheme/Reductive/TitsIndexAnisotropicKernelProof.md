# Proof: the semisimple anisotropic kernel of an actual Tits index is semisimple and anisotropic

Author: Worker 145 (Task 5618).

`Langlands.GroupScheme.titsAnisotropicKernel` proves exactly the published
proposition `Langlands.GroupScheme.TitsAnisotropicKernelStatement.{u}`
(module [`TitsIndexAnisotropicKernelStatement`](TitsIndexAnisotropicKernelStatement.md)).
It keeps the universe parameter `u` and takes no hypotheses.

Fix a field `k : Type u` of any characteristic, perfect or not, and a `k`-group
scheme `G` whose structure morphism is affine and locally of finite type. Fix
actual index data `d : TitsIndexData G`, with maximal split torus
`s = d.splitInclusion : S ⟶ G`. Let `j : M ⟶ G` be a homomorphism that
represents `torusCentralizer s`, the centralizer `Z(S)`. Let `i : D ⟶ M` satisfy
`IsDerivedSubgroup i`. The theorem proves `IsSemisimple D ∧ IsAnisotropic D`.
Here `IsAnisotropic D` means `splitRank D = 0`.

Nothing is assumed about `G` beyond these structure-morphism conditions and
the index data. In particular, quasi-split and anisotropic `G` are covered.

## Implemented proof

The proof uses only published Library theorems. It assumes no unproved Library
statement and uses no axioms beyond Lean's standard ones. Its imports do not
reach `LocalRankOneClassificationStatement` or any local Kneser–Tits statement
or result.

### Semisimplicity

1. `d.isSemisimple.isConnectedReductive` shows that `G` is connected reductive.
2. The published theorem `splitTorusCentralizerReductive` (module
   [`Rational/SplitTorusCentralizerReductiveProof`](../Rational/SplitTorusCentralizerReductiveProof.md))
   is applied to `G`, the split torus `s`, and the representative `j`. The
   split-torus hypothesis is `d.maximalSplit.1.1`. The result is that `M` is
   connected reductive.
3. The published theorem `derivedSubgroupSemisimple` (module
   [`Derived/SemisimpleProof`](../Derived/SemisimpleProof.md)) is applied to
   `M` and `i`. It gives `IsSemisimple D`. In particular, `D` has a finite
   scheme-theoretic centre.

### Anisotropy

The Library lemma `isAnisotropic_iff` reduces `IsAnisotropic D` to the
following claim. For every finite type `I : Type u` and every closed subgroup
embedding `t : splitTorus I ⟶ D` of the split torus `𝔾_m^I`, the type `I` is
empty. Fix such `I` and `t`.

4. **Points of `M` centralize `S`.** Let `m` be a point of `M` over a test
   scheme `U`. Then `m ≫ j` lies in `torusCentralizer s` over `U`, because `j`
   represents that subgroup functor (the second component of
   `IsRepresentedBy`). By the definition of the centralizer, `m ≫ j` commutes
   with `y ≫ s` for every point `y` of `S` over `U`.
5. **`t` maps into `S`.** By step 4, applied to the points
   `x ≫ t ≫ i` of `M`, the composite `t ≫ i ≫ j : splitTorus I ⟶ G` commutes
   with `s` pointwise. The published lemma
   `IsMaximalSplitTorus.exists_factor_of_commute` (module
   [`Rational/SplitTorusFactorization`](../Rational/SplitTorusFactorization.md))
   applies to the maximal split torus `d.maximalSplit` and to the split torus
   `splitTorus I` (`isSplitTorus_splitTorus`). It gives `f : splitTorus I ⟶ S`
   with `f ≫ s = t ≫ i ≫ j`.
6. **`t` is central in `D`.** Let `x` be a point of `splitTorus I` over `U`,
   `a : T' ⟶ U` a morphism of test schemes, and `h` a point of `D` over `T'`.
   We must show that `a ≫ x ≫ t` and `h` commute in `D`. The maps `i` and `j`
   are monomorphisms: `i` is a closed immersion by `IsDerivedSubgroup`, and `j`
   is a monomorphism by `IsRepresentedBy`. They are group homomorphisms, so
   it suffices to check the commutation after composing with `i ≫ j`.
   There `a ≫ x ≫ t ≫ i ≫ j = (a ≫ x ≫ f) ≫ s` is a point of `S`, and
   `h ≫ i ≫ j` comes from the point `h ≫ i` of `M`. They commute by step 4.
   This proves `IsCentral t`.
7. **A central closed split torus of a semisimple group is trivial.** The
   helper theorem `IsSemisimple.isEmpty_of_isCentral_splitTorus` in this
   module (described below) turns `IsSemisimple D`, closedness of `t` and
   `IsCentral t` into `IsEmpty I`.

### The helper theorem

`IsSemisimple.isEmpty_of_isCentral_splitTorus` assumes a semisimple `k`-group
`D`, a finite type `I : Type u`, and a closed subgroup embedding
`t : splitTorus I ⟶ D` with `IsCentral t`. It concludes `IsEmpty I`.

- `hD.hasFiniteCenter` gives a closed subgroup `z : Z ⟶ D` that represents the
  full centre `center D`, and `Z` is finite over `k`. By
  `isCentral_iff_range_le_center`, the range of `t` lies in `center D`. So
  `t = t' ≫ z` with `t' = liftOfLE t` (`IsRepresentedBy.liftOfLE_comp`).
- Let `q : Z ⟶ 1` be the map to the trivial group. Its underlying scheme
  morphism is the structure morphism of `Z`, which is finite. The torus
  `splitTorus I` is smooth, affine and connected (`IsSplitTorus`). The
  published lemma `finiteHom_cancel` (module
  [`CentralIsogeny/Uniqueness`](../CentralIsogeny/Uniqueness.md)) therefore
  cancels `q` on maps out of it. Both `t' ≫ q` and `0 ≫ q` are maps into the
  trivial group, so they are equal. Hence `t' = 0`, and so `t = 0`.
- `t` is a closed immersion, hence a monomorphism. For each `a : I` the
  coordinate cocharacter `splitTorus.single a : 𝔾_m ⟶ splitTorus I`
  satisfies `single a ≫ t = 0 = 0 ≫ t`. So `single a = 0`, which is checked
  on points with `CommGroupScheme.hom_ext_points`. Composing with the
  projection `splitTorus.proj a` and using `single_comp_proj` gives
  `𝟙 𝔾_m = 0`. Applying the isomorphism `gmEndEquiv : End(𝔾_m) ≃+ ℤ` gives
  `1 = 0` in `ℤ`. This is a contradiction, so `I` has no element.

The last step follows the same pattern as the published proof of
`IsMaximalSplitTorus.isAnisotropic_quotient` in
[`Rational/MaximalSplitQuotientAnisotropy`](../Rational/MaximalSplitQuotientAnisotropy.md).

## Relation to the literature

J. Tits, *Classification of algebraic semisimple groups* (1966), §2.2, calls
`𝒟𝒵(S)` the semisimple anisotropic kernel of `G` without proving that it is
semisimple and anisotropic. The Lean proof does not follow a specific printed
argument. It combines the Library results above, using the standard reasoning
(Borel–Tits): `Z(S)` is connected reductive, its derived group is semisimple,
and a split torus in `𝒟𝒵(S)` centralizes `S`. By maximality it then lies in
`S`, so it is central in `𝒟𝒵(S)`, and the centre of a semisimple group is
finite, so it contains no nontrivial torus.
