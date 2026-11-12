# A pseudo-reductive group that is not reductive: proof

Worker 3483 (author of the proof, from the shared draft of Task 3483); submitted
by Worker 221 for Task 5610.

`Langlands.GroupScheme.weilGmPurelyInseparablePseudoReductive.{u}` proves the
proposition
`Langlands.GroupScheme.WeilGmPurelyInseparablePseudoReductiveStatement.{u}`
(module `Langlands.GroupScheme.Reductive.WeilGmPurelyInseparableStatement`). The
theorem's type is exactly that proposition, with no added hypotheses.

## The statement

For fields `k` and `k'` with `k'/k` finite, purely inseparable and of degree
`1 < [k' : k]`, the Weil restriction
`G = WeilGm.groupScheme (CommRingCat.of k) k'` of `𝔾_m` (points `(k' ⊗_k A)ˣ`)
satisfies `IsPseudoReductive G` and `¬ IsConnectedReductive G`. This is
Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2015), Example 1.1.3; the
statement's Markdown gives the quotations and the correspondence.

## The proof

The auxiliary declarations are in the namespace
`Langlands.GroupScheme.WeilGmPurelyInseparable`; none is private.

### The characteristic and a `p`-th root

`exists_pthRoot`: if `ExpChar k p`, then `p` is prime and some `b ∈ k'` lies
outside `k` while `b ^ p ∈ k`. An element `a ∉ k` exists because otherwise
`algebraMap k k'` would be bijective and `[k' : k] = 1`
(`Algebra.finrank_eq_one_iff_bijective_algebraMap`). If `p = 1`, pure
inseparability (`IsPurelyInseparable.pow_mem`) would put `a` itself in `k`. For
prime `p`, take the least `N` with `a ^ (p ^ N) ∈ k` (`Nat.find`); then `N ≥ 1`
and `b = a ^ (p ^ (N - 1))` works.

### Not connected reductive

- `exists_unit_pow_eq_one`: if `b ∉ k`, `b ^ p = c ∈ k`, and `β ^ p = c` in a
  nonzero `k`-algebra `R`, then `1 + (b ⊗ 1 - 1 ⊗ β)` is a unit of `k' ⊗ R` of
  order exactly `p`. The `p`-th power of `ε = b ⊗ 1 - 1 ⊗ β` is
  `c ⊗ 1 - 1 ⊗ c = 0` in characteristic `p`. A `k`-linear functional on `k'`
  vanishing on `1` and not on `b` (`Submodule.exists_dual_map_eq_bot_of_notMem`)
  shows `ε ≠ 0`.
- `eq_one_of_pow_char_eq_one`: in a field of characteristic `p`, `x ^ p = 1`
  forces `x = 1` (`frobenius_inj`).
- `not_isConnectedReductive`: `G` is commutative (`WeilGm.isCommMonObj`), hence
  solvable (`isSolvableGroupScheme_of_isCommMonObj`). A connected reductive
  solvable group is a torus
  (`IsConnectedReductive.isTorus_of_isSolvableGroupScheme`), so some field
  `K/k` splits `G`. Take `Ω` an algebraic closure of `K` and the test scheme
  `Spec Ω` over `Spec K`. Its points in the split torus are `I`-tuples of units
  of `Γ(Spec Ω) ≅ Ω` (`isoPointsEquiv`, `splitTorus.pointsEquiv`), which have no
  element of order `p`. Its points in `G_K` are
  `(k' ⊗_k Γ(Spec Ω))ˣ` (`GroupScheme.baseChangePointsEquiv`,
  `WeilGm.pointsEquiv`), and `Γ(Spec Ω) ≅ Ω` contains a `p`-th root of `c`. So
  `exists_unit_pow_eq_one` gives an element of order `p`, a contradiction.

### Trivial `k`-unipotent radical

- `isReduced_tensor_separableClosure`: `k' ⊗_k k_s` is a field, by the published
  `Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range`
  (module
  `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range`),
  since separable elements of `k'` lie in `k`
  (`IsPurelyInseparable.inseparable`). Hence it is reduced.
- `hasTrivialUnipotentRadical`: let `i : H ⟶ G` be a closed subgroup with `H`
  smooth and unipotent (connectedness and normality are not needed). `H` is
  affine, being closed in the affine `G`. The published
  `exists_hasUniformPowerExponent_of_isUnipotent`
  (`Rational/UnipotentPointsExponent`) gives `r` with `x ^ (p ^ r) = 1` for every
  point `x` of `H` over every test scheme. After base change to `k_s`, every
  rational point of `H_{k_s}` maps to a unit `u ∈ (k' ⊗_k k_s)ˣ`
  (`WeilGm.extensionUnitsEquiv`, `Torus/WeilRestrictionGaloisPoints`) with
  `u ^ (p ^ r) = 1`. So `u - 1` is nilpotent in a reduced ring, and `u = 1`.
  Rational points are dense in the smooth `H_{k_s}`
  (`PointTopology.hasDenseRationalPoints_of_smooth_of_isSepClosed`), which is
  reduced (`SmoothReducedProof.isReduced_of_smooth_over_field`), and `G_{k_s}` is
  separated, so `i_{k_s}` is the constant map `1`
  (`PointTopology.hom_ext_of_denseRationalPoints`). Faithfulness of base change
  along `Spec k_s → Spec k` (`(Over.pullback b).map_injective`, with
  `fieldExtension_fpqc`) gives `i = 1`, and therefore
  `SubgroupFunctor.range i = ⊥`.

### Connectedness

Choose a basis `b₁, …, bₙ` of `k'` (`Module.finBasis`) and `m` with
`bᵢ ^ (p ^ m) = cᵢ ∈ k` for all `i` (`exists_pow_mem_range`). Write `q = p ^ m`.

- `powPoly q c = ∑ cᵢ Xᵢ ^ q` in `k[X₁, …, Xₙ]`, and
  `locAlg q c = k[X₁, …, Xₙ][(∑ cᵢ Xᵢ ^ q)⁻¹]`.
- `coordEquiv`: `r ↦ ∑ bᵢ ⊗ rᵢ` identifies `Rⁿ` with `k' ⊗_k R`
  (`Algebra.TensorProduct.basis`, `TensorProduct.comm`); `lTensor_coordEquiv` is
  its naturality.
- `coordEquiv_pow`: `(∑ bᵢ ⊗ rᵢ) ^ q = 1 ⊗ (∑ cᵢ rᵢ ^ q)` in characteristic `p`
  (`sum_pow_char_pow`).
- `isUnit_of_isUnit_one_tmul`: if `1 ⊗ s` is a unit of `k' ⊗_k R` then `s` is a
  unit; apply `φ ⊗ id` for a `k`-linear `φ : k' → k` with `φ 1 = 1`. Hence
  `isUnit_coordEquiv_iff`: `∑ bᵢ ⊗ rᵢ` is a unit if and only if `∑ cᵢ rᵢ ^ q` is.
- `corep`: `locAlg q c` corepresents `R ↦ (k' ⊗_k R)ˣ` (the functor
  `WeilGm.functor` that `WeilGm.groupScheme` is built from). A `k`-algebra map
  `f` goes to the unit with coordinates `f(Xᵢ)`. A unit `u` goes to the map
  `IsLocalization.Away.liftAlgHom` of the evaluation at its coordinates
  (`aeval_powPoly_isUnit`, `lift_algebraMap`).
- `powPoly_ne_zero`: evaluating at the first basis vector gives `c₁ ≠ 0`, so
  `locAlg q c` is a domain (`IsLocalization.isDomain_localization`).
- `connectedSpace_groupScheme`: `CorepresentableBy.uniqueUpToIso` identifies the
  coordinate algebra of `G` with `locAlg q c`. Applying `algSpec` and
  `Scheme.homeoOfIso` gives a homeomorphism from the connected space
  `Spec (locAlg q c)` onto the underlying space of `G`.

### Assembly

`weilGmPurelyInseparablePseudoReductive` combines `WeilGm.smooth`
(`Torus/WeilRestriction`), affineness of `G` (its structure map is `Spec` of an
algebra map), `connectedSpace_groupScheme` and `hasTrivialUnipotentRadical`
into `IsPseudoReductive G`, and uses `not_isConnectedReductive` for the second
conjunct.

CGP prove pseudo-reductivity by noting that `G(k_s) = (k' ⊗_k k_s)ˣ` has no
nontrivial `p`-torsion, and non-reductivity by the unipotent quotient
`G/GL_1`. The Lean proof uses the same `k_s`-point argument for the first part,
made rigorous with density of rational points. For the second part it uses an
element of order `p` over an algebraically closed field instead of the
quotient `G/GL_1`.

## Published inputs

Every published Library theorem the proof uses, with its module (all names in
the namespace `Langlands.` unless written in full):

- `GroupScheme.IsConnectedReductive.isTorus_of_isSolvableGroupScheme` —
  `Langlands.GroupScheme.Rational.ReductiveSolvableTorus`.
- `GroupScheme.isSolvableGroupScheme_of_isCommMonObj` —
  `Langlands.GroupScheme.Torus.Geometry`.
- `GroupScheme.WeilGm.isCommMonObj` —
  `Langlands.GroupScheme.Torus.WeilRestrictionCommutative`.
- `GroupScheme.WeilGm.smooth` — `Langlands.GroupScheme.Torus.WeilRestriction`.
- `GroupScheme.baseChange_isCommMonObj` (an instance, used implicitly for the
  commutative base change) — `Langlands.AbelianScheme.Multiplication`.
- `GroupScheme.exists_hasUniformPowerExponent_of_isUnipotent` —
  `Langlands.GroupScheme.Rational.UnipotentPointsExponent`.
- `GroupScheme.fieldExtension_fpqc` — `Langlands.GroupScheme.BaseChangeReflection`.
- `AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field` —
  `Langlands.AlgebraicGeometry.SmoothReducedProof`.
- `AlgebraicGeometry.PointTopology.hasDenseRationalPoints_of_smooth_of_isSepClosed`
  — `Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity`.
- `AlgebraicGeometry.PointTopology.hom_ext_of_denseRationalPoints` —
  `Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt`.
- `GroupScheme.SubgroupFunctor.bot_carrier`, `GroupScheme.SubgroupFunctor.mem_range`
  and `GroupScheme.SubgroupFunctor.ext` — `Langlands.GroupScheme.SubgroupFunctor`.
- `Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range`
  (full name) —
  `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range`.

Published definitions and equivalences used: `GroupScheme.WeilGm.groupScheme`,
`GroupScheme.WeilGm.functor`, `GroupScheme.WeilGm.pointsEquiv` and
`GroupScheme.WeilGm.corepresentableBy`
(`Langlands.GroupScheme.Torus.WeilRestriction`);
`GroupScheme.WeilGm.extensionUnitsEquiv`
(`Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints`);
`GroupScheme.isoPointsEquiv`, `GroupScheme.splitTorus.pointsEquiv`
(`Langlands.GroupScheme.Torus.Split`); `GroupScheme.baseChangePointsEquiv`
(`Langlands.AbelianScheme.KernelBaseChange`); `GroupScheme.baseChange`
(`Langlands.AbelianScheme.GroupScheme`);
`GroupScheme.GaloisPointComparison.baseMap`
(`Langlands.GroupScheme.GaloisPointRational`); `GroupScheme.rationalPoints`
(`Langlands.GroupScheme.Rational.Characters`). All other lemmas are from
Mathlib or are the auxiliary declarations above.

## Checks

The module compiles against the Library with no errors or warnings, and
`#print axioms` for `weilGmPurelyInseparablePseudoReductive` lists only
`propext`, `Classical.choice` and `Quot.sound`. The list of published inputs
above was produced by collecting every constant from a `Langlands.*` module
that occurs in the types and values of this module's declarations.
