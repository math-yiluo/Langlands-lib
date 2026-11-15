# KP Lemma C.5.3 for multipliable roots, from valued unitary coordinates

Lean module: `Langlands.BruhatTits.IntegralModels.RootDepthKernelMultipliable`.

This module proves the conclusion of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Lemma C.5.3 (printed page 705), for a *multipliable* relative
root `a` (one with `2 • a` also a relative root). It assumes the root has valued
scheme-level unitary coordinates, the record
`ValuedUnitaryRootGroupCoordinates` of the published module
`Langlands.Geometry.Building.MultipliableRootGroupCoordinates`. Combined with
the published no-higher-root case
`unramifiedNoHigherRootDepthKernel`, it gives the *conditional* theorem

`unramifiedRootDepthKernel_of_multipliableCoordinates :
  MultipliableRootGroupCoordinatesExistenceStatement.{u} →
    UnramifiedRootDepthKernelStatement.{u}`.

The hypothesis `MultipliableRootGroupCoordinatesExistenceStatement` is **not**
proved here. Hence neither the main Task 6392 target
`UnramifiedRootDepthKernelStatement` nor C.5.3 for multipliable roots is proved
unconditionally by this module.

## Provenance

KP prove Lemma C.5.3 in one line: "This follows from Facts C.2.1 and C.3.1 and
Lemma C.4.4." For a multipliable root, KP Proposition C.5.1 (printed pages
703–704) writes `U_a = R_{E/K} U_{L/E}` for finite separable `E / K` and quadratic
`L / E`. It uses the valuation of `E` normalized by `ω_E(E^×) = ℤ`, reindexes
depths by the ramification index `e` of `E / K`, and sets
`U_{a,x,r} = R_{O_E/O} U'_{a,x,r}`, where `U'_{a,x,r}` is the `O_E`-model of
§C.4. Lemma C.4.4 (printed page 701) says the kernel between special fibres of
the `§C.4` models `X_{r_2,s_2} → X_{r_1,s_1}` is smooth, connected and
unipotent.

This module follows that route on the Library's objects:

- the KP model `R_{O_E/O} X_{r',2r'}` is the published canonical restricted
  lattice model `IsRamifiedQuadraticValuation.canonicalWeilLatticeModel`
  (module `Langlands.GroupScheme.Examples.SU3RootUnitaryCanonicalWeilModel`);
- the kernel statement for it is the published
  `canonicalWeilLatticeModel_kernel_properties`, the Library's form of Lemma C.4.4
  combined with Weil restriction;
- the normalization `ω_E(E^×) = ℤ` is realized by rescaling the prolonged
  valuation by a positive real `c`, the ramification index in KP's notation;
- KP's translation `U_{a,y,r} = U_{a,x,r + a(x - y)}` (Lemma 6.1.6) is the
  published `IntegerValuationBuildingData.val_apply_eq_add`.

Two parts of the formulation are internal to this project:

- the exact depth `r' = c (r - a(y - origin)) - μ / 2`, which uses the
  unshifted origin of the record (`towerDepth (u, v) = ω(v) / 2`, KP
  Construction 6.1.17) instead of KP's adjusted Chevalley valuation
  (Definition 6.1.20, which carries the `μ` shift);
- the transfer to arbitrary supplied presentations through the published
  presentation-invariance theorem
  `RootFiltrationModelData.specialFibreKernel_properties_of_presentation`
  (module `Langlands.BruhatTits.IntegralModels.RootModelPresentationIso`).

## Normalizing the prolonged valuation on a separable tower

Namespace `Langlands.GroupScheme.SU3Root`, section `SeparableTower`. Setting:

- `k` is a field with a `ℤ`-valued valuation `v`, surjective (`hv`), whose
  valuation ring is henselian (`hH`);
- `k → E → L` is a scalar tower of fields;
- `E / k` is finite separable, `L / E` is quadratic separable, and `L / k` is
  separable;
- `FieldTheory.henselianSeparableAddValuation v hH E` (written `w_E`, and
  similarly `w_L`) is the published unique prolongation of `v` to a separable
  extension, normalized by `w(k^×) = ℤ`.

Declarations:

- `towerScale v hv hH E` is the positive real `c` chosen by the published
  `FieldTheory.henselianSeparable_exists_integer_scale`.
  `towerScale_pos` gives `0 < c`. `towerScale_spec` gives two facts:
  - for every `a ≠ 0` in `E`, `w_E(a)` is a real `t` with `c * t` an integer;
  - some `ϖ ∈ E` has `w_E(ϖ) = 1 / c`.
- `towerNormalizedValuation v hv hH E L` is the additive valuation
  `rescaleValuation w_L c` on `L`, i.e. `x ↦ c · w_L(x)` with `c · ⊤ = ⊤`
  (`towerNormalizedValuation_apply`, by `rfl`).
- `henselianSeparableAddValuation_tower`: `w_L(a) = w_E(a)` for `a ∈ E`. This is
  `henselianSeparableAddValuation_algHom` applied to the `k`-algebra map
  `E → L`. Hence `towerNormalizedValuation_algebraMap`: the normalized value of
  `a ∈ E` is `c · w_E(a)`.
- Two private lemmas: for `c > 0`, `0 ≤ c · x ↔ 0 ≤ x` and `0 < c · x ↔ 0 < x`
  on `WithTop ℝ`, from strict monotonicity of `scaleTop c`.
- `towerNormalizedValuation_isRamified`: if the residue field of `v` is
  algebraically closed, the normalized valuation satisfies
  `IsRamifiedQuadraticValuation E L`. Proof: apply the published
  `IsRamifiedQuadraticValuation.of_hasResidueQuadraticRoots` with `ϖ` from
  `towerScale_spec`. Its four hypotheses hold as follows:
  - conjugation invariance comes from
    `FieldTheory.henselianSeparableAddValuation_invariant`, applied to the
    nontrivial automorphism of `L / E` restricted to a `k`-automorphism;
  - integer values on `E^×` come from `towerScale_spec`;
  - `ϖ` has value `c · (1 / c) = 1`;
  - approximate roots of monic integral quadratics come from the published
    `FieldTheory.henselianSeparable_exists_quadratic_approxRoot`, after
    removing the factor `c` with the private lemmas.
- `towerNormalizedValuation_isValuationIntegers`: the published ring of integers
  `FieldTheory.henselianSeparableIntegers v hH E` is the ring of integers of `E`
  for the normalized valuation (`IsValuationIntegers`), i.e. `a ∈ E` lies in its
  image iff `0 ≤ c · w_E(a)`. Proof: remove `c`, then use
  `FieldTheory.mem_henselianSeparableIntegers`.

## The filtration product at doubled central depth

`IsRamifiedQuadraticValuation.mem_filtrationProduct_double_iff`. Setting:

- `L / K` is a quadratic separable extension;
- `ω` is an additive valuation on `L` with `hω : IsRamifiedQuadraticValuation K L ω`;
- `μ = mu K L ω`.

For a real `r` and a unitary parameter `p = (u, v)`,
`p ∈ hω.filtrationProduct r (2 r)` iff `2 r + μ ≤ ω(v)`. Proof: the central
filtration at depth `2 r + μ` lies in the filtration at depth `r + μ / 2`, since
both conditions on `v` become `2 r + μ ≤ ω(v)`. So the join defining
`filtrationProduct` is the second filtration, whose membership is
`Parameters.mem_filtration`. This is KP's remark that `X(K)_r · Z(K)_{2r} = X(K)_r`.

## Integral models of multipliable root filtration groups

Namespace `Langlands.Geometry.Building.ValuedUnitaryRootGroupCoordinates`. Setting:

- `F` is a nonarchimedean local field with maximal unramified field
  `K = inertiaFixedField F`;
- `v = MaximalUnramified.valuation F` is the Library's surjective integer
  valuation on `K`, with henselian valuation ring `O = v.valuationSubring`;
- `G` is an affine group scheme over `Spec K`, and
  `B : MaximalUnramified.BuildingData F G`;
- `a` is a relative root of `B.i`;
- `P : ValuedUnitaryRootGroupCoordinates B a` has fields `E = P.base` and
  `L = P.extension`, inclusion `R_{E/K} U_{L/E} → G`, and origin `P.origin`.

Instances `henselianSeparableIntegers_finite` and
`henselianSeparableIntegers_free`: for a finite separable `E / K`, the ring of
integers `O_E` of `E` is finite and free as an `O`-module. These are the
published `FieldTheory.henselianSeparableIntegers_finite` and `_free` with
`MaximalUnramified.valuation_surjective F`. The Weil restriction along
`O → O_E` needs them.

Definitions attached to `P`:

- `P.integers`: `O_E = FieldTheory.henselianSeparableIntegers v hH E`.
- `P.scale`: `c = towerScale v hv hH E`.
- `P.normalizedValuation`: `ω = towerNormalizedValuation v hv hH E L` on `L`.
- `P.normalizedValuation_isRamified` and
  `P.normalizedValuation_isValuationIntegers`: the two theorems above. For the
  first, the residue field of `O` is algebraically closed by
  `MaximalUnramified.residueField_isAlgClosed F`.
- `P.weilGroup`: the published `canonicalWeilGroup O K O_E E L`, i.e. the generic
  form of `R_{O_E/O} U_{L/E}`. This is definitionally the source of
  `P.inclusion`.
- `P.pointsEquiv`: the published `canonicalWeilRationalPointsEquiv`, a
  multiplicative equivalence between `K`-points of `P.weilGroup` and unitary
  parameters `(u, v)` over `L / E`.
- `P.depthShift y = rootForm B.i a (y -ᵥ P.origin)`, i.e. `a(y - origin)` for a
  point `y` of the apartment.
- `P.latticeDepth y r = c · (r - a(y - origin)) - μ / 2`, where
  `μ = mu E L ω`.
- `P.latticeModel y r`: the published canonical restricted lattice model
  `canonicalWeilLatticeModel` of `P.weilGroup` over `O` at depths
  `(r', 2 r')`, where `r' = P.latticeDepth y r`.

Theorems:

- `val_map_inclusion`: for every `K`-point `g` of `P.weilGroup`, the value
  `y.val a` at the image of `g` in `G` equals
  `towerDepth K E L v hH (P.pointsEquiv g) + a(y - origin)`. Proof:
  `IntegerValuationBuildingData.val_apply_eq_add` rewrites `y.val a` as
  `P.origin.val a + a(y - origin)`. The record field `P.depth` gives the value at
  the origin, after inserting `P.pointsEquiv.symm (P.pointsEquiv g) = g`.
- A private real-arithmetic lemma: for `c > 0`, reals `m, d, r` and
  `t ∈ WithTop ℝ`,
  `2 (c (r - d) - m / 2) + m ≤ c · t ↔ r ≤ t / 2 + d`.
  At `⊤` both sides hold. For finite `t` it is a linear inequality, closed by
  `nlinarith`.
- `mem_integralPoints_latticeModel_iff`: a `K`-point `g` of `P.weilGroup` is an
  integral point of `P.latticeModel y r` iff `r ≤ y.val a (image of g)`. Proof:
  - the published `mem_integralPoints_canonicalWeilLatticeModel_iff` reduces
    integrality to `P.pointsEquiv g ∈ filtrationProduct r' (2 r')`;
  - `mem_filtrationProduct_double_iff` turns this into
    `2 r' + μ ≤ ω(v) = c · w_L(v)`;
  - `val_map_inclusion` with `towerDepth (u, v) = w_L(v) / 2` and the private
    lemma finish the proof.
- `latticeModel_integralPoints_map`: the image in `G(K)` of the integral points
  of `P.latticeModel y r` is the filtration subgroup
  `B.apartment.filtration y a r`, i.e. `U_{a,y,r}`. Proof: `P.isRootSubgroup`
  identifies the `K`-points of `P.weilGroup` with the root group `U_a(K)`
  (`pointsEquiv` and `pointsEquiv_symm_comp` of `IsRepresentedBy`). Then the
  previous theorem compares the depth conditions.

## The entry definition

`rootFiltrationModelData P y r :
RootFiltrationModelData O K B.apartment y a r` is a presentation of `U_{a,y,r}`.
Its fields:

- root group `P.weilGroup`, inclusion `P.inclusion`, and root-subgroup witness
  `P.isRootSubgroup`;
- model `P.latticeModel y r`;
- smoothness and geometrically connected fibres from the published
  `canonicalWeilLatticeModel_isSmooth` and
  `canonicalWeilLatticeModel_hasGeometricallyConnectedFibres`;
- integral-point image `latticeModel_integralPoints_map`.

This is the Library form of KP's `U_{a,y,r} = R_{O_E/O} U'_{a,y,r}` for a
multipliable root.

## The kernel statement

`latticeDepth_mono`: `r ≤ s` implies `P.latticeDepth y r ≤ P.latticeDepth y s`,
since `c > 0`.

`specialFibreKernel_properties` (with explicit argument `P`). Hypotheses:

- `O'` (Lean name `O`) is a valuation subring of `K` equal to
  `v.valuationSubring` (`hO`);
- `hext` says smooth model maps extend over `O'`
  (`IntegralModel.HasSmoothHomExtension`);
- `y` is a point of the apartment and `r ≤ s`;
- `U` and `V` are any presentations over `O'` of `U_{a,y,r}` and `U_{a,y,s}`;
- `g : V.rootGroup ⟶ U.rootGroup` satisfies `g ≫ U.inclusion = V.inclusion`,
  and `φ` is a model map over `g`.

Conclusion: the kernel of the special-fibre map of `φ` is smooth, connected
and unipotent.

Proof:

1. Substitute `hO`.
2. Let `r' ≤ s'` be the lattice depths of `r ≤ s` (`latticeDepth_mono`), so
   `2 r' ≤ 2 s'`.
3. The published `canonicalWeilLatticeTransition` gives a model map
   `ψ : P.latticeModel y s ⟶ P.latticeModel y r` over the identity of
   `P.weilGroup`.
4. The published `canonicalWeilLatticeModel_kernel_properties` shows that the
   kernel of the special-fibre map of `ψ` is smooth, connected and unipotent.
5. `specialFibreKernel_properties_of_presentation` transfers these properties to
   `φ`. It is applied to the presentations `U`, `V`,
   `P.rootFiltrationModelData y r` and `P.rootFiltrationModelData y s`, with
   the maps `g` and `𝟙` and the extension property `hext`.

## The conditional main theorem

`Langlands.BruhatTits.IntegralModels.unramifiedRootDepthKernel_of_multipliableCoordinates`.
Assume `MultipliableRootGroupCoordinatesExistenceStatement.{u}`: every
multipliable relative root of the actual maximal unramified building data has
valued unitary coordinates. Then `UnramifiedRootDepthKernelStatement.{u}`
holds.

Proof: introduce the data of the target statement and split on whether `2 • a`
is a relative root.

- If it is, the hypothesis gives `P`. Apply `P.specialFibreKernel_properties` with:
  - `MaximalUnramified.valuationSubring_eq F`, identifying `O` with
    `fixedFieldIntegers F`;
  - the extension property
    `IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F`.
- If it is not, `G` is smooth (it is connected reductive), and `2 • a ∉ Φ` as a
  `ℤ`-multiple. The published
  `hasOppositeFactorPairs.hasNoHigherRoots_of_two_not_mem`, applied to
  `C.hasOppositeFactorPairs` and the torus property extracted from
  `C.isMaximalSplitTorus`, gives `RelativeRoot.HasNoHigherRoots C.i a`. The published
  `unramifiedNoHigherRootDepthKernel` then applies.

The statements and proofs use only the standard axioms. They contain no
`sorry` and no new axioms.
