# Harris's `D_m(K_ℓ)` and the forms of level `K(n)` along the tower `K_ℓ(n)`

Author: Worker 61. Built on the published
`Langlands.Shimura.DefiniteFormsFunctions` (Worker 61: `rightRegular`,
`functionRightRegular`, `invariantsPullback`, `invariantsDescend`,
`functionModuleRep`, `functionModuleForms`, `congruenceFunctionEquiv`,
`congruenceFunctionEquiv_apply`), `Langlands.Shimura.DefiniteFormsTower`
(Worker 61: `CongruenceTower`, `exists_lower_le`, `isSmooth_iff_iSup`,
`congruenceLevel_mono`, `compactSpace_localLevel`),
`Langlands.Shimura.DefiniteFormsDoubleCoset` (Worker 61: `localLevel`,
`localLevelMap`, `localLevelMap_surjective`, `ellModuleForms`,
`LocalLevelFree`, `congruenceLevel`, `congruenceLevel_le`,
`congruenceLevel_subgroupOf` and the normality instance of
`(congruenceLevel σ ℓ K H).subgroupOf K`),
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`, `mem_forms`,
`levelAction`), `Langlands.Shimura.EquivariantFormsDoubleCoset` (Worker 61:
`DoubleCosets`, `exists_eq_mul_out_mul`, `forms_apply_mul_mul`),
`Langlands.Topology.GroupAction.CompactLocallyConstantStabilizer` (Worker 56:
`CompactAction.functionStabilizer`, `functionStabilizer_isOpen`),
`Langlands.Representation.Smooth.Definitions` (`fixedVectors`, `IsSmooth`),
and on Worker 57's similitude groups (`AlgebraInvolution.FiniteAdelicPoints`,
`finiteAdelicDiagonal`, the topology on `σ.Points`). From Mathlib it uses
locally constant functions (`LocallyConstant`), direct limits of modules
(`Module.DirectLimit`, `Module.DirectLimit.lift`, `lift_injective`,
`DirectedSystem`), quotient groups (`Subgroup.quotientMapOfLE`,
`QuotientGroup.induction_on`), opposite groups (`MulOpposite`,
`Subgroup.unop`), suprema of directed families of submodules
(`Submodule.mem_iSup_of_directed`) and representations
(`Representation.invariants`, `Representation.Equiv`).

The module lets the level `n` of Harris 1999, p.308, vary. It shows that
Harris's `D_m(K_ℓ)` is a smooth representation and the direct limit of the
`D_m(K_{ℓ,n})`, forms the union over `n` of the forms of level `K(n)`,
proves (3.10) for this union, and identifies the forms
`𝒜_ℓ(GJ, D_m(K_ℓ), K)` with coefficients in `D_m(K_ℓ)` with the same union.
Harris's coefficient ring `𝒪/ℓ^m𝒪` becomes an arbitrary commutative ring
`R`, and his continuous functions with discrete values become locally
constant functions.

## Conventions

As in the published `DefiniteFormsDoubleCoset.md` and
`DefiniteFormsFunctions.md`: `σ : AlgebraInvolution ℚ A` is an involution of
a finite-dimensional `ℚ`-algebra `A`, `σ.FiniteAdelicPoints` is Harris's
`GJ(𝔸^f)`, with the rational points embedded by `σ.finiteAdelicDiagonal`,
`ℓ` is a finite place of `ℚ` and `K` a subgroup of `σ.FiniteAdelicPoints`.
`localLevel σ ℓ K` (Harris's `K_ℓ`) is the image of `K` in the `ℓ`-adic
points, with the subspace topology, and `localLevelMap σ ℓ K : K →* K_ℓ` is
`k ↦ k_ℓ`. For a subgroup `H` of `K_ℓ`, `congruenceLevel σ ℓ K H` (Harris's
`K(n)` for `H = K_ℓ(n)`) is the set of `k ∈ K` with `k_ℓ ∈ H`.
`DoubleCosets σ.finiteAdelicDiagonal K` is `GJ(ℚ)\GJ(𝔸^f)/K` and `x.out` is
Mathlib's chosen representative of a class `x`. `LocalLevelFree σ ℓ K` is
Harris's hypothesis (3.6). For a topological group `G` and an `R`-module
`M`, `rightRegular R G M` is the representation of `G` on
`LocallyConstant G M` by right translation, `(g • f)(x) = f (x * g)`
(Harris's `D_m(K_ℓ)` for `G = K_ℓ`, `M = R`); `functionModuleRep σ ℓ K R M`
is `rightRegular R K_ℓ M`, and `functionModuleForms σ ℓ K R M` is
`𝒜_ℓ(GJ, D(K_ℓ), K)` defined by analogy with (3.7): the functions
`f : GJ(𝔸^f) → LocallyConstant K_ℓ M` with `f (γ g) = f g` for rational `γ`
and `f (g k) = rightRegular (k_ℓ)⁻¹ (f g)` for `k ∈ K`. A tower
`T : CongruenceTower G` is a decreasing sequence `T.lower n` (Harris's
`K_ℓ(n)`) of open normal subgroups with trivial intersection.

## Smoothness and the direct limit

Namespace `Langlands.Shimura.FunctionModule`, for a compact topological
group `G` (`[IsTopologicalGroup G] [CompactSpace G]`):

- `rightStabilizer f`, for `f : LocallyConstant G M`: the open subgroup of
  the `h` with `f (x * h) = f x` for all `x` (`mem_rightStabilizer`). It is
  the published `CompactAction.functionStabilizer` of `f` for the action of
  `Gᵐᵒᵖ` on `G` by right multiplication, transported to `G` by Mathlib's
  `Subgroup.unop`; it is open by the published `functionStabilizer_isOpen`
  and the continuity of `MulOpposite.op`.
- `isSmooth_rightRegular R`: `rightRegular R G M` is smooth, since
  `rightStabilizer f` fixes `f`.

Namespace `Langlands.CongruenceTower`, for `T : CongruenceTower G`:

- `exists_lower_apply_mul T f` (compact `G`): some `T.lower n` fixes `f` by
  right translation, since `rightStabilizer f` contains some `T.lower n`
  (`exists_lower_le`).
- `exists_mem_fixedVectors_rightRegular T R f` (compact `G`): `f` lies in
  `fixedVectors (rightRegular R G M) (T.lower n)` for some `n`.
- `iSup_fixedVectors_rightRegular T R` (compact `G`):
  `⨆ n, fixedVectors (rightRegular R G M) (T.lower n) = ⊤`.
- `quotientFunctionsMap T R h`, for `h : m ≤ n`: the `R`-linear pullback
  `(G ⧸ T.lower m → M) → (G ⧸ T.lower n → M)` along the map
  `G ⧸ T.lower n → G ⧸ T.lower m` of Mathlib's `Subgroup.quotientMapOfLE`
  (`quotientFunctionsMap_apply_mk`); the instance
  `directedSystem_quotientFunctions` records that these maps form a
  directed system.
- `quotientFunctionsPullback T R n`: the `R`-linear map
  `(G ⧸ T.lower n → M) → LocallyConstant G M`, `φ ↦ (y ↦ φ [y])`
  (`quotientFunctionsPullback_apply`; the function is locally constant since
  `T.lower n` is open, via the published `invariantsPullback`). It is
  compatible with the transition maps (`quotientFunctionsPullback_map`),
  injective (`quotientFunctionsPullback_injective`) and intertwines right
  translation by `[g]` with right translation by `g`
  (`quotientFunctionsPullback_comm`).
- `directLimitEquiv T R` (compact `G`): the `R`-linear equivalence from
  Mathlib's `Module.DirectLimit` of the functions on the `G ⧸ T.lower n`
  along `quotientFunctionsMap` to `LocallyConstant G M`, induced by the
  `quotientFunctionsPullback T R n` (`directLimitEquiv_of`). Injectivity is
  Mathlib's `Module.DirectLimit.lift_injective`; surjectivity is
  `exists_mem_fixedVectors_rightRegular` with the published
  `invariantsDescend`. This is `D_m(K_ℓ) = lim→_n D_m(K_{ℓ,n})` for
  `G = K_ℓ`. Only the linear structure is packaged; the action of `G` is
  recorded by `quotientFunctionsPullback_comm`.

## Forms along the tower

Namespace `Langlands.Shimura.DefiniteForms`, with `σ`, `ℓ`, `K` as in the
conventions, a commutative ring `R` and an `R`-module `M`.

- `localLevelSection σ ℓ K y`: a chosen `k ∈ K` with `k_ℓ = y`
  (`Function.surjInv` of the published `localLevelMap_surjective`;
  `localLevelMap_localLevelSection`). The results below do not depend on
  the choice: their statements either do not mention it or hold for every
  preimage.
- `congruenceForms σ ℓ R M H` (an abbreviation): the published
  `forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)` for the trivial
  representation of `K` on `M` restricted to `K(n)`, Harris's
  `𝒜_ℓ(GJ, M, K(n))`, on which the published `levelAction` acts.
  `mem_congruenceForms`: its elements are the `f : GJ(𝔸^f) → M` with
  `f (γ g) = f g` for rational `γ` and `f (g k) = f g` for `k ∈ K(n)`.
- `congruenceForms_apply_mul_eq hf g hk`: for such `f` and `k, k' ∈ K` with
  `k_ℓ⁻¹ k'_ℓ ∈ H`, `f (g k') = f (g k)`.
- `translate_mem_congruenceForms hf k`: for normal `H` and `k ∈ K`,
  `g ↦ f (g k)` is again a form of level `K(n)` (normality of `K(n)` in
  `K`).
- `congruenceForms_anti σ ℓ R M h`: `H' ≤ H` implies
  `congruenceForms σ ℓ R M H ≤ congruenceForms σ ℓ R M H'`.

For a tower `T : CongruenceTower (localLevel σ ℓ K)`:

- `monotone_congruenceForms σ ℓ T R M`: the forms of level `K(n)` increase
  with `n`.
- `towerForms σ ℓ T R M`: the submodule
  `⨆ n, congruenceForms σ ℓ R M (T.lower n)` of the functions
  `GJ(𝔸^f) → M`. `mem_towerForms`: its elements are the forms of level some
  `K(n)` (the family is directed); `congruenceForms_le_towerForms`.
- `towerAction σ ℓ T R M`: the representation of `K` on `towerForms` by
  right translation, `(k • f)(g) = f (g * k)` (`towerAction_apply_coe`);
  on each `𝒜_ℓ(GJ, M, K(n))` this is the formula of `levelAction` for
  trivial coefficients.

### (3.10) along the tower

With `M = R`:

- `towerFunctionMap σ ℓ R`: the `R`-linear map from the functions
  `GJ(𝔸^f) → R` to the functions `K_ℓ → (DoubleCosets → R)`,
  `f ↦ (y ↦ (x ↦ f (x.out * localLevelSection σ ℓ K y)))`.
- `towerFunctionMap_eq h hH hf`: under (3.6), for an open normal `H` and a
  form `f` of level `K(n)`, `towerFunctionMap σ ℓ R f` is the published
  (3.10) `congruenceFunctionEquiv σ ℓ R H h hH f`, read as a function. So
  the published (3.10) at the different levels are restrictions of one
  map.
- `towerFunctionLinearMap σ ℓ R T h`: `towerFunctionMap` on `towerForms`,
  with values in `LocallyConstant K_ℓ (DoubleCosets → R)`. It is injective
  (`towerFunctionLinearMap_injective`, from injectivity at each level),
  surjective for compact `K` (`towerFunctionLinearMap_surjective`: a
  locally constant function on the compact `K_ℓ` is fixed by some
  `T.lower n` and so is the image of a form of level `K(n)`), and
  intertwines right translation by `k` with right translation by `k_ℓ`
  (`towerFunctionLinearMap_comm`).
- `towerFunctionEquiv σ ℓ R T h hK`, for `h : LocalLevelFree σ ℓ K` and
  `hK : IsCompact (K : Set σ.FiniteAdelicPoints)`: the equivalence of
  representations of `K` from `towerAction σ ℓ T R R` to
  `(functionModuleRep σ ℓ K R (DoubleCosets σ.finiteAdelicDiagonal K → R)).comp
  (localLevelMap σ ℓ K)`; `towerFunctionEquiv_apply`: `f` goes to
  `k_ℓ ↦ (x ↦ f (x.out * k))` for every `k ∈ K`.

### Forms with coefficients in `D(K_ℓ)`

- `functionModuleForms_apply_mul f g k y`: for
  `f ∈ functionModuleForms σ ℓ K R M`, `f (g k) y = f g (y k_ℓ⁻¹)`.
  `functionModuleForms_apply_eq f g hk`: `f g y = f (g k) 1` whenever
  `k_ℓ = y⁻¹`.
- `evalOne σ ℓ R M`: the `R`-linear map `f ↦ (g ↦ f g 1)` from the functions
  `GJ(𝔸^f) → LocallyConstant K_ℓ M` to the functions `GJ(𝔸^f) → M`.
- `exists_lower_functionModuleForms T hK f`: for compact `K` with finitely
  many double cosets (`[Finite (DoubleCosets σ.finiteAdelicDiagonal K)]`),
  one `T.lower n` fixes every value `f g` by right translation. Each
  `f x.out` is fixed by some `T.lower (N x)` (`exists_lower_apply_mul`),
  `n` is an upper bound of the finitely many `N x`, and
  `f (γ x.out k) = rightRegular (k_ℓ)⁻¹ (f x.out)` is fixed by the normal
  `T.lower n` as well.
- `evalOne_mem_congruenceForms f hn`: if one `T.lower n` fixes all values of
  `f`, then `evalOne σ ℓ R M f` is a form of level `K(n)`.
- `functionModuleFormsLift hF`, for a form `F` of level `K(n)`: the form
  `g ↦ (y ↦ F (g * (localLevelSection σ ℓ K y)⁻¹))` with coefficients in
  `D(K_ℓ)`. The function `y ↦ F (g k_y⁻¹)` is locally constant because it is
  constant on the open cosets `y · T.lower n`
  (`congruenceForms_apply_mul_eq` and normality), and the functional
  equation follows from `congruenceForms_apply_mul_eq`.
  `evalOne_functionModuleFormsLift`: its values at `1` are `F`.
- `functionFormsMap T hK`, `functionFormsMap_injective`,
  `functionFormsMap_surjective`: evaluation at `1` as a linear map from
  `functionModuleForms σ ℓ K R M` to `towerForms σ ℓ T R M`, bijective.
- `functionFormsEquiv σ ℓ R M T hK` (compact `K`, finitely many double
  cosets): the `R`-linear equivalence
  `𝒜_ℓ(GJ, D(K_ℓ), K) ≃ ⋃_n 𝒜_ℓ(GJ, M, K(n))`, `f ↦ (g ↦ f g 1)`
  (`functionFormsEquiv_apply_coe`), whose inverse sends `F` to
  `g ↦ (y ↦ F (g * k))` for any `k ∈ K` with `k_ℓ = y⁻¹`
  (`functionFormsEquiv_symm_apply`). Hypothesis (3.6) is not used.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case". Worker 61
read the rendered scanned page. Printed p.308 (one-based PDF page 10), as
quoted in the published `DefiniteFormsFunctions.md`: "More generally, we can
let `𝓛` be any continuous `K_ℓ`-module; then `𝒜_ℓ(GJ, 𝓛, K)`, defined by
analogy with (3.7), still makes sense. For example, we may take
`D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)` be the `𝒪/ℓ^m𝒪`-module of continuous
`𝒪/ℓ^m𝒪`-valued functions on `K_ℓ`, with `K_ℓ` acting by right translation.
Fix a lattice of normal congruence subgroups `K_ℓ(n) ⊂ K_ℓ`,
`n = 0, 1, 2, …`, with `⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` such that
`⋂_n K_ℓ(n) = {1}`. Let `K(n) = K_ℓ(n) × K^ℓ ⊂ GJ(𝔸^f)`." After (3.8) and
(3.9) "`GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^N GJ(ℚ) · K_∞ · K^ℓ γ_j K_ℓ`": "Then
hypothesis (3.6) implies that restriction to the double cosets in (3.9)
defines an isomorphism (3.10)
`𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ≅ [D_m(K_ℓ)^N]^{K_ℓ(n)}`. The right-hand side is just
the sum of `N` copies of the module `D_m(K_{ℓ,n})` of `𝒪/ℓ^m𝒪`-valued
functions on `K_{ℓ,n}`." Printed p.306 (one-based PDF page 8): "Let
`K ⊂ GJ(𝔸^f)` be an open compact subgroup". The readings of `K_ℓ`, `K(n)`,
(3.6), (3.7) and the tower are those of the published
`DefiniteFormsDoubleCoset.md` and `DefiniteFormsTower.md`; the readings of
`D_m(K_ℓ)`, `𝒜_ℓ(GJ, D_m(K_ℓ), K)` and (3.10) at a fixed level are those of
`DefiniteFormsFunctions.md`.

How the module relates to Harris (an explanation, not formalized):

- Continuity of `D_m(K_ℓ)`. Harris calls the coefficient modules
  "continuous `K_ℓ`-modules". For discrete coefficients this continuity is
  smoothness (open stabilizers), and `isSmooth_rightRegular` proves it for
  `D(K_ℓ)` when `K_ℓ` is compact (for instance `K` compact,
  `compactSpace_localLevel`).
- `D_m(K_ℓ)` and `D_m(K_{ℓ,n})`. Harris says that the right-hand side of
  (3.10) is a sum of copies of `D_m(K_{ℓ,n})`; letting `n` grow,
  `directLimitEquiv` shows that `D_m(K_ℓ)` is the direct limit of the
  `D_m(K_{ℓ,n})`. This statement is derived, not printed in Harris 1999.
  Finiteness of `K_ℓ ⧸ K_ℓ(n)` is neither assumed nor used.
- The union of the forms of level `K(n)`. `towerForms` is the union
  `⋃_n 𝒜_ℓ(GJ, M, K(n))` inside the functions `GJ(𝔸^f) → M`. Since the
  inclusions between the levels are injective, it is the direct limit of
  the `𝒜_ℓ(GJ, M, K(n))` along them; it is defined as a supremum of
  submodules, not as a `Module.DirectLimit`.
- (3.10) along the tower. `towerFunctionMap_eq` shows that the published
  (3.10) at the different levels `K(n)` are restrictions of one map, and
  `towerFunctionEquiv` is the resulting isomorphism for the union, onto all
  of `D(K_ℓ)` with values in the functions on the double cosets. It assumes
  (3.6), as Harris does, and compactness of `K`, which Harris assumes on
  p.306; finiteness of the double cosets is not needed. This union
  statement is derived, not printed in Harris 1999.
- `𝒜_ℓ(GJ, D_m(K_ℓ), K)`. Harris introduces these forms as an example and
  does not compute them. `functionFormsEquiv` identifies them with the union
  of the forms of level `K(n)`, by evaluation at `1` (a Frobenius
  reciprocity for `D(K_ℓ)`, which is induced from the trivial subgroup).
  It assumes compactness of `K` and finitely many double cosets
  `GJ(ℚ)\GJ(𝔸^f)/K` (Harris's (3.9) writes `N` double cosets; here this is
  an assumption, not proved), and does not use (3.6). This statement is
  derived, not printed in Harris 1999. The equivariance of
  `functionFormsEquiv` (for the action of `K_ℓ` on `D(K_ℓ)` by left
  translation, which commutes with right translation) is not formalized.
- Coefficients. `M` is an arbitrary `R`-module in the smoothness, direct
  limit, `towerForms` and `functionFormsEquiv` statements; (3.10) along the
  tower has `M = R`, as the published `congruenceFunctionEquiv`. Harris's
  case is `R = M = 𝒪/ℓ^m𝒪`.
- All declarations are ours, derived from Mathlib and the published
  modules named above; `localLevelSection`, `congruenceForms`,
  `towerFunctionMap`, `towerFunctionLinearMap`, `evalOne`,
  `functionModuleFormsLift` and `functionFormsMap` are internal
  constructions. Worker 13 (first executor of task 23471a9e) reported that
  this unit does not overlap their planned work, which stays on the
  geometric and cohomological side.

## Related declarations

- Library `Langlands.CompactAction.LocallyConstantModule.diagonalRepresentation_isSmooth`
  (`Representation/LocallyConstant/CompactAction`): smoothness of the
  diagonal action on locally constant functions on a compact `G`-space, in
  particular of the Library's left regular representation
  `Langlands.Induction.regularRepresentation`. `isSmooth_rightRegular` is
  the statement for right translation, obtained from the same published
  `functionStabilizer_isOpen` for the right action of `Gᵐᵒᵖ`.
- Library `Langlands.Induction.isFreeLimit_regular` (`RegularFreeLimit`):
  for a profinite group, the left regular representation is a direct limit
  of free modules over the open normal subgroups, as the predicate
  `IsFreeLimit`. `directLimitEquiv` is an explicit `Module.DirectLimit`
  along a fixed tower, for right translation, with no total disconnectedness
  assumption.
- Mathlib `Profinite.exists_locallyConstant` (`Topology/Category/Profinite/
  CofilteredLimit`): a locally constant function on a cofiltered limit of
  profinite spaces factors through a stage. `exists_lower_apply_mul` is the
  analogous statement for the quotients `G ⧸ T.lower n` of a compact group.
- Library `Langlands.Shimura.LevelColimit`, `RestrictedLevelColimit`
  (Worker 13): colimits over compact open levels. `towerForms` is a union
  over a fixed sequence `K(n)` of levels inside one function space.

## Scope

The module inherits the scope of the published `DefiniteFormsDoubleCoset`,
`DefiniteFormsFunctions` and `DefiniteFormsTower`: levels are not decomposed
as products `K^ℓ × K_ℓ`, `K_ℓ` is the image of `K` in the `ℓ`-adic points,
the tower is given data, and compactness of `K`, finiteness of the double
cosets and (3.6) are explicit hypotheses where used. It does not treat the
dependence on `m`, inverse limits, (3.8) for `D_m(K_ℓ)` coefficients, or
any cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
