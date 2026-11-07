# Harris's function modules `D_m(K_ℓ)` and the identifications (3.10), (3.11)

Author: Worker 61. Built on the published
`Langlands.Shimura.DefiniteFormsDoubleCoset` (Worker 61: `localLevel`,
`localLevelMap`, `ellModuleForms`, `LocalLevelFree`, `congruenceLevel`,
`congruenceLevel_le`, `congruenceLevelEquiv`,
`congruenceLevelEquiv_apply_mk`), `Langlands.Shimura.EquivariantForms`
(Worker 61: `forms`, `levelAction`),
`Langlands.Shimura.EquivariantFormsDoubleCoset` (Worker 61:
`DoubleCosets`), `Langlands.Shimura.EquivariantFormsTensor` (Worker 61:
`EquivariantForms.invariantsEquivOfEquiv`),
`Langlands.Cohomology.DivisibleSystem.RegularFreeLimit` (Worker 61:
`Langlands.Induction.regularRepresentation`),
`Langlands.Representation.Induction.PermutationDual` (Worker 61:
`Langlands.Induction.functionRepresentation`),
`Langlands.Representation.Induction.PermutationInvariants` (Worker 61:
`Langlands.Induction.invariantsEquivOfEquiv`) and
`Langlands.Representation.EquivalencePullback` (`equivComp`), and on Worker
57's similitude groups (`AlgebraInvolution.FiniteAdelicPoints`,
`finiteAdelicDiagonal`, the topology on `σ.Points`). From Mathlib it uses
locally constant functions (`LocallyConstant`, `LocallyConstant.comapₗ`,
`LocallyConstant.flip`, `LocallyConstant.unflip`,
`IsLocallyConstant.of_discrete`), quotient groups and their topology
(`QuotientGroup.mk'`, `QuotientGroup.discreteTopology`), representations
(`Representation.comp`, `Representation.invariants`,
`Representation.toInvariants`, `Representation.quotientToInvariants`,
`Representation.tprod`, `Representation.Equiv`) and tensor products with
function spaces (`TensorProduct.piScalarRight`).

The module formalizes the passage of Harris 1999, p.308, after (3.7): the
module `D_m(K_ℓ)` of continuous functions on `K_ℓ` with right translation,
the forms `𝒜_ℓ(GJ, D_m(K_ℓ), K)`, the isomorphism (3.10) as restriction to
double cosets with values in `[D_m(K_ℓ)^N]^{K_ℓ(n)}`, the observation that
this is a sum of `N` copies of `D_m(K_{ℓ,n})`, and the "tautological
identification" (3.11). Harris's coefficient ring `𝒪/ℓ^m𝒪` becomes an
arbitrary commutative ring `R`, and his continuous functions with discrete
values become locally constant functions.

## Conventions

As in the published `DefiniteFormsDoubleCoset.md`:
`σ : AlgebraInvolution ℚ A` is an involution of a finite-dimensional
`ℚ`-algebra `A`, and `σ.FiniteAdelicPoints` is the group of finite adelic
points of its similitude group (Harris's `GJ(𝔸^f)`), with the rational
points embedded by `σ.finiteAdelicDiagonal`. `ℓ` is a finite place of `ℚ`,
`K` is a subgroup of `σ.FiniteAdelicPoints`, `localLevel σ ℓ K` (Harris's
`K_ℓ`) is the image of `K` under the `ℓ`-component map, a subgroup of the
`ℓ`-adic points `σ.Points ℚ_ℓ` with the subspace topology of Worker 57's
topology on `σ.Points ℚ_ℓ`, and `localLevelMap σ ℓ K : K →* localLevel σ ℓ K`
is `k ↦ k_ℓ`. `DoubleCosets σ.finiteAdelicDiagonal K` is
`GJ(ℚ) \ GJ(𝔸^f) / K` and `x.out` is Mathlib's chosen representative of a
class `x`. For a representation `ρ'` of `K_ℓ`, `ellModuleForms σ ℓ K ρ'` is
Harris's (3.7), the functions `f : GJ(𝔸^f) → V` with `f (γ g) = f g` for
rational `γ` and `f (g k) = ρ'(k_ℓ)⁻¹ f g` for `k ∈ K`. For a subgroup `H`
of `K_ℓ` (Harris's `K_ℓ(n)`), `congruenceLevel σ ℓ K H` (Harris's `K(n)`)
is the set of `k ∈ K` with `k_ℓ ∈ H`, `levelAction` is the action of `K` by
right translation on the forms of level `K(n)` with trivial coefficients
`R`, and `LocalLevelFree σ ℓ K` is Harris's hypothesis (3.6). For a
representation `ρ` of `G` and a normal subgroup `H`, Mathlib's
`ρ.toInvariants H` is the representation of `G` on the `H`-invariants and
`ρ.quotientToInvariants H` the same as a representation of `G ⧸ H`.
Elements of subgroups and submodules are coerced silently below.

## Function modules

Namespace `Langlands.Shimura.FunctionModule`. `R` is a commutative ring,
`M` and `V` are `R`-modules.

For a group `Q` and a representation `ρ` of `Q` on `V`:

- `functionRightRep ρ`: the representation of `Q` on all functions
  `Q → V` with `(g • F)(x) = ρ g (F (x * g))` (`functionRightRep_apply`).
- `functionRightRegular R Q M` (an abbreviation): `functionRightRep` of the
  trivial representation on `M`, that is right translation
  `(g • φ)(x) = φ (x * g)` on the functions `Q → M`
  (`functionRightRegular_apply`).
- `functionInvEquiv R M H`, for a normal subgroup `H` of a group `G`: an
  equivalence of representations of `G` from the Library's
  `functionRepresentation (Representation.trivial R G M) (G ⧸ H)` (functions
  on `G ⧸ H` with `(g • φ)(q) = φ (g⁻¹ q)`) to
  `functionRightRegular R (G ⧸ H) M` composed with `G → G ⧸ H`, given by
  `φ ↦ (q ↦ φ q⁻¹)` (`functionInvEquiv_apply`).

For a topological group `G`:

- `rightRegular R G M`: Harris's `D_m(K_ℓ)` for general `G` and values in
  `M`, the representation of `G` on the locally constant functions
  `G → M` by right translation, `(g • f)(x) = f (x * g)`
  (`rightRegular_apply`).
- `rightRegularEquivRegular`: the equivalence of representations from
  `rightRegular R G M` to the Library's `regularRepresentation R M` (left
  translation, `(g • f)(x) = f (g⁻¹ * x)`) given by `f ↦ (x ↦ f x⁻¹)`
  (`rightRegularEquivRegular_apply`).
- For a subgroup `H` of `G`: `apply_mul_of_mem_invariants`: an `H`-invariant
  `f` satisfies `f (x * h) = f x` for `h ∈ H`; `invariantsDescend H f` is
  the function `[y] ↦ f y` on `G ⧸ H` (`invariantsDescend_mk`).
  For `H` open (`hH : IsOpen (H : Set G)`), `invariantsPullback hH φ` is the
  `H`-invariant locally constant function `y ↦ φ [y]` for any function `φ`
  on `G ⧸ H` (`invariantsPullback_apply`); it is locally constant since
  `G ⧸ H` is discrete.
- `invariantsEquiv hH`, for `H` open and normal: the equivalence of
  representations of `G` from `(rightRegular R G M).toInvariants H` to
  `functionRightRegular R (G ⧸ H) M` composed with `G → G ⧸ H`, given by
  `invariantsDescend` with inverse `invariantsPullback`
  (`invariantsEquiv_apply_mk`, `invariantsEquiv_symm_apply`).
  `quotientInvariantsEquiv hH` is the same linear equivalence as an
  equivalence of representations of `G ⧸ H`, from
  `(rightRegular R G M).quotientToInvariants H` to
  `functionRightRegular R (G ⧸ H) M`. Thus the `H`-invariants of `D(G)` are
  the module of functions on `G ⧸ H` with right translation.
- `rightRegularPi R G M X`, for a type `X`: the representation of `G` on the
  families `X → LocallyConstant G M`, acting by `rightRegular` in each
  coordinate (`rightRegularPi_apply`): `X` copies of `rightRegular R G M`.
  `rightRegularPiEquiv R G M X`, for `X` finite: the equivalence of
  representations from `rightRegular R G (X → M)` to `rightRegularPi R G M X`
  given by Mathlib's `LocallyConstant.flip`, `f ↦ (x ↦ (y ↦ f y x))`
  (`rightRegularPiEquiv_apply`), with inverse `LocallyConstant.unflip`.

For a group `Q` and a representation `ρ` of `Q` on `V`:

- `inducedFunctions ρ`: the submodule of functions `f : Q → V` with
  `f k = ρ k⁻¹ (f 1)` for all `k` (`mem_inducedFunctions`), the left-hand
  side of Harris's (3.11).
- `invariants_functionRightRep`: the `Q`-invariants of `functionRightRep ρ`
  are `inducedFunctions ρ`. Proof: evaluating `ρ g (F (x * g)) = F x` at
  `x = 1` gives `F g = ρ g⁻¹ (F 1)`; conversely this formula gives the
  invariance.
- For `Q` finite: `tensorFunctionEquiv ρ`: the equivalence of
  representations from `(functionRightRegular R Q R).tprod ρ` (Mathlib's
  tensor product of representations, on `(Q → R) ⊗[R] V`) to
  `functionRightRep ρ`, the composite of the swap of factors and Mathlib's
  `TensorProduct.piScalarRight`; it sends `φ ⊗ v` to `x ↦ φ x • v`
  (`tensorFunctionEquiv_tmul`).
- `tautologicalEquiv ρ`, for `Q` finite: the `R`-linear equivalence from
  `inducedFunctions ρ` to the `Q`-invariants of
  `(functionRightRegular R Q R).tprod ρ`, composed of
  `invariants_functionRightRep` and the restriction of
  `(tensorFunctionEquiv ρ).symm` to invariants (published
  `EquivariantForms.invariantsEquivOfEquiv`).
  `tautologicalEquiv_symm_apply`: the inverse sends an invariant tensor `t`
  to `tensorFunctionEquiv ρ t`. This is Harris's (3.11) with `Q = K_{ℓ,n}`,
  `V = 𝓛` and `Q → R` the module `D_m(K_{ℓ,n})` of functions on the finite
  group `K_{ℓ,n}`.

## Harris's setting

Namespace `Langlands.Shimura.DefiniteForms`, with `σ`, `ℓ`, `K` as in the
conventions, a commutative ring `R` and an `R`-module `M`.

- `functionModuleRep σ ℓ K R M` (an abbreviation): `rightRegular` for the
  topological group `K_ℓ = localLevel σ ℓ K`, Harris's `D_m(K_ℓ)` with
  values in `M`.
- `functionModuleForms σ ℓ K R M` (an abbreviation): `ellModuleForms` for
  `functionModuleRep σ ℓ K R M`, Harris's `𝒜_ℓ(GJ, D_m(K_ℓ), K)` "defined
  by analogy with (3.7)".
- `congruenceFunctionEquiv σ ℓ R H h hH`, for a normal subgroup `H` of
  `K_ℓ`, `h : LocalLevelFree σ ℓ K` (Harris's (3.6)) and `H` open in `K_ℓ`:
  an equivalence of representations of `K` from `levelAction` on the forms
  of level `K(n)` with trivial coefficients `R` to the `H`-invariants of
  `functionModuleRep σ ℓ K R (DoubleCosets σ.finiteAdelicDiagonal K → R)`
  (locally constant functions on `K_ℓ` with values in the functions on the
  double cosets), with `K` acting through `k ↦ k_ℓ`. It is the published
  `congruenceLevelEquiv` (Harris's (3.10) with values in the functions on
  `K_ℓ ⧸ H`, left translation), followed by `functionInvEquiv` and the
  inverse of `invariantsEquiv`, each composed with `localLevelMap` by
  `equivComp`. `congruenceFunctionEquiv_apply`: a form `f` goes to the
  function with value `f (x.out * k)` at `k_ℓ` and the double coset `x`.
- `congruencePiEquiv σ ℓ R H h hH`, under the same hypotheses and finitely
  many double cosets (`[Finite (DoubleCosets σ.finiteAdelicDiagonal K)]`):
  the equivalence of representations of `K` from the same `levelAction` to
  the `H`-invariants of `rightRegularPi R K_ℓ R (DoubleCosets …)`, with `K`
  acting through `k ↦ k_ℓ`: `congruenceFunctionEquiv` followed by the
  restriction of `rightRegularPiEquiv` to `H`-invariants (the Library's
  `Langlands.Induction.invariantsEquivOfEquiv`, an equivalence of
  representations of `K_ℓ ⧸ H`, composed with `K → K_ℓ → K_ℓ ⧸ H`).
  `congruencePiEquiv_apply`: a form `f` goes to the family whose
  coordinate at the double coset `x` is the function with value
  `f (x.out * k)` at `k_ℓ`. This is Harris's (3.10)
  `𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ≅ [D_m(K_ℓ)^N]^{K_ℓ(n)}`, with `N` the number of
  double cosets.

By `quotientInvariantsEquiv` and `rightRegularPi`, the right-hand side of
(3.10) is `N` copies of the functions on `K_ℓ ⧸ H = K_{ℓ,n}` with right
translation, Harris's "sum of `N` copies of the module `D_m(K_{ℓ,n})`";
this is the content of the stated equivalences, not a separate
declaration.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case". Worker 61
read the rendered scanned page. Printed p.308 (one-based PDF page 10),
after (3.7) and the lattice comparison: "More generally, we can let `𝓛` be
any continuous `K_ℓ`-module; then `𝒜_ℓ(GJ, 𝓛, K)`, defined by analogy with
(3.7), still makes sense. For example, we may take
`D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)` be the `𝒪/ℓ^m𝒪`-module of continuous
`𝒪/ℓ^m𝒪`-valued functions on `K_ℓ`, with `K_ℓ` acting by right translation.
Fix a lattice of normal congruence subgroups `K_ℓ(n) ⊂ K_ℓ`,
`n = 0, 1, 2, …`, with `⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` such that
`⋂_n K_ℓ(n) = {1}`. Let `K(n) = K_ℓ(n) × K^ℓ ⊂ GJ(𝔸^f)`. Let `𝓛` be a free
`𝒪/ℓ^m𝒪`-module of finite order with a continuous action of `K_ℓ`, which we
suppose to factor through the quotient group
`K_{ℓ,n} =def K_ℓ/K_ℓ(n)`." Then (3.8), (3.9)
"`GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^N GJ(ℚ) · K_∞ · K^ℓ γ_j K_ℓ`", and "Then
hypothesis (3.6) implies that restriction to the double cosets in (3.9)
defines an isomorphism (3.10)
`𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ≅ [D_m(K_ℓ)^N]^{K_ℓ(n)}`. The right-hand side is just
the sum of `N` copies of the module `D_m(K_{ℓ,n})` of `𝒪/ℓ^m𝒪`-valued
functions on `K_{ℓ,n}`. Thus (3.8) is a consequence of the tautological
identification (3.11)
`{f : K_{ℓ,n} → 𝓛 | f(k) = ρ(k)^{-1} f(1)} ≅ [D_m(K_{ℓ,n}) ⊗ 𝓛]^{K_{ℓ,n}}`."
The readings of (3.6), (3.7), `K_ℓ`, `K(n)` and the published (3.10) are
those of `DefiniteFormsDoubleCoset.md`.

How the module relates to Harris (an explanation, not formalized):

- Coefficients. Harris's `𝒪/ℓ^m𝒪` becomes an arbitrary commutative ring
  `R`, and the values of the functions in `D_m(K_ℓ)` may lie in any
  `R`-module `M`; Harris's case is `M = R = 𝒪/ℓ^m𝒪`.
- Continuity. `𝒪/ℓ^m𝒪` is finite and Harris's functions are continuous for
  its discrete topology; a function into a discrete space is continuous
  exactly when it is locally constant. We use Mathlib's `LocallyConstant`,
  so no topology on `R` or `M` is needed.
- Right translation. Harris's "`K_ℓ` acting by right translation" is
  `(g • f)(x) = f (x g)` (`rightRegular`). The Library's
  `regularRepresentation` uses left translation `f (g⁻¹ x)`;
  `rightRegularEquivRegular` relates the two.
- `K_ℓ(n)`. Harris's `K_ℓ(n)` is an open normal congruence subgroup; a
  single one is fixed and becomes an open normal subgroup `H` of `K_ℓ`.
  Openness is used for `invariantsPullback`; normality is used for the
  action of `K_ℓ ⧸ H`. The tower `n ↦ K_ℓ(n)` and the condition
  `⋂_n K_ℓ(n) = {1}` are not used.
- (3.10). Harris's isomorphism is "restriction to the double cosets in
  (3.9)". The published `congruenceLevelEquiv` already records restriction
  to the representatives `x.out` with values in the functions on
  `K_ℓ ⧸ K_ℓ(n)`; `congruenceFunctionEquiv` rewrites the target as the
  `K_ℓ(n)`-invariants of `D(K_ℓ)` with values in the functions on the
  double cosets, and `congruencePiEquiv` as `[D(K_ℓ)^N]^{K_ℓ(n)}`: Harris's
  `D_m(K_ℓ)^N` is read as `N` copies indexed by the double cosets, which
  requires finitely many double cosets (Harris's `N`; assumed, not proved).
  The form `f` is sent to `k_ℓ ↦ f (x.out * k)` for the double coset `x`,
  that is, to the restriction of `f` to `x.out · K`, read through `k_ℓ`
  (it depends only on `k_ℓ`, since every `k ∈ K` with `k_ℓ = 1` lies in
  `K(n)`; in Harris's product setting this is `K^ℓ ⊂ K(n)`); (3.6) is what
  makes this restriction bijective.
- (3.11). `K_{ℓ,n}` becomes an arbitrary finite group `Q`, `𝓛` an arbitrary
  representation `ρ` of `Q` over `R` (not necessarily free or finite), and
  `D_m(K_{ℓ,n})` the functions `Q → R` with right translation. The
  identification is `R`-linear; Harris's `⊗` is over `𝒪/ℓ^m𝒪`, our `⊗[R]`.
  Harris does not write out the map; we read "tautological" as the
  identification whose inverse is `φ ⊗ v ↦ (x ↦ φ x • v)`
  (`tensorFunctionEquiv_tmul`). By Mathlib's construction of the inverse of
  `piScalarRight`, the forward map sends `f` to `Σ_x δ_x ⊗ f x`, with `δ_x`
  the indicator function of `x`; this formula is not stated as a lemma.
- Not formalized: the deduction of (3.8) from (3.10) and (3.11), (3.8) for
  `D_m(K_ℓ)` coefficients (the published `DefiniteFormsTensor` treats
  (3.8)), the continuity of the `K_ℓ`-action on `𝓛`, and the dependence on
  `m`.
- All declarations are ours; `functionRightRep`, `functionInvEquiv`,
  `rightRegularEquivRegular`, `invariantsDescend`, `invariantsPullback`,
  `invariantsEquiv`, `quotientInvariantsEquiv`, `rightRegularPi`,
  `rightRegularPiEquiv`, `invariants_functionRightRep` and
  `tensorFunctionEquiv` are internal constructions not printed in Harris
  1999, derived from Mathlib and the published modules named above.

## Related declarations

- Library `Langlands.Induction.regularRepresentation` (`RegularFreeLimit`):
  the same locally constant functions with left translation; equivalent to
  `rightRegular` by `rightRegularEquivRegular`. Its `regularInvariantsEquiv`
  identifies, for compact `G`, the invariants of an open normal subgroup
  with the permutation representation `(G ⧸ H) →₀ M`; `invariantsEquiv`
  here needs no compactness and has the functions `G ⧸ H → M` as target.
- Library `Langlands.Induction.functionRepresentation` (`PermutationDual`):
  functions on a `G`-set with `G` acting on the argument by `g⁻¹`;
  `functionInvEquiv` relates it to right translation on `G ⧸ H`.
- Library `Langlands.CompactAction.LocallyConstantModule.diagonalRepresentation`
  (`Representation/LocallyConstant/CompactAction`): locally constant
  functions on a `G`-space `X` with `(g • f)(x) = ρ g (f (g⁻¹ • x))`; for
  `X = G` with left multiplication and trivial `ρ` this is left translation,
  as in `regularRepresentation`, not `rightRegular`.
- Mathlib `TannakaDuality.FiniteGroup.rightRegular`: right translation on
  the functions `G → k`, with scalar values; `functionRightRegular R Q M`
  allows values in an `R`-module `M`.
- Mathlib `ContRepresentation.coind`: right translation on continuous
  functions `C(H, V)` satisfying a coinduction condition, for topological
  `R` and `V`. `rightRegular` uses locally constant functions and needs no
  topology on the coefficients.

## Scope

The module inherits the scope of the published `DefiniteFormsDoubleCoset`:
levels are not decomposed as products `K^ℓ × K_ℓ`, `K_ℓ` is the image of
`K` in the `ℓ`-adic points, and there are no compactness conditions. It
fixes one open normal subgroup `H` of `K_ℓ` rather than a tower, does not
prove the finiteness of the double coset space, does not deduce (3.8) from
(3.10) and (3.11), does not treat limits in `m` or `n`, and constructs no
cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
