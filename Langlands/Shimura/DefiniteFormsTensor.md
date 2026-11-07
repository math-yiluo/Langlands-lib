# Harris's isomorphism (3.8) for definite similitude groups

Author: Worker 61. Built on the published
`Langlands.Shimura.DefiniteFormsDoubleCoset` (Worker 61: `localLevel`,
`localLevelMap`, `ellModuleForms`, `LocalLevelFree`, `ellModuleFormsEquiv`,
`congruenceLevel` with its normality instance, `congruenceLevel_le`,
`congruenceLevel_subgroupOf`, `congruenceQuotientEquiv`,
`congruenceQuotientEquiv_mk`), `Langlands.Shimura.EquivariantFormsTensor`
(Worker 61: `tensorForms`, `tensorQuotientAction`,
`tensorQuotientAction_invariants`, `tensorQuotientInvariantsEquiv`),
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`, `levelAction`)
and `Langlands.Shimura.EquivariantFormsDoubleCoset` (Worker 61:
`DoubleCosets`), and on Worker 57's similitude groups
(`AlgebraInvolution.FiniteAdelicPoints`, `finiteAdelicDiagonal`,
`finiteLocalMap`). From Mathlib it uses quotient groups
(`QuotientGroup.mk'`), representations (`Representation.comp`,
`Representation.tprod`, `Representation.invariants`,
`Representation.trivial`, `Representation.IsTrivial`), tensor products and
linear equivalences (`LinearEquiv.ofEq`, `LinearEquiv.trans`).

The module specializes the published generic form of Harris's isomorphism
(3.8) to the levels and forms of the published `DefiniteFormsDoubleCoset`.
For a representation `ρ` of `K_ℓ ⧸ K_ℓ(n)` on a finite free module `𝓛`, it
identifies the `K_ℓ ⧸ K_ℓ(n)`-invariants of the tensor product of the forms
of level `K(n)` with trivial coefficients and `𝓛` with the forms of level
`K` with coefficients `𝓛`, Harris's `𝒜_ℓ(GJ, 𝓛, K)`; under Harris's
hypothesis (3.6), it identifies both with the `𝓛`-valued functions on the
double cosets.

## Conventions

As in the published `DefiniteFormsDoubleCoset.md`:
`σ : AlgebraInvolution ℚ A` is an involution of a finite-dimensional
`ℚ`-algebra `A`, `σ.FiniteAdelicPoints` is the group of finite adelic
points of its similitude group (Harris's `GJ(𝔸^f)`), with the rational
points embedded by `σ.finiteAdelicDiagonal`; `ℓ` is a finite place of `ℚ`;
`K` is a subgroup of `σ.FiniteAdelicPoints`; `localLevel σ ℓ K` (Harris's
`K_ℓ`) is the image of `K` under the `ℓ`-component map and
`localLevelMap σ ℓ K : K →* localLevel σ ℓ K` is `k ↦ k_ℓ`. `H` is a normal
subgroup of `localLevel σ ℓ K` (Harris's `K_ℓ(n)`, an explicit instance
hypothesis `[H.Normal]`), and `congruenceLevel σ ℓ K H` (Harris's `K(n)`)
is the subgroup of the `k ∈ K` with `k_ℓ ∈ H`. `forms ι K ρ` consists of
the functions `f` with `f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)`,
and `ellModuleForms σ ℓ K ρ'`, for a representation `ρ'` of
`localLevel σ ℓ K`, is `forms σ.finiteAdelicDiagonal K (ρ'.comp
(localLevelMap σ ℓ K))`, Harris's `𝒜_ℓ(GJ, 𝓛, K)`. `R` is a commutative
ring, `V` an `R`-module (Harris's `𝓛`) and `ρ` a representation of
`localLevel σ ℓ K ⧸ H` on `V`. Elements of subgroups are coerced silently,
`[k_ℓ]` is the class of `k_ℓ` in `localLevel σ ℓ K ⧸ H`, and `x.out` is
Mathlib's chosen representative of a class `x`.

## Definitions and results

- A local instance `isTrivial_trivial_comp`: the restriction of the trivial
  representation `Representation.trivial R G' R` along any group
  homomorphism is trivial. It is the same local instance as in the
  published `EquivariantFormsTensor` (local instances are not exported),
  needed to form the forms of level `K(n)` with trivial coefficients.
- `congruenceRep σ ℓ K H ρ` (an abbreviation): the representation
  `(ρ.comp (QuotientGroup.mk' H)).comp (localLevelMap σ ℓ K)` of `K` on
  `V`, `k ↦ ρ [k_ℓ]`. Its forms of level `K` are, by definition,
  `ellModuleForms σ ℓ K (ρ.comp (QuotientGroup.mk' H))`.
- An instance `Representation.IsTrivial` for `congruenceRep σ ℓ K H ρ`
  restricted to `K(n)` (along `Subgroup.inclusion (congruenceLevel_le σ ℓ K H)`):
  for `k ∈ K(n)`, `k_ℓ ∈ H` by `congruenceLevel_subgroupOf`, so
  `[k_ℓ] = 1` and `ρ [k_ℓ]` is the identity.
- `congruenceTensorSpace σ ℓ K H` (an abbreviation): the `R`-module
  `forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H) ((Representation.trivial R K R).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H))) ⊗[R] V`,
  the tensor product of the forms of level `K(n)` with trivial coefficients
  `R` (Harris's `𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n))` for `R = 𝒪/ℓ^m𝒪`) and `V`.
- `congruenceTensorAction σ ℓ K H ρ`: the representation of
  `localLevel σ ℓ K ⧸ H` on `congruenceTensorSpace σ ℓ K H`, the published
  `tensorQuotientAction` of `K ⧸ K(n)` for `congruenceRep σ ℓ K H ρ` and the
  level `K(n) ≤ K`, composed with the inverse of
  `congruenceQuotientEquiv σ ℓ K H : K ⧸ K(n) ≃* K_ℓ ⧸ H`.
  `congruenceTensorAction_mk`: `[k_ℓ]` acts as `k` acts in Mathlib's tensor
  product (`Representation.tprod`) of the published `levelAction` with
  trivial coefficients (right translation, `(k • f) g = f (g * k)`) and
  `congruenceRep`, so `[k_ℓ] • (f ⊗ v) = (g ↦ f (g * k)) ⊗ ρ [k_ℓ] v`.
- `congruenceTensorAction_invariants`: the invariants of
  `congruenceTensorAction` equal, as submodules, the invariants of
  `tensorQuotientAction`, since `congruenceQuotientEquiv` is a bijection.
- From here on `V` is finite free (`Module.Free R V`, `Module.Finite R V`).
  `congruenceTensorEquiv σ ℓ K H ρ`: an `R`-linear equivalence from the
  invariants of `congruenceTensorAction` to
  `ellModuleForms σ ℓ K (ρ.comp (QuotientGroup.mk' H))`:
  `congruenceTensorAction_invariants` followed by the published
  `tensorQuotientInvariantsEquiv` for `congruenceRep` and the level
  `K(n) ≤ K`. `congruenceTensorEquiv_apply_coe` (true by definition): the
  underlying function of the image of `x` is the published
  `tensorForms x`, which sends `f ⊗ v` to `g ↦ f g • v`.
- `congruenceTensorDoubleCosetEquiv σ ℓ H ρ h`: under (3.6)
  (`h : LocalLevelFree σ ℓ K`), an `R`-linear equivalence from the
  invariants of `congruenceTensorAction` to the functions
  `DoubleCosets σ.finiteAdelicDiagonal K → V`: `congruenceTensorEquiv`
  followed by the published `ellModuleFormsEquiv σ ℓ h` (restriction to the
  representatives of the double cosets).
  `congruenceTensorDoubleCosetEquiv_apply` (true by definition): its value
  at `x` and a double coset `y` is the value of `congruenceTensorEquiv x` at
  `y.out`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case", printed
p.308 (one-based PDF page 10). Worker 61 read the rendered scanned page:
"More generally, we can let `𝓛` be any continuous `K_ℓ`-module; then
`𝒜_ℓ(GJ, 𝓛, K)`, defined by analogy with (3.7), still makes sense. [...]
Fix a lattice of normal congruence subgroups `K_ℓ(n) ⊂ K_ℓ`,
`n = 0, 1, 2, ...`, with `⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` such that
`⋂_n K_ℓ(n) = {1}`. Let `K(n) = K_ℓ(n) × K^ℓ ⊂ GJ(𝔸^f)`. Let `𝓛` be a free
`𝒪/ℓ^m𝒪`-module of finite order with a continuous action of `K_ℓ`, which we
suppose to factor through the quotient group `K_{ℓ,n} = K_ℓ/K_ℓ(n)`. Then
there is a canonical isomorphism (3.8)
`𝒜_ℓ(GJ, 𝓛, K) ⥲ [𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛]^{K_{ℓ,n}}`. Indeed, write
(3.9) `GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^N GJ(ℚ) · K_∞ · K^ℓ γ_j K_ℓ`. Then
hypothesis (3.6) implies that restriction to the double cosets in (3.9)
defines an isomorphism (3.10)
`𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⥲ [D_m(K_ℓ)^N]^{K_ℓ(n)}`. The right-hand side is
just the sum of `N` copies of the module `D_m(K_{ℓ,n})` of
`𝒪/ℓ^m𝒪`-valued functions on `K_{ℓ,n}`. Thus (3.8) is a consequence of the
tautological identification (3.11)
`{f : K_{ℓ,n} → 𝓛 | f(k) = ρ(k)^{-1} f(1)} ⥲ [D_m(K_{ℓ,n}) ⊗ 𝓛]^{K_{ℓ,n}}`."
The levels, (3.6), (3.7) and (3.10) are quoted and interpreted in the
published `DefiniteFormsDoubleCoset.md`, and the generic (3.8) in the
published `EquivariantFormsTensor.md`.

How the module relates to (3.8) (an explanation, not formalized):

- Coefficients. Harris's action of `K_ℓ` on `𝓛` factoring through
  `K_{ℓ,n}` is the representation `ρ` of `localLevel σ ℓ K ⧸ H`, inflated
  to `K_ℓ` by `ρ.comp (QuotientGroup.mk' H)`; `𝒜_ℓ(GJ, 𝓛, K)` is then
  `ellModuleForms σ ℓ K (ρ.comp (QuotientGroup.mk' H))`, as in the
  published reading of (3.7). Harris's `𝓛` is "a free `𝒪/ℓ^m𝒪`-module of
  finite order", a finite free module over the finite ring `𝒪/ℓ^m𝒪`; we
  assume `Module.Free R V` and `Module.Finite R V` over an arbitrary
  commutative ring `R`. No continuity is imposed.
- The group `K_{ℓ,n}`. Harris's `K_{ℓ,n} = K_ℓ/K_ℓ(n)` is
  `localLevel σ ℓ K ⧸ H`; the published generic (3.8) uses `K ⧸ K(n)`
  instead, and `congruenceQuotientEquiv` transports its action to
  `K_ℓ ⧸ H`. As Harris does not write out the action of `K_{ℓ,n}` on the
  tensor product, we take, as in the published generic module, right
  translation on the forms and `ρ` on `𝓛` (`congruenceTensorAction_mk`).
- (3.8). `congruenceTensorEquiv` is (3.8) in the opposite direction; it is
  an equivalence, so the direction is immaterial. Harris does not write out
  the "canonical isomorphism"; the inverse of ours sends a form `F` to
  `∑ i, (g ↦ b.coord i (F g)) ⊗ b i` for Mathlib's chosen basis `b` of `V`
  (the published `tensorFormsEquiv`).
- Proof route. Harris derives (3.8) from (3.9), (3.6), (3.10) and the
  "tautological identification" (3.11). The Lean proof uses none of them: it
  is the published generic `tensorQuotientInvariantsEquiv`, whose proof
  commutes tensoring with the finite free `V` with forming forms at level
  `K(n)` (where `ρ` is trivial) and takes `K`-invariants. (3.11) itself is
  not formalized.
- Double cosets. Under (3.6), `congruenceTensorDoubleCosetEquiv` identifies
  the right-hand side of (3.8) with the `𝓛`-valued functions on the double
  cosets `GJ(ℚ) \ GJ(𝔸^f) / K` of (3.9), and the published
  `ellModuleFormsEquiv` does the same for the left-hand side. In Harris's
  argument both sides become `N` copies of
  `{f : K_{ℓ,n} → 𝓛 | f(k) = ρ(k)^{-1} f(1)}`, that is `𝓛^N`; this
  composite is our derived statement, not printed in Harris 1999. It is
  stated with the published `DoubleCosets` and Mathlib's representatives;
  finiteness of the double coset space (Harris's `N`) is not proved.
- The local triviality instance, `congruenceRep`, `congruenceTensorSpace`,
  the triviality instance of `congruenceRep` on `K(n)` and
  `congruenceTensorAction_invariants` are internal constructions not
  printed in Harris 1999. All definitions, statements and proofs are ours,
  derived from Mathlib and the published modules named above.

## Scope

The module inherits the scope of the published `DefiniteFormsDoubleCoset`:
levels are not decomposed as products `K^ℓ × K_ℓ`, `K_ℓ` is the image of
`K` in the `ℓ`-adic points, a single normal subgroup `H` stands for
`K_ℓ(n)`, and there are no openness, compactness, continuity or finiteness
conditions. It does not formalize (3.11) or the functions `D_m(K_{ℓ,n})`,
does not treat lattices or base change, does not pass to limits in `m` or
`n`, and constructs no cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
