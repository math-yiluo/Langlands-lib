# Base change of Harris's forms `𝒜_f(GJ, ρ, K)`

Author: Worker 61. Built on the published `Langlands.Shimura.DefiniteForms`
(Worker 61: `rationalRep`, `rationalRep_apply`, `finiteForms`,
`mem_finiteForms`), `Langlands.Shimura.EquivariantFormsTwist` (Worker 61:
`twistedForms`), `Langlands.Shimura.EquivariantFormsDoubleCoset` (Worker 61:
`DoubleCosets`, `exists_eq_mul_out_mul`) and
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (Worker 61:
`Langlands.Cohomology.baseChangeRepresentation`,
`baseChangeRepresentation_apply_tmul`), and on Worker 57's published
`Langlands.Shimura.Unitary.Adelic` (`similitudes`, `FiniteAdelicPoints`,
`finiteAdelicDiagonal`, `diagonalPoints`) and
`Langlands.Shimura.Coefficients.Algebraic` (`AlgebraicRepresentation`,
`rationalAction`). From Mathlib it uses tensor products and base change
(`TensorProduct.lid`, `LinearMap.liftBaseChange`, `LinearEquiv.baseChange`,
`TensorProduct.inductionOn`), free modules and bases (`Module.Free`,
`Module.Free.chooseBasis`, `Module.Basis`,
`TensorProduct.equivFinsuppOfBasisLeft`) and finitely supported functions
(`Finsupp.onFinset`).

The module constructs Harris's base change isomorphism (3.4) for the space
(3.2) `𝒜_f(GJ, ρ, K)(L')`, assuming finitely many double cosets
`GJ(ℚ)\GJ(𝔸^f)/K`. It first proves a generic statement for functions on a
group that are twisted on the left by a representation of a second group
and invariant on the right under a subgroup.

## Conventions

As in the published `DefiniteForms.md`: `σ : AlgebraInvolution ℚ A` is an
involution of a `ℚ`-algebra `A`, `σ.similitudes` is Harris's `GJ(ℚ)`,
`σ.FiniteAdelicPoints` is `GJ(𝔸^f)` and `σ.finiteAdelicDiagonal` the
diagonal embedding. `L` is a field with `[Algebra ℚ L]`, `W` an `L`-vector
space and `ρ : (σ.baseChange L).AlgebraicRepresentation W` an algebraic
representation; `ρ.rationalAction` is its action of the `L`-points by
`L`-linear automorphisms of `W`. For an `L`-algebra `S`, `W(S) = S ⊗[L] W`,
`rationalRep σ ρ S` is the action `γ ↦ ρ(γ)` of `σ.similitudes` on `W(S)`
and `finiteForms σ ρ S K` is Harris's `𝒜_f(GJ, ρ, K)(S)` (3.2): the
functions `f : GJ(𝔸^f) → W(S)` with `f (γ g) = ρ(γ) (f g)` for rational `γ`
and `f (g k) = f g` for `k ∈ K`. For a commutative ring `R`, an `R`-algebra
`S` and a representation `τ` of a group `Γ` on an `R`-module `V`, the
published `baseChangeRepresentation S τ` is the representation of `Γ` on
`S ⊗[R] V` by `1 ⊗ τ γ`. `DoubleCosets ι K` is `ι Γ \ G / K` and `x.out` is
Mathlib's chosen representative of a class `x`.

## Generic forms twisted on the left

Namespace `Langlands.Shimura.EquivariantForms`. `Γ` and `G` are groups,
`ι : Γ →* G`, `K` is a subgroup of `G`, `R` a commutative ring and `τ` a
representation of `Γ` on an `R`-module `V`.

- `rationalForms ι K τ`: the `R`-submodule of functions `f : G → V` with
  `f (ι γ * g) = τ γ (f g)` for all `γ : Γ` and `f (g * k) = f g` for all
  `k ∈ K` (`mem_rationalForms`).
- `twistedForms_eq_rationalForms`: for a representation `ρ` of `G`, the
  published `twistedForms ι K ρ` is `rationalForms ι K (ρ.comp ι)`. The new
  submodule is needed because Harris's `ρ(γ)` on `W(S)` is an action of the
  rational points only, not of `GJ(𝔸^f)`.

For an `R`-algebra `S`:

- `rationalFormsScalar ι K τ S`: the `R`-linear map
  `f ↦ (g ↦ 1 ⊗ f g)` from `rationalForms ι K τ` to
  `rationalForms ι K (baseChangeRepresentation S τ)`.
- `rationalFormsBaseChange ι K τ S`: its `S`-linear extension
  `S ⊗[R] rationalForms ι K τ → rationalForms ι K
  (baseChangeRepresentation S τ)` (Mathlib's `LinearMap.liftBaseChange`),
  `s ⊗ f ↦ (g ↦ s ⊗ f g)` (`rationalFormsBaseChange_tmul`).

For a basis `b : Module.Basis I R S` (`[DecidableEq I]`) and Mathlib's
coordinate equivalence `TensorProduct.equivFinsuppOfBasisLeft b :
S ⊗[R] N ≃ I →₀ N` (the unique expression `Σ_i b i ⊗ n_i`):

- `equivFinsuppOfBasisLeft_rationalFormsBaseChange`: the `i`-th coordinate
  of the value at `g` of `rationalFormsBaseChange x` is the value at `g` of
  the `i`-th coordinate of `x`.
- `equivFinsuppOfBasisLeft_baseChange`: the `i`-th coordinate of
  `(1 ⊗ τ γ) y` is `τ γ` of the `i`-th coordinate of `y`.
- `coordinateForm ι K b F i`: for a form `F` for
  `baseChangeRepresentation S τ`, the function `g ↦ i`-th coordinate of
  `F g`, a form for `τ` (`coordinateForm_apply`).
- `finite_support_coordinateForm` (`[Finite (DoubleCosets ι K)]`): only
  finitely many `coordinateForm ι K b F i` are nonzero. Every `g` is
  `ι γ * x.out * k` for its double coset `x` (published
  `exists_eq_mul_out_mul`), so `F g = (1 ⊗ τ γ) (F x.out)`, whose
  coordinates vanish outside the support of the coordinates of `F x.out`;
  the finitely many `x` give a finite set.

For `[Module.Free R S]` (with the basis `Module.Free.chooseBasis R S`):

- `rationalFormsBaseChange_injective`: if `rationalFormsBaseChange x = 0`,
  every coordinate of `x` vanishes at every `g`, so `x = 0`.
- `rationalFormsBaseChange_surjective` (`[Finite (DoubleCosets ι K)]`): a
  form `F` is the image of the element of `S ⊗[R] rationalForms ι K τ`
  whose coordinates are the finitely many nonzero `coordinateForm ι K b F i`.
- `rationalFormsBaseChangeEquiv ι K τ` (`[Module.Free R S]`,
  `[Finite (DoubleCosets ι K)]`): the `S`-linear equivalence
  `S ⊗[R] rationalForms ι K τ ≃ rationalForms ι K
  (baseChangeRepresentation S τ)`, `s ⊗ f ↦ (g ↦ s ⊗ f g)`
  (`rationalFormsBaseChangeEquiv_tmul`).
- `lid_baseChangeRepresentation`, `rationalFormsLidEquiv ι K τ`: for the base
  change to `R` itself, `TensorProduct.lid : R ⊗[R] V ≃ V` intertwines
  `baseChangeRepresentation R τ` with `τ` and identifies
  `rationalForms ι K (baseChangeRepresentation R τ)` with
  `rationalForms ι K τ` (`rationalFormsLidEquiv_apply_coe`); no finiteness
  is needed.

## Harris's (3.4)

Namespace `Langlands.Shimura.DefiniteForms`, with `σ`, `L`, `W`, `ρ` as in
the conventions and `K` a subgroup of `σ.FiniteAdelicPoints`.

- `rationalBaseRep σ ρ : Representation L σ.similitudes W`: the action
  `γ ↦ ρ(γ)` on `W` itself, `ρ.rationalAction` composed with
  `σ.diagonalPoints L` and viewed as linear maps.
- `rationalRep_eq_baseChangeRepresentation σ ρ S`: the published
  `rationalRep σ ρ S` is `baseChangeRepresentation S (rationalBaseRep σ ρ)`
  (by definition).
- `finiteForms_eq_rationalForms σ ρ K S`: `finiteForms σ ρ S K` is
  `rationalForms σ.finiteAdelicDiagonal K
  (baseChangeRepresentation S (rationalBaseRep σ ρ))`.
- `finiteFormsBaseEquiv σ ρ K`: `𝒜_f(GJ, ρ, K)(L)`, whose published values
  lie in `L ⊗[L] W`, as the `W`-valued forms for `rationalBaseRep σ ρ`
  (`rationalFormsLidEquiv`).
- `finiteFormsBaseChangeEquiv σ ρ K S`, for
  `[Finite (DoubleCosets σ.finiteAdelicDiagonal K)]` and any commutative
  `L`-algebra `S`: the `S`-linear equivalence
  `S ⊗[L] finiteForms σ ρ L K ≃ finiteForms σ ρ S K`, the base change of
  `finiteFormsBaseEquiv` followed by `rationalFormsBaseChangeEquiv` (an
  `L`-algebra is free over the field `L`). `finiteFormsBaseChangeEquiv_tmul`:
  `s ⊗ f` goes to `g ↦ s ⊗ w_g`, where `w_g ∈ W` is `f g ∈ L ⊗[L] W` read in
  `W` by `TensorProduct.lid`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case". Worker 61
read the rendered scanned page. Printed p.307 (one-based PDF page 9): "For
any `L`-algebra `L'`, we let (3.2)
`𝒜_f(GJ, ρ, K)(L') = {f : GJ(𝔸^f)/K → W(L') | f(γ · g) = ρ(γ)f(g),
g ∈ GJ(𝔸), γ ∈ GJ(ℚ)}`" and "Obviously, for any `L`-algebra `L'`, there is
a canonical isomorphism (3.4)
`𝒜_f(GJ, ρ, K)(L') = 𝒜_f(GJ, ρ, K)(L) ⊗_L L'`. Restriction to `GJ(𝔸^f)`
defines a natural isomorphism `res : 𝒜_0(GJ, ρ, K) ⥲ 𝒜_f(GJ, ρ, K)(ℂ)` and
hence, via (3.4), a canonical `L`-structure on `𝒜_0(GJ, ρ, K)`." Printed
p.306 (one-based PDF page 8): "Let `K ⊂ GJ(𝔸^f)` be an open compact
subgroup". The reading of (3.2) as `finiteForms` is that of the published
`DefiniteForms.md`.

How the module relates to Harris (an explanation, not formalized):

- The map. Harris does not write out the "canonical isomorphism"; we read it
  as `s ⊗ f ↦ s · f`, that is `g ↦ s ⊗ f g` (`finiteFormsBaseChangeEquiv_tmul`),
  the evident map. Harris's `L'` is any `L`-algebra; here `S` is a
  commutative `L`-algebra in any universe.
- Finiteness. The isomorphism uses that `GJ(ℚ)\GJ(𝔸^f)/K` is finite, which
  Harris does not mention at (3.4); for an open compact `K` it is the
  finiteness of class numbers, which is not proved here and is an explicit
  hypothesis `[Finite (DoubleCosets σ.finiteAdelicDiagonal K)]`. Without it
  the map is still injective (`rationalFormsBaseChange_injective`), but it
  need not be surjective when `S` has infinite dimension over `L`.
- Generality. The generic `rationalFormsBaseChangeEquiv` holds for any
  commutative ring `R` and any `R`-algebra `S` that is free as an
  `R`-module; Harris's case is `R = L` a field, where every `L`-algebra is
  free (Mathlib's instance for division rings).
- Proof route. Harris gives no proof ("Obviously"). The proof here
  expands values in a basis of `S` over `L`: the coordinates of a form for
  `W(S)` are forms for `W`, and finitely many double cosets make only
  finitely many of them nonzero.
- Not formalized: the archimedean space (3.1), the restriction `res` and
  the resulting `L`-structure on `𝒜_0`, and compatibility of (3.4) with
  changing the level `K` or with Hecke operators.
- All declarations are ours, derived from Mathlib and the published modules
  named above. `rationalForms`, `rationalFormsScalar`, `coordinateForm`,
  `rationalFormsLidEquiv`, `rationalBaseRep` and `finiteFormsBaseEquiv` are
  internal constructions not printed in Harris 1999.

## Related declarations

- Library `Langlands.Shimura.EquivariantForms.formsBaseChangeEquiv`
  (`Shimura/DefiniteFormsLattice`): for the forms of `EquivariantForms.forms`
  (invariant on the left, twisted on the right) with values in an
  `S`-module that is the localization of an `O`-module at a submonoid,
  `S ⊗[O] forms ≃ forms`, also with finitely many double cosets; it gives
  Harris's lattice isomorphism. `rationalFormsBaseChangeEquiv` treats forms
  twisted on the left and free (not localized) scalar extensions.
- Library `Langlands.Cohomology.HyperextScalarExtension.invariantsBaseChangeMap`
  (`Cohomology/HyperextIsotypicBaseChange`) and
  `HyperextScalarExtension.invariantsBaseChangeEquivOfIsSMulRegular`
  (`Cohomology/HyperextHomLocalization`): base change of invariants of a
  representation, injective for flat and bijective for localized scalar
  extensions.
- Library `Langlands.Shimura.EquivariantForms.twistedForms`
  (`Shimura/EquivariantFormsTwist`): the special case of `rationalForms` for
  a representation of `G` (`twistedForms_eq_rationalForms`).

## Scope

The module proves (3.4) for one level `K` with finitely many double cosets.
It does not define `𝒜_0` (3.1) or `res`, does not prove the finiteness of
`GJ(ℚ)\GJ(𝔸^f)/K`, and does not treat naturality in `K`, Hecke operators,
or the `ℓ`-adic spaces (3.3) beyond the published (3.5).

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
