# Partial derivatives on completed localizations of polynomial rings

This helper module for the proof of
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` builds the
derivations needed by the fibre-regularity criterion
`isRegularRing_fiber_of_jacobian` (module `FiberRegular`) on a polynomial ring
over a completed localization of a polynomial ring. All declarations are in
the namespace `Langlands.CommutativeAlgebra.FiniteTypeIntGRing`.

Derivations are encoded as ring maps into trivial square-zero extensions
`TrivSqZeroExt T V = T ⊕ V`, as in the module `JacobianQuotient`.

## Statements

**Jets.** Let `S`, `T` be commutative rings and `V` a `T`-module (with the
same left and right action).

- `jetHom f d hd : S →+* TrivSqZeroExt T V` is `x ↦ (f x, d x)` for a ring map
  `f : S →+* T` and an additive map `d : S →+ V` with
  `hd : d (a b) = f a • d b + f b • d a`. The simp lemmas `jetHom_fst` and
  `jetHom_snd` give its components.
- `map_pderiv_X κ v w`: any ring map `κ` from `R[X_τ]` sends `∂X_w/∂X_v` to the
  Kronecker delta `Pi.single w 1 v`.
- `pderivJet κ : R[X_τ] →+* TrivSqZeroExt F (τ → F)` is
  `g ↦ (κ g, v ↦ κ (∂g/∂X_v))` for a ring map `κ : R[X_τ] →+* F`.

**Derivations on a localization.** Let `R₀` be a commutative ring, `σ` a type
and `A₀` the localization of `R₀[X_σ]` at a submonoid `M`.

- `polyJet A₀ i : R₀[X_σ] →+* TrivSqZeroExt A₀ A₀` is
  `p ↦ (p, ∂p/∂X_i)`, with values in `A₀`.
- `localJet M i : A₀ →+* TrivSqZeroExt A₀ A₀` extends it to `A₀`, with
  `localJet_algebraMap` (it extends `polyJet`) and `localJet_fst` (its first
  component is the identity).
- `localDeriv M i : A₀ →+ A₀` is its second component: the partial derivative
  `∂/∂X_i` on `A₀`. `localDeriv_algebraMap` says that it extends `∂/∂X_i` of
  `R₀[X_σ]`, and `localDeriv_mul` gives the Leibniz rule.

**Derivations on the completion.** Let moreover `μ` be a type, `σ` and `μ`
with decidable equality, `I` an ideal of `A₀`, and `Â₀ = AdicCompletion I A₀`.

- `hatDeriv M I : σ ⊕ μ → (Â₀ →+ Â₀)` is the extension
  `completionDeriv` (module `CompletionDerivation`) of `localDeriv M i` for
  indices `inl i`, and `0` for indices `inr j`. `hatDeriv_mul` gives the
  Leibniz rule, and `hatDeriv_inl_algebraMap` says that on the image of
  `p ∈ R₀[X_σ]` the derivation `hatDeriv (inl i)` is the image of `∂p/∂X_i`.
- For a ring map `ρ : Â₀[Y_μ] →+* F` into a commutative ring `F`:
  `coeffJet M I ρ : Â₀ →+* TrivSqZeroExt F (σ ⊕ μ → F)` is
  `b ↦ (ρ (C b), v ↦ ρ (C (hatDeriv v b)))`, and
  `completedJet M I ρ : Â₀[Y_μ] →+* TrivSqZeroExt F (σ ⊕ μ → F)` is the
  evaluation map extending `coeffJet` by
  `Y_j ↦ (ρ (Y_j), Pi.single (inr j) 1)`. `completedJet_fst` says its first
  component is `ρ`.
- `completedJet_snd_algebraMap M I ρ hB₁ hB₂ g`: suppose `Â₀[Y_μ]` is an
  `R₀[X_σ, Y_μ]`-algebra (with `R₀[X_σ, Y_μ] = MvPolynomial (σ ⊕ μ) R₀`) such
  that (`hB₁`) the image of `p ∈ R₀[X_σ]` is the constant polynomial of the
  image of `p` in `Â₀`, and (`hB₂`) `Y_j` maps to `Y_j`. Then for every
  `g ∈ R₀[X_σ, Y_μ]` the second component of `completedJet` at the image of
  `g` is `v ↦ ρ (image of ∂g/∂X_v)`.
- `isRegularRing_fiber_completedPolynomial M I hB₁ hB₂ N` (**main
  theorem**): suppose in addition that `σ` and `μ` are finite, `R₀` is
  Noetherian and `Â₀[Y_μ]` is a regular ring. Then for every prime `N` of
  `R₀[X_σ, Y_μ]` whose residue field is formally smooth over `R₀`, the fibre
  `N.Fiber Â₀[Y_μ]` is a regular ring.

The module is internal to the project's proof and does not follow a specific
reference.

## Proofs

**Jets.** `jetHom` is a ring map because multiplication in
`TrivSqZeroExt T V` is `(a, x)(b, y) = (a b, a • y + b • x)`. The Leibniz rule
`hd` is exactly the second component of multiplicativity (the right action is
the left one, `op_smul_eq_smul`), and `hd 1 1` gives `d 1 = 0`. For
`map_pderiv_X`, distinguish `v = w` from `v ≠ w` and use `pderiv_X`.
`pderivJet` is `jetHom` with `d g = (v ↦ κ (∂g/∂X_v))`, whose Leibniz rule is
`Derivation.leibniz` for each `pderiv v`.

**Localization.** `polyJet` is `jetHom` of `R₀[X_σ] → A₀` with
`d p = image of ∂p/∂X_i`. Its values on `M` have unit first components, hence
are units (`isUnit_iff_isUnit_fst`), so `IsLocalization.lift` extends it to
`localJet`. The first component of `localJet` is a ring map `A₀ → A₀` that is
the identity on the image of `R₀[X_σ]`, hence the identity
(`IsLocalization.ringHom_ext`). The second component `localDeriv` is
additive. Multiplicativity of `localJet` together with `localJet_fst` gives
its Leibniz rule.

**Completion.** For `inl i`, `hatDeriv` is `completionDeriv` of `localDeriv`,
whose Leibniz rule is `completionDeriv_mul`. On the image of `p` it is
`completionDeriv_of` followed by `localDeriv_algebraMap`. For `inr j` it is
zero. `coeffJet` is `jetHom` of `ρ ∘ C` with these reduced derivations.
`completedJet_fst` compares two ring maps out of `Â₀[Y_μ]` on constants and
variables (`MvPolynomial.ringHom_ext`).

**Derivatives of images.** Write `κ` for `ρ` composed with the structure map
`R₀[X_σ, Y_μ] → Â₀[Y_μ]`. It suffices that `completedJet` composed with the
structure map is `pderivJet κ`. By `MvPolynomial.ringHom_ext` this is checked
on constants and variables, and componentwise; the first components agree by
`completedJet_fst`.

- On a constant `a ∈ R₀`, `hB₁` (applied to `C a`) reduces `completedJet` to
  `coeffJet`. The derivative of a constant is `0` for both kinds of index
  (`hatDeriv_inl_algebraMap` with `∂a/∂X_i = 0`, and `hatDeriv (inr j) = 0`).
- On `X_i` (`v = inl i`), `hB₁` again reduces to `coeffJet`. The
  `inl i'`-component is the reduction of `∂X_i/∂X_i'`, which is the Kronecker
  delta by `map_pderiv_X`. The `inr j'`-component is `0`, as is
  `∂X_i/∂Y_j'`.
- On `Y_j` (`v = inr j`), `hB₂` gives the image `Y_j`, whose `completedJet`
  value has second component `Pi.single (inr j) 1`, the Kronecker delta of
  `∂Y_j/∂ –` (`map_pderiv_X`).

**Main theorem.** Apply `isRegularRing_fiber_of_jacobian` with
`τ = σ ⊕ μ`, `B = Â₀[Y_μ]`, and, for every prime `r` of `B`,
`Φ r = completedJet M I ρ` for the residue map `ρ : B → κ(r)`. The conditions
`hΦ₁` and `hΦ₂` are `completedJet_fst` and `completedJet_snd_algebraMap`.
