# Positive traces and invariant forms on simple modules

Author: Worker 5219.

The module `Langlands.LinearAlgebra.PositiveTraceForms` (namespace
`Langlands.PositiveTraceForms`) contains the purely algebraic core of the
following classical fact. If the trace of a finite-dimensional representation
is a positive functional, then every irreducible subquotient is unitarizable,
with a unitary structure that is unique up to a positive scalar. It is written as
a helper for `Langlands.UnitaryCharacterLimitSubquotientsStatement`. That
statement is used in Tadić's argument (Tadić 1986, Proposition 2.9) that the end
points of a complementary series have unitary constituents. The algebra used is
standard (Burnside's density theorem, the Jacobson density theorem, the
Cauchy–Schwarz inequality, composition series). The module is derived internal
work and does not follow a particular source.

Throughout, `A` is a ring with `[Algebra ℂ A]`. Modules `M` carry both a complex
structure and an `A`-module structure that are compatible, `[IsScalarTower ℂ A M]`.
Sections about the involution add `[StarRing A]`, and also `[StarModule ℂ A]`
where conjugate linearity of `star` is needed. Universes of `A`, of the modules
and of index types are independent.

## Definitions

- `act M a : Module.End ℂ M` is the complex-linear action of `a : A`
  (`DistribSMul.toLinearMap ℂ M a`). `actLinear M : A →ₗ[ℂ] Module.End ℂ M` is
  the same map, bundled as a complex-linear map.
- `StarInvariantForm A V` extends `InnerProductSpace.Core ℂ V`. It is a positive
  definite Hermitian form `inner` on `V`, conjugate-linear in its **first**
  argument and linear in the second (Mathlib's convention). It has one extra
  field, `adjoint a v w : inner (a • v) w = inner v (star a • w)`, which says that
  `star a` is adjoint to `a`. The structure needs only `[Ring A] [StarRing A]`
  and complex and `A`-module structures on `V`.
- `StarInvariantForm.comapEquiv b e` pulls a form `b` on `N` back along an
  `A`-linear equivalence `e : V ≃ₗ[A] N` (it needs `[Algebra ℂ A]` and both
  scalar towers). Its inner product is `b.inner (e v) (e w)`.
- `SimpleFDModule A` bundles a type with instances `AddCommGroup`, `Module ℂ`,
  `Module A`, `IsScalarTower ℂ A`, `FiniteDimensional ℂ` and `IsSimpleModule A`.
  `SimpleFDModule.traceAct F a` is the trace of `act F.carrier a`.

## Results

### Traces

- `trace_eq_add_of_exact`: for a short exact sequence `0 → N → M → Q → 0` of
  finite-dimensional complex spaces and endomorphisms `TN, TM, TQ` that commute
  with the two maps, `trace TM = trace TN + trace TQ`. This is the Library lemma
  `FiniteRankEnd.trace_shortExact`, specialized through
  `FiniteRankEnd.trace_eq_ambient`. `mem_finiteRankEnd` records that every
  endomorphism of a finite-dimensional space has finite rank.
- `trace_act_eq_add S a`: for a submodule `S` of a finite-dimensional module
  `M`, the trace of `a` on `M` is its trace on `S` plus its trace on `M ⧸ S`.
- `trace_act_eq_of_equiv`, `act_eq_zero_of_equiv`: isomorphic modules have the
  same traces, and an element acting by zero on one acts by zero on the other.
- `act_mul`, `act_sub`, `act_apply`, `actLinear_apply`: elementary identities.

### Density

Here `M : ι → Type` is a finite family (`[Fintype ι]`) of finite-dimensional
simple modules.

- `exists_isotypic_action M j`: there is `r : A` that acts as the identity on
  every `M i` isomorphic to `M j` and as zero on all other `M i`. Proof: the
  coordinate projection `q` onto the members isomorphic to `M j` commutes with
  every `A`-endomorphism of `∀ i, M i`. By Schur's lemma, no nonzero
  `A`-linear map goes between non-isomorphic members. So `q` is linear over
  `Module.End A (∀ i, M i)`, and Mathlib's `jacobson_density` gives an `r`
  that agrees with `q` on the finite set of vectors `Pi.single i (b i k)`, where
  `b i` is a basis of `M i`.
- `exists_act_eq T` (Burnside): for a finite-dimensional simple module `V`,
  every `T : Module.End ℂ V` is `act V x` for some `x : A`. This is the Library
  theorem `SandwichDimensionBound.action_surjective`.
- `act_eq_zero_of_trace_mul a h`: on a finite-dimensional simple module `V`, if
  `trace (act V (x * a)) = 0` for all `x`, then `act V a = 0`. Otherwise choose
  `v` with `a • v ≠ 0` and a functional `ℓ` with `ℓ (a • v) ≠ 0`. Burnside gives
  `x` that acts as the rank-one map `u ↦ ℓ u • v`. Then
  `trace (act V (x * a)) = ℓ (a • v) ≠ 0`, which is a contradiction.
- `act_eq_zero_of_sum_trace_mul M a h j`: if
  `∑ i, trace (act (M i) (x * a)) = 0` for all `x`, then `a` acts by zero on
  every `M j`. Substituting `r * x` with the isotypic element `r` for `j` turns
  the sum into `(number of i with M i ≅ M j) * trace (act (M j) (x * a))`.
  The count is nonzero, so the previous lemma applies.
- `act_mul_eq_zero_of_isotypic`: if `r` is as in `exists_isotypic_action` for
  `j` and `y` acts by zero on `M j`, then `y * r` acts by zero on every `M i`.

### Positive functionals

These assume `[StarRing A] [StarModule ℂ A]`. Here `t : A →ₗ[ℂ] ℂ` satisfies
`ht : ∀ a, 0 ≤ t (star a * a)`, with `≤` the partial order on `ℂ` in which
nonnegative means real and nonnegative.

- `conj_apply_star_mul t ht a b : conj (t (star a * b)) = t (star b * a)`. This
  is polarization: the imaginary parts of `t` on `star c * c` vanish for
  `c = a`, `b`, `a + b` and `a + I • b`, and these four expansions determine the
  real and imaginary parts of the two cross terms. `im_eq_zero_of_nonneg` is
  the auxiliary fact that a nonnegative complex number has zero imaginary part.
- `starMulCore t ht` is the semi-definite form `(a, b) ↦ t (star a * b)`, as a
  `PreInnerProductSpace.Core ℂ A`.
- `apply_star_mul_eq_zero t ht ha b`: if `t (star a * a) = 0`, then
  `t (star b * a) = 0` for every `b`. This follows from Mathlib's Cauchy–Schwarz
  inequality `InnerProductSpace.Core.inner_mul_inner_self_le` for
  `starMulCore`.

### Construction of the form

`exists_starInvariantForm_of_sum M t ht htr j` assumes
`[StarRing A] [StarModule ℂ A]`, a finite family `M` of finite-dimensional
simple modules, a functional `t` that is nonnegative on every `star a * a`, and
`htr : ∀ a, t a = ∑ i, trace (act (M i) a)`. It concludes
`Nonempty (StarInvariantForm A (M j))` for every `j`.

Construction. Let `r` be the isotypic element for `j`. Let `σ` be a
complex-linear right inverse of the surjective map `actLinear (M j)`
(Burnside). Let `ℓ` be a functional with `ℓ v₀ ≠ 0` for some `v₀ ≠ 0`. Put
`Φ v = σ (ℓ.smulRight v) * r`, a complex-linear map `M j → A` with
`act (M j) (Φ v) = (u ↦ ℓ u • v)`. Define `inner v w = t (star (Φ v) * Φ w)`.

- Hermitian symmetry is `conj_apply_star_mul`, and the nonnegativity of
  `re (inner v v)` comes from `ht`. Additivity and conjugate linearity in the
  first argument follow from the linearity of `Φ` and `t`.
- Definiteness. If `inner v v = 0`, then `t (x * Φ v) = 0` for all `x`
  (`apply_star_mul_eq_zero` applied with `star x`). So by
  `act_eq_zero_of_sum_trace_mul`, `Φ v` acts by zero on `M j`. Evaluating
  `u ↦ ℓ u • v` at `v₀` gives `v = 0`.
- Adjointness. The defect `d = Φ (c • u) - c * Φ u` equals
  `(σ (L (c • u)) - c * σ (L u)) * r`, where `L v = ℓ.smulRight v`, and the
  left factor acts by zero on `M j`. So `d` acts by zero on every `M i`
  (`act_mul_eq_zero_of_isotypic`). Hence `t (x * d) = 0` and, by Hermitian
  symmetry, `t (star d * x) = 0` for all `x`. Expanding `Φ (a • v)` and
  `Φ (star a • w)` with their defects then gives
  `t (star (Φ (a • v)) * Φ w) = t (star (Φ v) * Φ (star a • w))`, using
  `star (a * Φ v) = star (Φ v) * star a`.

### Composition factors

`exists_composition_factors M` (for a finite-dimensional module `M`, no star
needed) produces a list `L : List (SimpleFDModule A)` with:

1. `∀ a, trace (act M a) = (L.map (·.traceAct a)).sum`;
2. for any `A`-modules `W` and `V` with `V` simple, an injective `ι : W →ₗ[A] M`
   and a surjective `f : W →ₗ[A] V`, some `F ∈ L` has `V ≃ₗ[A] F.carrier`.

The proof is induction on a bound for `finrank ℂ M`. If `M` is trivial, the
empty list works (`composition_factors_of_subsingleton`): a simple module is
nontrivial, so it cannot be a quotient of the trivial `W`. Otherwise `M` is
Artinian over `A`, so it has an atom `S`, a simple submodule. The quotient
`M ⧸ S` has smaller dimension. Take `S :: L`, where `L` comes from `M ⧸ S`.
Trace additivity is `trace_act_eq_add`. For a subquotient `(W, ι, f)`, let
`g = mkQ ∘ ι`. If `ker g ≤ ker f`, then `f` factors through `W ⧸ ker g`, which
embeds into `M ⧸ S`, and the induction hypothesis applies. Otherwise `ι`
restricts to an isomorphism `ker g ≅ S`: it is injective, and its image is not
zero because some `w ∈ ker g` has `f w ≠ 0`. Moreover, `f` restricted to `ker g`
is a nonzero map between simple modules, hence an isomorphism. So `V ≅ S`.

### Main theorem

`exists_starInvariantForm_of_subquotient M hpos ι hι f hf` takes
`[StarRing A] [StarModule ℂ A]`, a finite-dimensional module `M` with
`hpos : ∀ a, 0 ≤ trace (act M (star a * a))`, an `A`-module `W` (no complex
structure needed), a simple `A`-module `V` with a compatible complex structure,
an injective `ι : W →ₗ[A] M` and a surjective `f : W →ₗ[A] V`. It concludes
`Nonempty (StarInvariantForm A V)`. `V` is not assumed finite-dimensional.

Proof: take the composition factors `L` of `M`, and let `t` be the trace of the
action on `M`. Then `t` is nonnegative on `star a * a` and equals the sum of the
traces over `Fin L.length`. `exists_starInvariantForm_of_sum` gives a form on
the factor isomorphic to `V`, and `comapEquiv` transports it to `V`.

### Uniqueness

These need `[Ring A] [Algebra ℂ A] [StarRing A]` and a finite-dimensional simple
module `V`, but no `StarModule`.

- `StarInvariantForm.inner_mul_inner_eq b b' v₀ x w`: for star-invariant forms
  `b` and `b'` on `V`,
  `b.inner v₀ v₀ * b'.inner x w = b'.inner v₀ v₀ * b.inner x w`.
  Proof: Burnside gives `a` acting as `u ↦ b.inner v₀ u • x`. Its `b`-adjoint
  shows that `star a` acts on `w` as `b.inner x w • v₀`
  (`eq_of_forall_inner_eq`). Applying `b'.adjoint a v₀ w` and expanding both
  sides gives the identity.
- `StarInvariantForm.exists_pos_real_eq b b'`: there is a real `r > 0` with
  `b'.inner x w = r * b.inner x w` for all `x` and `w`. Take `v₀ ≠ 0`. Both
  `b.inner v₀ v₀` and `b'.inner v₀ v₀` are real and positive, and
  `r = re (b'.inner v₀ v₀) / re (b.inner v₀ v₀)`.

Auxiliary lemmas about a form `b`: `inner_add_right`, `inner_smul_right`
(linearity in the second argument), `conj_inner_self` (`b.inner v v` is real)
and `eq_of_forall_inner_eq` (nondegeneracy in the second argument).
