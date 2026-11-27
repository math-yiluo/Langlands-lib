# Rational torsion and geometric monodromy

The module `Langlands.AbelianScheme.RationalTorsionMonodromy` shows how
rational torsion forces the geometric monodromy on Tate modules to be
congruent to the identity. Let `B` be an abelian variety over a field `K`
and `n` a positive integer invertible in `K`, with
`HasRationalGeometricTorsion B n` (from
`Langlands/AbelianScheme/RaynaudSemiabelianCriterionStatement.lean`): every
`n`-torsion point with values in `AlgebraicClosure K` comes from a
`K`-point. Let `L` be a field over `K` and `s : Spec Ω → Spec L` a
geometric point, `Ω` algebraically closed. Then every `n`-torsion point of
the base change of `B` to `L` with values at `s` comes from an `L`-point
(`torsionPointsRational_baseChange`). Let moreover `ℓ` be a prime whose
powers are all invertible on `Spec L`, and `a` a natural number with
`ℓ ^ a ∣ n`. Then every element of the finite étale fundamental group of
`Spec L` at `s` acts on the integral `ℓ`-adic Tate module of the base change
of `B` to `L` by an endomorphism congruent to the identity modulo `ℓ ^ a`
(`monodromyMap_sub_one_valuesDivisible`). The helpers take both a
positivity witness `0 < n` and the invertibility `IsUnit (n : K)`; the
latter already forces `n ≠ 0`, hence `0 < n` for a natural number `n`, so
the positivity witness is redundant given invertibility. The proofs use
these hypotheses through the finiteness of the `n`-torsion subgroup scheme.
Without these hypotheses the base-change assertion fails once level zero
is admitted: for `n = 0`, an algebraically
closed `K` and a positive-dimensional `B`, every point over
`AlgebraicClosure K` comes from `K`, while the generic point of `B` over an
algebraic closure of the function field `K(B)` is killed by `0` and does
not come from a `K`-point.
The module also compares unipotence on the integral and rational Tate
modules.

## Spectra of fields

- `epi_specAlgebraMap`: for a field extension `F → A`,
  `Spec A → Spec F` is an epimorphism of schemes. The ring map is
  faithfully flat, so Mathlib's `flat_and_surjective_SpecMap_iff` makes
  the morphism flat and surjective, and `Flat.epi_of_flat_of_surjective`
  applies.
- `specAlgebraMap_preimage`: a morphism `s : Spec A → Spec F` of spectra of
  fields is `Spec.algebraMap F A` for the algebra structure given by the
  ring map `Spec.preimage s`.
- `epi_of_spec_field`: hence every morphism between spectra of fields is
  an epimorphism.

## Points over algebraically closed fields

`exists_algebraicClosure_pointFactorization` takes a finite morphism
`f : X → Spec K`, an algebraically closed field `Ω` over `K` and a point
`x : Spec Ω → X` over `K`. It produces a `K`-embedding
`emb : AlgebraicClosure K → Ω` (Mathlib's `IsAlgClosed.lift`) and a point
`y : Spec (AlgebraicClosure K) → X` over `K` with
`Spec.map emb ≫ y = x`. The proof follows that of
`RationalTorsionExtension.exists_finite_pointFactorization` in
`Langlands/AbelianScheme/RationalTorsionExtension.lean`. The field
`AlgebraicClosure K` replaces the splitting field. Every polynomial splits
over it, so `exists_algHom_factor_of_splits` factors the `K`-algebra map
`Γ(X, ⊤) → Ω` of `x` through `emb`.

`exists_section_of_hasRationalGeometricTorsion` takes `n > 0` invertible
in `K` and `HasRationalGeometricTorsion B n`. Let `t : Spec Ω → Spec K`
be any geometric point and `x` an `n`-torsion point of `B` over `t`. Then
`x` is the restriction along `t` of a `K`-point of `B`. Since `n` is
invertible, the torsion subgroup scheme is finite (the Library's
`torsionFiniteEtale`), and `x` factors through it. The previous lemma, for
the algebra structure defined by `t`, factors the torsion point through a
point over `AlgebraicClosure K`. The hypothesis makes that point the
restriction of a `K`-point `y_K`. Composing the spectrum maps gives
`t ≫ y_K = x`.

`exists_section_baseChange_of_hasRationalGeometricTorsion` transfers this
to the base change of `B` along `Spec L → Spec K`. The Library's
`GroupScheme.baseChangePointsEquiv` identifies points of the base change
with points of `B` over the composite. It respects the group law, so it
preserves `n`-torsion, and its naturality
(`baseChangePointsEquiv_naturality`) carries the factorization back.
`torsionPointsRational_baseChange` states the result in the form of the
next section.

## Monodromy on torsion levels

`TorsionPointsRational s A n` says that every `n`-torsion point of an
abelian scheme `A` over `Spec L`, with values at the geometric point
`s`, is `Over.homMk s ≫ y` for a point `y` of `A` over `L`.

`levelMonodromy_eq_self` proves that, under `TorsionPointsRational s A n`,
the Library's geometric monodromy `Tate.levelMonodromy` (in
`Langlands/AbelianScheme/Tate/FiniteMonodromy.lean`) fixes every point of
`Tate.Level A (Over.mk s) k`. Here `k > 0` divides `n` and is invertible on
`Spec L`. A point of the level is a point `p` of the kernel of
multiplication by `k`. Its image in `A` is `n`-torsion, hence equal to
`Over.homMk s ≫ y`.

- `y` is `k`-torsion: `Over.homMk s` is an epimorphism (its underlying
  morphism `s` is one by `epi_of_spec_field`), and precomposition respects
  powers (Mathlib's `GrpObj.comp_zpow`).
- `y` therefore lifts to the kernel. Then `p = Over.homMk s ≫ y'`, since
  the kernel inclusion is a monomorphism.
- The fundamental group acts on fibres naturally (`act_naturality` in
  `FiniteMonodromy.lean`). The action on points of the trivial cover
  `Spec L → Spec L` is trivial, because there is only one morphism from
  `Over.mk s` to the terminal object. Hence `p` is fixed.
- `finiteLevelMonodromy_kernel` translates this to the level.

`monodromyMap_sub_one_valuesDivisible` deduces, for a prime `ℓ` with
`ℓ ^ a ∣ n` and invertible powers of `ℓ`, that
`Tate.PrimeAdic.monodromyMap g - 1` has values divisible by `ℓ ^ a`
(`LinearAlgebra.CongruentQuasiUnipotent.ValuesDivisible`). The
level-`ℓ ^ a` coordinate of `σ x - x` is
`levelMonodromy g (x_a) - x_a = 0` (`evaluation_monodromyMap`). The
Library's `exists_smul_eq_of_evaluation_eq_zero` makes `σ x - x` a
multiple of `ℓ ^ a`.

## Integral and rational Tate modules

For an abelian scheme `A`, a test object `T` and a prime `ℓ`:

- `integral_eq_zero_of_nsmul_eq_zero`: the integral `ℓ`-adic Tate module
  has no `ℓ`-torsion (the Library's `eq_zero_of_prime_smul_eq_zero`).
- `integral_eq_zero_of_forall_dvd`: an element divisible by every power of
  `ℓ` is zero. Its level-`ℓ ^ j` coordinate is `ℓ ^ j` times a point of the
  level, which `ℓ ^ j` kills (`level_nsmul_eq_zero`).
- `monodromyMap_pow`: the integral monodromy of `g ^ m` is the `m`-th power
  of that of `g`.
- `rationalMonodromyRepresentation_toLinearMap`: the rational monodromy is
  the scalar extension to `ℚ_[ℓ]` of the integral one (by definition).
- `isNilpotent_baseChange_iff`: an endomorphism of the integral Tate module
  is nilpotent if and only if its scalar extension is. One direction is
  `LinearMap.baseChange_pow`. For the other, `1 ⊗ f ^ N x = 0` gives
  `f ^ N x = 0` by the Library's injectivity `toRational_injective`.
- `isNilpotent_rationalMonodromy_sub_one_iff` and
  `isNilpotent_rationalMonodromy_pow_sub_one_iff`: an element, or a power
  of an element, acts unipotently on the rational Tate module if and only
  if its integral monodromy is unipotent.

## Provenance

The results are derived from the Library's definitions. The premise that
inertia fixes the rational `n`-torsion points is the starting point of the
proof of Raynaud's criterion in SGA 7 I, Exposé IX, Proposition 4.7. There
the trivial action on `n`-torsion is applied to the essentially fixed part
of the torsion, which is identified with torsion in the semiabelian special
fibre of a model with semistable reduction, and Serre's lemma on
automorphisms of finite order of a semiabelian group (Lemme 4.7.1, proved
in 4.7.3) concludes. Silverberg and Zarhin, *Semistable reduction and
torsion subgroups of abelian varieties*, Ann. Inst. Fourier 45 (1995),
Theorem 3.5, state the criterion with a reference to that argument. Their
Theorem 4.1 treats an element of finite multiplicative order of an integral
domain of characteristic zero that is congruent to `1` modulo `n`, where no
prime dividing `n` is a unit.

The congruence of the whole integral Tate-module monodromy modulo `ℓ ^ a`
is not taken from these sources. It is derived here from the naturality of
the fundamental-group action on the finite étale torsion level
(`levelMonodromy_eq_self`) and from the description of the kernel of
evaluation at level `ℓ ^ a` (the Library's
`exists_smul_eq_of_evaluation_eq_zero`). The sources work with the Galois
group acting on points over a separable closure. The Library's fundamental
group acts on fibres of finite étale covers at a geometric point, and the
trivial action on points that come from sections is the naturality of that
action.
