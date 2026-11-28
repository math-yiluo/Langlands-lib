# Kummer covers and the Kummer character

The module `Langlands.AlgebraicGeometry.FiniteEtale.KummerCovers` builds,
for a commutative ring `A : Type u`, a unit `a` of `A` and a positive integer
`m` invertible in `A`, the finite étale Kummer cover
`Spec A[X]/(X^m - a) → Spec A` as an object of the Library's category
`Cover (Spec A)`. It lets `m`-th roots of unity act on it by `X ↦ ζX`, and it
defines the Kummer character, the homomorphism from the finite étale
fundamental group to the roots of unity describing the action on a geometric
fibre. With `A = R[1/t]` and `a = t` this is the Kummer cover
`Spec (KummerAlgebra t m)` of the Library module `KummerFactorizationStatement`.

## Algebra

- `KummerRootAlgebra a m` is the abbreviation `AdjoinRoot (X ^ m - C a)`.
  For `A = Localization.Away t` and `a = algebraMap R A t` it is literally
  `KummerAlgebra t m`. `kummerRoot_pow` records `X^m = a`.
- `kummerRootMorphism a m` is `Spec.map` of the structure map; it is
  definitionally the Library's `kummerMorphism t m` in that case.
- `kummerRoot_isFinite` (for `m > 0`, since `X^m - a` is monic) and
  `kummerRoot_etale` (for `m > 0` with `m` and `a` units, from
  `AdjoinRoot.etale_X_pow_sub_C` in the pinned package
  `WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale`) give the cover
  `kummerRootCover a m hm0 hm ha : Cover (Spec A)` via the Library's
  `cover`; `kummerRootCover_hom` says its structure morphism is
  `kummerRootMorphism a m`.
- For a ring `R` with `[Algebra R A]` and `ζ` in `rootsOfUnity m R`,
  `kummerScale R a m ζ` is the `A`-algebra endomorphism `X ↦ ζX`
  (`kummerScale_root`).
- `kummerLevel a hmn`, for `m * d = n`, is the `A`-algebra map
  `A[X]/(X^m - a) → A[X]/(X^n - a)`, `X ↦ X^d` (`kummerLevel_root`).
- `kummerUnitSection m` is the `A`-algebra map `A[X]/(X^m - 1) → A`,
  `X ↦ 1`.

## Geometric fibres

Fix a field `Ω : Type u` and a point `x : Spec Ω ⟶ Spec A`.

- `kummerPointHom` is the ring map `A[X]/(X^m - a) → Ω` of a point `p` of the
  fibre `Fiber x (kummerRootCover …)` (by `Spec.preimage`);
  `kummerPointHom_spec`, `algebraMap_comp_kummerPointHom` and
  `kummerPointHom_algebraMap` say it lies over `x`.
- `kummerRootValue p` is the image of `X` in `Ω`. It satisfies
  `kummerRootValue_pow` (`value^m` is the image of `a`) and
  `kummerRootValue_ne_zero`, and `kummerRootValue_injective` shows that a
  point is determined by its value (a map out of `AdjoinRoot` is determined
  by the image of the root).
- `kummerPointOfRoot r hr` is the point with value a given `m`-th root `r` of
  the image of `a` (`kummerRootValue_pointOfRoot`). Hence
  `kummerFiber_nonempty` when `Ω` is algebraically closed, and
  `kummerFiber_finite_and_card_le`: the fibre is finite with at most `m`
  points (values are among the roots of `X^m - c`, Mathlib's `nthRoots`).
- `kummerScaleHom a m hm0 hm ha R ζ` is the cover endomorphism induced by
  `kummerScale R a m ζ`; `kummerRootValue_scale` says it multiplies the value
  by the image of `ζ`, and `kummerScale_comp`, `kummerScale_one` make it a
  right action of `rootsOfUnity m R` on the fibre.

## Torsor structure

Assume `R` is local and `m` is invertible in `R`.

- `rootsOfUnity_eq_of_map_eq`: distinct `m`-th roots of unity of `R` have
  distinct images in every nonzero ring (by
  `StrictlyHenselianKummerUnits.eq_one_of_pow_eq_one_of_map_eq_one`).
- `kummerScale_injective`: `ζ ↦ p · ζ` is injective on the fibre, since the
  values `ζ · value(p)` differ.
- `kummerScale_bijective`: if moreover `Nat.card (rootsOfUnity m R) = m`, this
  map is bijective (injective, and the fibre has at most `m` points). So the
  fibre is a torsor under `rootsOfUnity m R`.
- `kummerScale_eq_self_iff`: `p · ζ = p` iff `ζ = 1`.

## The Kummer character

Assume in addition that `Ω` is algebraically closed, that
`hx : ∀ Y : Cover (Spec A), Finite (Fiber x Y)` (so that the Library's
`FundamentalGroup x hx` is defined), and that
`hcardR : Nat.card (rootsOfUnity m R) = m`.

- `kummerBasePoint` is a chosen point of the fibre.
- `kummerCharacterFun g` is the unique root of unity `ζ` with
  `g • base = base · ζ` (`smul_kummerBasePoint`), and
  `smul_eq_comp_kummerScale` extends this to every point `p`: write
  `p = base · η` and use that the action of `g` commutes with the cover map
  `kummerScaleHom … η` (`smul_naturality`) and that roots of unity commute.
- `kummerCharacter a m hm0 hm ha x hx R hmR hcardR` is this function as a
  group homomorphism `FundamentalGroup x hx →* rootsOfUnity m R`;
  multiplicativity again uses `smul_naturality` and `kummerScale_comp`.
- `smul_eq_comp_kummerCharacter`: `g • p = p · κ(g)` for every point `p`.
- `smul_eq_self_iff_kummerCharacter` and `ker_kummerCharacter`: the kernel of
  `κ` is the stabilizer of any point `p` of the fibre.
- `isOpen_ker_kummerCharacter`: the kernel is open, since stabilizers are
  open for the Library's `continuous_evaluation`.

## Compatibility between levels and the unit parameter

- `kummerLevelHom` is the cover map `Spec A[X]/(X^n - a) → Spec A[X]/(X^m - a)`
  of `kummerLevel`, `m * d = n`; `kummerRootValue_level` says it raises values
  to the `d`-th power.
- `kummerCharacter_level`: for `m * d = n` (both invertible, both with the
  full number of roots of unity), `κ_m(g) = κ_n(g)^d` in `R`. Apply
  `smul_naturality` to the image under `kummerLevelHom` of a point `p` of
  level `n`, compare values, cancel `value(p)^d ≠ 0`, and conclude with
  `rootsOfUnity_eq_of_map_eq`.
- `kummerUnitSectionHom`, `identityCoverPoint`, `identityCover_subsingleton`,
  `kummerUnitPoint`, `smul_kummerUnitPoint`: for `a = 1`, the section `X ↦ 1`
  maps the one point of the identity cover to a point of the Kummer fibre,
  which is therefore fixed by the fundamental group.
- `kummerCharacter_one_eq_one`: the Kummer character of `a = 1` is trivial.

## Provenance

The cover with unit parameter `a` is the classical binomial Kummer cover.
The character records the action on the roots of `X^m = a` in the geometric
fibre.
The localization construction `A_f[x]/(x^e - f)` is the form in the Stacks
Project, *Fundamental Groups of Schemes*, [Example 58.31.4 (Tag 0EYF)](https://stacks.math.columbia.edu/tag/0EYF).

For a strictly Henselian discrete valuation ring `R` with residue field
`k`, take `A = Frac(R)` and let `a` be a uniformizer of `R`. For positive
`m` invertible in `R`, an `m`-th root `r` of `a` has valuation `1/m` when
the valuation of `a` is normalized to `1`. Under the absolute Galois
interpretation of the fundamental group of `Spec A`, the character gives the
ratio `g(r)/r` in the `m`-th roots of unity of `R`. Reduction identifies
those roots with `μ_m(k)` and gives
Deligne's level-`m` projection from tame inertia `I/P` to `μ_m(k)`.
See P. Deligne, *Résumé des premiers exposés de A. Grothendieck*, SGA 7 I,
Exposé I, §0.3, pp. I-3–I-4.
