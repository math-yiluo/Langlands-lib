# Quadratic cocycles through a central isogeny with kernel killed by `3`

Module: `Langlands.GroupScheme.Rational.CentralCubeKernelQuadraticLift`.

Let `p : X ⟶ D` be a central isogeny (`IsCentralIsogeny p`) of group schemes over `Spec F`,
`F` a field, such that every point of `X` over a field `K` (an `F`-algebra) that is killed by
`p` has cube one:

```lean
∀ (K : Type u) [Field K] [Algebra F K] (x : X.affinePoints (CommAlgCat.of F K)),
  X.affinePointsTarget p (CommAlgCat.of F K) x = 1 → x ^ 3 = 1
```

Lemma 6.33 of Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8,
printed pp. 384–385, uses that the order of the kernel `H ∩ B` of `H × B → D = H·B`
divides `3`. This divisibility suffices for the cube condition since the `K`-points are
a subgroup of the geometric kernel points. For `B = Z_G(H)°`, the cocharacter lattice
calculation gives order exactly `3`.
[`Rational.NumberFieldTypeE6QuadraticCentralProduct`](NumberFieldTypeE6QuadraticCentralProduct.md)

The module gives cochain proofs of the lifting and archimedean steps of Lemma 6.33 on a
quadratic cover. `TypeA2CentralIsogenyFactorization.isTrivial_map` uses the two lemmas.

- `IsCentralIsogeny.exists_cohomologous_map_of_cube_kernel`: for a quadratic Galois extension
  `E/F` of a field of characteristic zero, every cocycle of `D` on the cover
  `GaloisCocycle.cover F E` (that is, `Spec E → Spec F`) is cohomologous to the image under
  `p` of a cocycle of `X` on the same cover;
- `IsCentralIsogeny.isTrivial_baseChange_of_cube_kernel`: over a field `K` over `F` with an
  algebraically closed Galois extension `M` of degree `2` (for example the completion at a
  real place of a number field), a cocycle of `X` is trivial on the full pullback cover to
  `Spec K` as soon as its image in `D` is.

The source argues in cohomology: the class of `ξ` in `H²(F, H ∩ B)` dies over `E`, so it is
killed by `[E : F] = 2` by restriction–corestriction and by `3`, hence vanishes; and
`H¹(F_v, H ∩ B) = 1` at the archimedean places. This module replaces both cohomological
arguments by explicit cochain computations on the given covers (provenance: derived from the
source's argument; the computations are given below).

## Conventions

- `GaloisCocycle.value ξ σ` is the value of a cocycle `ξ` on `GaloisCocycle.cover F E` at
  `σ ∈ Gal(E/F)`, a point of the group over `E`; the cocycle identity reads
  `value ξ (σ τ) = value ξ σ · σ(value ξ τ)` (`GaloisCocycle.value_mul`), where `σ(x)` is
  `conjugate F E G σ x`.
- `ξ.twist f` is the cocycle `(a, b) ↦ f(a)⁻¹ ξ(a, b) f(b)`, and `ξ.Cohomologous ζ` means
  `ζ = ξ.twist f` for some `f`; `IsTrivial` means being a twist of the trivial cocycle.
- `relativeExtend F E M`, `relativeConjugate F E M` and `relativeDescend F E M` are the
  extension of coefficients from `E` to `M`, the action of `Gal(M/E)` on `M`-points, and the
  descent of `Gal(M/E)`-fixed `M`-points to `E`-points (module `GaloisPointTower`).

## Auxiliary statements

- `affinePointsTarget_conjugate`, `affinePointsTarget_relativeExtend`,
  `affinePointsTarget_relativeConjugate`: a homomorphism of group schemes over `Spec k`
  commutes on coefficient points with the Galois action, with extension of coefficients and
  with the relative Galois action. Each is the naturality square of `affinePointsTarget`.
- `GaloisCocycle.value_map`: `value (ξ.map φ) σ` is the image of `value ξ σ` (by definition).
- `GaloisCocycle.value_twist`: `value (ξ.twist f) σ = f⁻¹ · value ξ σ · σ(f)`.
- `GaloisCocycle.value_one`: `value ξ 1 = 1`, from the cocycle identity at `(1, 1)`.
- `exists_eq_one_or_eq_of_card_eq_two`: a finite group of order `2` is `{1, s}` with
  `s ≠ 1` and `s · s = 1`.
- `IsCentralIsogeny.commute_of_affinePointsTarget_eq_one`: a point killed by a central
  isogeny commutes with every point over the same test algebra (centrality of the kernel,
  `isCentral_kernelι_iff`).

## The quadratic lift

`IsCentralIsogeny.exists_cohomologous_map_of_cube_kernel` assumes `CharZero F`, that `X` and
`D` are affine, `Module.finrank F E = 2`, `IsGalois F E` and the cube condition. Let `σ` be the
nonidentity automorphism of `E/F` and `a = value ξ σ ∈ D(E)`.

1. The cocycle identity at `(σ, σ)` gives `a σ(a) = 1`, so `σ(a) = a⁻¹`.
2. `exists_finiteGalois_coefficient_lifts` gives a finite Galois extension `M/F` containing `E`
   and `b ∈ X(M)` with `p(b) = a`. For `τ ∈ Gal(M/E)` the point `c = b⁻¹ τ(b)` is killed by
   `p` (because `τ` fixes `a`), so it is central and `c³ = 1`; hence
   `τ(b³) = (b c)³ = b³ c³ = b³`. So `b³` is `Gal(M/E)`-fixed and descends to `x ∈ X(E)`,
   and `p(x) = a³` by injectivity of extension of coefficients on `D`.
3. `z = x σ(x)` satisfies `p(z) = a³ σ(a)³ = 1`, so `z` is central and `z³ = 1`. Since
   `σ² = 1`, `σ(z) = σ(x) x = x⁻¹ z x = z`.
4. `y = x z` satisfies `y σ(y) = x z σ(x) z = x σ(x) z² = z³ = 1` and `p(y) = a³`.
5. The function `c` on `Gal(E/F)` with `c(1) = 1` and `c(σ) = y` satisfies the cocycle
   identity (checked on the four pairs, using `y σ(y) = 1`); `GaloisCocycle.ofValues` makes it
   a cocycle `ζ` of `X`.
6. `ζ.map p` and `ξ.twist a⁻¹` have the same values: at `1` both are `1`, and at `σ`,
   `value (ξ.twist a⁻¹) σ = a · a · σ(a⁻¹) = a · a · a = a³ = p(y)`.
   `GaloisCocycle.toFun_eq_of_value_eq` turns equality of values into equality of cocycles,
   so `ξ` is cohomologous to `ζ.map p` via `a⁻¹`.

## The local correction

`IsCentralIsogeny.isTrivial_baseChange_of_cube_kernel` takes fields `K`, `L`, `M` over `F`
with `M` over `K` and `L` (`L/F` normal), `M` algebraically closed and Galois of degree `2`
over `K`, a cocycle `ζ` of `X` on `GaloisCocycle.cover F L` whose image under `p` is trivial
on the pullback `Cocycle.baseChangePullback (Spec.algebraMap F K)`, and the cube condition
for the `M`-points of the kernel.

1. `IsCentralIsogeny.nonempty_localCentralCorrection` gives a local central correction: a
   point `g ∈ X(M)` (`cochain`) and a function `c` (`correction`) from `Gal(M/K)` to the
   `M`-points of the commutative kernel of `p` with
   `j(c(σ)) = g⁻¹ A(σ) σ(g)`, where `A(σ)` is the value of `ζ` at the restriction of `σ` to
   `L`, extended to `M`, and `j` is the inclusion of the kernel points; `c` is a crossed
   homomorphism (`correction_mul`).
2. With `s` the nonidentity element of `Gal(M/K)` and `k = c(s)`: `c(1) = 1`, `k s(k) = 1`,
   so `s(k) = k⁻¹`, and `k³ = 1` by the cube condition (`j` is injective).
3. For `m = k⁻¹`, `c(σ) = m σ(m)⁻¹` for both elements `σ`: at `s` it reads
   `k = k⁻¹ k⁻¹`, which holds as `k³ = 1`.
4. Hence `A(σ) = w σ(w)⁻¹` with `w = g j(m)`, so the restricted cocycle is a coboundary over
   `M`; `GaloisCocycle.isTrivial_baseChange_of_scalarExtension` and
   `scalarExtensionPointsEquiv` transport this to the full pullback cover over `K`.

## Imports

- [`Rational.CentralNormOneLocalCorrection`](CentralNormOneLocalCorrection.md), for
  `LocalCentralCorrection` and `nonempty_localCentralCorrection`; through its imports it
  supplies `GaloisCocycle.value`, `value_mul`, `value_coboundary`, `toFun_eq_of_value_eq`
  ([`GaloisCocycle`](../GaloisCocycle.md)) and `scalarExtensionPointsEquiv`,
  `isTrivial_baseChange_of_scalarExtension`
  ([`GaloisCocycleScalarExtension`](../GaloisCocycleScalarExtension.md)).
- [`CentralIsogeny.FiniteGaloisCoefficientLift`](../CentralIsogeny/FiniteGaloisCoefficientLift.md),
  for `exists_finiteGalois_coefficient_lifts`.
- [`GaloisCocycleConstruction`](../GaloisCocycleConstruction.md), for `GaloisCocycle.ofValues`
  and `value_ofValues`.
- [`GaloisPointTower`](../GaloisPointTower.md), for relative extension, conjugation and descent
  of points in a tower of fields.
