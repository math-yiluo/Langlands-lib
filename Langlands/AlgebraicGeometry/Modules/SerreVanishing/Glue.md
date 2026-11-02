# Gluing lifts of twisted sections from module charts

Internal helper module for the proof of `TwistKillingStatement` (module
`SerreVanishing.Iterate`). It proves the lifting step of the base case of that proof: a
global section of a quotient lifts to the twisted source after enough multiplications by
the section. It works
for an arbitrary system of modules `N 0 ⟶ N 1 ⟶ N 2 ⟶ ⋯` with transition maps
`μ m : N m ⟶ N (m + 1)`. `powMul N μ n k : N n ⟶ N (n + k)` is the Library's `k`-fold
composite (`LineBundleSectionClearingProof`).

## Systems

- `powMul_app_family`: if a family of sections `p m ∈ Γ(N m, W)` satisfies
  `μ m (p m) = p (m + 1)`, then `powMul N μ n k (p n) = p (n + k)`.
- `powMul_comp_hom`, `powMul_hom_app`: a family of morphisms `π m : N m ⟶ N' m` that
  commutes with the transition maps also commutes with `powMul`. The first is stated for
  morphisms, the second for sections.

## Module charts

`ModChart N μ R T c`, for a reference module `R`, an open `T` and a function
`c ∈ Γ(X, T)`, has the following fields.

- `E m W hW : Γ(N m, W) → Γ(R, W)` for every `m` and every open `W ≤ T`.
- `injective`, `surjective`: each `E m W hW` is a bijection.
- `res`: `E` commutes with restriction.
- `smul`: `E` is linear over `Γ(X, W)`.
- `mul`: `E (m + 1) W hW (μ m d) = c|_W • E m W hW d`.

So over opens inside `T`, all the `N m` look like `R`, and every transition map looks like
multiplication by `c`.

Lemmas about one chart `C`:

- `E_zero`: `E` sends `0` to `0`.
- `E_powMul`: `E (n + k) (powMul N μ n k d) = (c|_W)^k • E n d`.
- `E_family`: for a family `p` as in `powMul_app_family` over some `W₀ ⊇ W`,
  `E m (p m|_W) = (c|_W)^m • E 0 (p 0|_W)`.
- `exists_powMul_eq_zero`: suppose `W ≤ T` and `R` has the localization property
  `IsLocalizingAt R W` of the Library (module `QuasicoherentLocal.Basic`). Then a section
  `d ∈ Γ(N n, W)` that vanishes on the basic open of `c|_W` satisfies
  `powMul N μ n k d = 0` for some `k`.

`exists_local_lift` treats two charts `C` of `(N, μ)` with reference `R` and `C'` of
`(N', μ')` with reference `R'`, over the same `T` and `c`. It assumes the following.

- Morphisms `π m : N m ⟶ N' m` and `ρ : R ⟶ R'` with `C'.E (π m d) = ρ (C.E d)`.
- An open `V ≤ T` over which `R` and `R'` are localizing and `ρ` is surjective on sections.
- An open `U` with `X.basicOpen c = T ⊓ U`.
- Families `p m ∈ Γ(N' m, X)` and `q m ∈ Γ(N m, U)` compatible with `μ'`, `μ`, such that
  `π m (q m) = p m|_U`.

The conclusion is that there are `n` and `b ∈ Γ(N n, V)` with `π n b = p n|_V` and
`b|_{V ⊓ U} = q n|_{V ⊓ U}`.

## Global lifting

`exists_global_lift` (for `X` quasi-compact) uses the data of `exists_local_lift`, but
now `π` is a morphism of systems (`π m ≫ μ' m = μ m ≫ π (m + 1)`). Its hypotheses are:

- every point lies in an open `T` carrying compatible charts `C`, `C'` with a function `c`
  satisfying `X.basicOpen c = T ⊓ U`;
- `R` and `R'` are localizing over every affine open;
- `ρ` is surjective on sections over every affine open;
- the intersection of two affine opens is affine.

The conclusion is that for some `m` there is a global section `a ∈ Γ(N m, X)` with
`π m a = p m`.

## Proofs

`exists_local_lift`: write `h = c|_V`, so that `D(h) = V ⊓ U`. Choose
`y ∈ Γ(R, V)` with `ρ y = C'.E (p 0|_V)`. The difference between `y|_{D(h)}` and the
coordinate `C.E (q 0|_{D(h)})` maps to zero under `ρ`. By the localization property of `R`
over `V`, `h^{n₁}` times this difference extends to a section `t` over `V`. By that of `R'`,
`h^{n₂} • ρ t = 0`. The lift `b` is the section with coordinates
`h^{n₁+n₂} • y - h^{n₂} • t`. Both required identities are then checked in coordinates,
using `E_family` and injectivity of the charts.

`exists_global_lift`: cover `X` by finitely many affine opens `V i`, each inside a chart
open. Step 1: local lifts `b i` with a common exponent `e`, using `exists_local_lift` and
`powMul_app_family` to raise exponents. Step 2: on each `V i ⊓ V j` the difference
`b i - b j` vanishes on the basic open of `c_i`, because both agree with `q e` there. The
overlap is affine, so `exists_powMul_eq_zero` kills the difference after `k` further
multiplications, with one `k` for all pairs. Step 3: the sections `powMul (b i)` glue to
`a ∈ Γ(N (e + k), X)`. The equality `π a = p (e + k)` holds locally, hence globally.

## Provenance

Derived for this proof. It is the module version of the Library's
`exists_global_of_charts` (`LineBundleSectionClearingProof`), which treats the powers of
one line bundle. The argument is the proof of part (2) of Stacks Project, Lemma 28.18.2
(tag [01PW](https://stacks.math.columbia.edu/tag/01PW)). For `X` quasi-compact and
quasi-separated, a section over the locus `X_s` extends to a global section after
multiplication by a power of `s`. The proof makes local extensions on a finite cover
trivializing the line bundle, then kills their differences on the overlaps. Here the
same steps are carried out for lifting through a surjection, which is what the degree-one
case of Lemma 30.17.4 (tag [01XR](https://stacks.math.columbia.edu/tag/01XR)) needs in
the dimension-shifting proof of module `SerreVanishing.Killing`. Separatedness enters only
through the hypothesis that intersections of affine opens are affine.
