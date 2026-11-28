# The spinor norm of a quaternionic line similitude

Module `Langlands.GroupScheme.Rational.QuaternionicSpinLineSimilitudeBoundary`, namespace
`Langlands.GroupScheme`. The auxiliary results live in the namespace
`Langlands.GroupScheme.QuaternionicLineSimilitude`.

## The statement proved

The module proves `QuaternionicSpinLineSimilitudeBoundaryStatement` (module
`Rational/NumberFieldQuaternionicSpinKernelReduction`) at every universe, as the theorem
`quaternionicSpinLineSimilitudeBoundary`.

Let `F` be a field of characteristic zero, `D` a central division `F`-algebra with
`dim_F D = 4`, `σ` a first-kind involution with three-dimensional symmetric subspace, `n ≥ 3`
and `q : σ.QuadraticForms (Fin n)` nondegenerate. Let `p : G ⟶ σ.normOneIsometryGroup q` be
a central isogeny from a simply connected `G`, and `e : kernel p ≅ μ₂`. Let `x ∈ Dⁿ` with
`c = h(x, x) ≠ 0`, and `d ∈ D` with `d c σ(d) = N c` where `N = Nrd(d) ∈ Fˣ`. Then for every
finite Galois extension `M/F` and every `z ∈ Mˣ` with `z² = N`, `KummerImageTrivial hp e F M
N z hz` holds. That is, there is `b ∈ G(M)` with `κ(s(z)/z) = b · s(b)⁻¹` for all
`s ∈ Gal(M/F)`, where `κ` is the kernel point attached to a square root of unity through
`e`.

Classically: `d` is a similitude of the rank-one hermitian space `D x` with multiplier `N`.
The element `t = d²/N` satisfies `t c σ(t) = c` and `Nrd(t) = 1`, so the isometry sending
`a x` to `a t x` and fixing the orthogonal complement of `D x` lies in `SU(F)`. Its spinor
norm, the image under the connecting map `SU(F) → H¹(F, μ₂)` of `1 → μ₂ → G → SU → 1`, is the
class `[N]`. By exactness, the image of `[N]` under the map `H¹(F, μ₂) → H¹(F, G)` induced by
the kernel inclusion is trivial. Through `e`, that image is the class of the cocycle
`s ↦ κ(s(z)/z)`. When `d` is not central, the proof lifts the rotation with parameter `d/z`
after extending `M` and squares the lift. The square lifts the rational rotation with
parameter `d²/N` and descends to `M` to trivialize the cocycle.

## Auxiliary results

**Quaternions** (`D` of dimension `4`).
* `purePart F d = d - Trd(d)/2`.
* `purePart_mul_self`: `w² = -Nrd(w)` for `w = purePart F d`, from the reduced
  characteristic polynomial (`CentralDivision.sq_sub_reducedTrace_add_reducedNorm`) and
  `Trd(w) = 0`.
* `purePart_commute`: `w` commutes with `d`.
* `purePart_mul_mul_map`: if `d c σ(d) = N c` with `Nrd(d) = N ≠ 0`, then
  `w c σ(w) = Nrd(w) c`. From `d² - Trd(d) d + N = 0` one gets
  `c σ(d) = (Trd(d) - d) c`, hence `c σ(w) = -w c` and `w c σ(w) = -w² c = Nrd(w) c`.

**Scaled units.** For a field `K` over `F`, `r ∈ Kˣ` and `y ∈ Dˣ`, `scaledUnit F K r y` is the
unit `r ⊗ y` of `K ⊗ D`, with `coe_scaledUnit`, `scaledUnit_mul`, `scaledUnit_comm` (for
commuting `y, y'`), `scaledUnit_algebraMap`, `scaledUnit_neg` and the naturality
`map_scaledUnit`. `mem_lineTorus_scaledUnit`: if `y c σ(y) = m c`, `Nrd(y) = m` and
`r² m = 1`, then `r ⊗ y` lies in the line torus `lineTorus σ q x K` (module
`Quaternionic/LineRotation`).

**Kernel points.** `negOneRoot K` is `-1 ∈ μ₂(K)`, and `kappa hp e K ζ` is the point of `G(K)`
attached to `ζ ∈ μ₂(K)` (`kernelPointInclusion` of `(kernelRootsEquiv 2 e K).symm ζ`).
* `kappa_commute`, `kappa_mul_self`, `kappa_one`, `project_kappa`: kernel points are
  central, of order dividing two, `κ(1) = 1`, and they project to `1`.
* `eq_one_or_eq_kappa`: a point of `G(K)` projecting to `1` is `1` or `κ(-1)`.
* `kappa_naturality`: `κ(-1)` is compatible with coefficient maps (from
  `kernelUnitMap_naturality`).
* `mul_self_eq_of_project_eq`: if `p(a) = p(b)` then `a² = b²`, since `a = b k` with `k`
  central of order dividing two.

**The negation of the line.** `neg_one_mem_lineTorus` and `negOneTorus`: `-1` lies in the line
torus. `lineRotationHom_negOne_val`: its rotation has tensor unit `1 ⊗ lineReflection σ q x`.

**Group theory.** `commute_sq_of_commutator`: if the commutator `k = g h g⁻¹ h⁻¹` is central with
`k² = 1`, then `g²` commutes with `h`.

**Lifts of the negation.** `lift_mul_self_eq_kappa`: if `y ∈ G(E)` projects to the negation of
the line, then `y² = κ(-1)`. `y²` projects to `1`, so it is `1` or `κ(-1)`. The first case
is excluded by `lineReflection_lift_mul_self_ne_one` (module
`Rational/QuaternionicSpinLineReflection`) after extending to an algebraic closure of `E`,
using `lineRotationHom_naturality`.

**Commuting lifts.** `mul_self_eq_kappa_mul_of_lifts`: let `t₀, t₁` be commuting elements of the
line torus over `E` with `t₁² = -1`. Let `h, g ∈ G(E)` be lifts of their rotations, and `a`
a lift of the rotation of `-t₀`. Then `a² = κ(-1) h²`. Indeed `y = g²` lifts the negation, so
`y² = κ(-1)`. The commutator of `g` and `h` projects to `1`, so `y` commutes with `h`
(`commute_sq_of_commutator`). Then `a² = (y h)² = y² h²` by `mul_self_eq_of_project_eq`.
`affinePointsTarget_affinePointMap` (namespace `Langlands.GroupScheme`) records that
projection commutes with coefficient maps.

**Descent.** `rootValue_eq_one`, `rootValue_eq_negOneRoot` and `eq_or_eq_neg_of_sq` compute the
Kummer values: `s(z) = ±z`, with value `±1`. `kummerImageTrivial_of_forall_fixed`: if every
automorphism fixes `z`, take `b = 1`. `kummerImageTrivial_of_twisted`: let `E ⊇ M` be finite
Galois over `F`, and `b' ∈ G(E)` with `s(b') = b'` when `s(z) = z` and `s(b') = κ(-1) b'`
when `s(z) = -z`, for all `s ∈ Gal(E/F)`. Then the Kummer image is a coboundary on
`Spec M → Spec F`. The point `b'` is fixed by `Gal(E/M)`, so it descends to `b ∈ G(M)`
(`GaloisPoint.relativeFixedEquiv`). For `s ∈ Gal(M/F)`, compare `s(b)` with `b` or
`κ(-1) b` after extension to `E`, through `s.liftNormal E`
(`GaloisPoint.relativeExtend_conjugate_lift`, `GaloisPoint.relativeExtend_injective`,
`kappa_naturality`). Finally `b · (κ b)⁻¹ = κ⁻¹ = κ`.

`exists_sqrt_extension`: a finite extension `L ⊇ M` (a splitting field of `X² - β` over `M`)
contains a square root of a given `β ∈ F`.

## Proof of `quaternionicSpinLineSimilitudeBoundary`

`G` is affine because it is semisimple (`IsConnectedReductive.isAffineHom`). Let
`w = purePart F d`.

* If `w = 0`, then `d = a ∈ F`, `N = Nrd(a) = a²` (`CentralSimple.reducedNorm_scalar`), so
  `z = ±a` is fixed by every automorphism, and `kummerImageTrivial_of_forall_fixed`
  applies.
* Otherwise `w` is a unit with `w² = -β`, `β = Nrd(w) ≠ 0`, and `w c σ(w) = β c`
  (`purePart_mul_mul_map`). Take `L ⊇ M` with `l² = β` (`exists_sqrt_extension`). Over `L`
  set `t₀ = z⁻¹ ⊗ d` and `t₁ = l⁻¹ ⊗ w`, both in the line torus
  (`mem_lineTorus_scaledUnit` with multipliers `N` and `β`). By
  `IsCentralIsogeny.exists_finiteGalois_coefficient_lifts`, their two rotations lift to
  `h, g ∈ G(E)` over a finite Galois `E ⊇ L`. Make `E` an `M`-algebra through `L`, and push
  `t₀, t₁` to `E` by `lineTorusMap` (`lineRotationHom_naturality`). There they commute
  (`scaledUnit_comm`, `purePart_commute`) and `t₁² = l⁻² ⊗ w² = -1`.

  For `s ∈ Gal(E/F)`, the conjugate `s(h)` lifts the rotation of `s(t₀) = s(z)⁻¹ ⊗ d`
  (`map_scaledUnit`). If `s(z) = z` this is `t₀`, so `s(h)² = h²`
  (`mul_self_eq_of_project_eq`). If `s(z) = -z` it is `-t₀` (`scaledUnit_neg`), so
  `s(h)² = κ(-1) h²` (`mul_self_eq_kappa_mul_of_lifts`). Hence `b' = h²` satisfies the
  hypotheses of `kummerImageTrivial_of_twisted`, which concludes.

## Provenance

The statement is the classical identification of the connecting map of the spin extension
with the spinor norm, here for line similitudes of quaternionic hermitian forms. The proof is
derived from the Library results named above. Its central input is the computation of the
square of a lift of the line negation in `lift_mul_self_eq_kappa`. The pure part `w` of `d`
supplies the rotation parameter `t₁`, which commutes with `t₀` and satisfies `t₁² = -1`.
