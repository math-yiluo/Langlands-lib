# Squares of rational points lift through a central isogeny with kernel `μ₂`

Module `Langlands.GroupScheme.Rational.CentralIsogenySquareLift`, namespace
`Langlands.GroupScheme.IsCentralIsogeny`. Throughout, `f : G ⟶ H` is a central isogeny of group
schemes over a field `k` (`hf : IsCentralIsogeny f`). Points are the affine points
`G.affinePoints (CommAlgCat.of k L)` over field extensions `L` of `k`.

## Lifting after a finite Galois extension

`exists_finiteGalois_lift L a`: for a field `L ⊇ k` of characteristic zero and `a ∈ H(L)`, there
is a finite Galois extension `E/L` (with its `k`-algebra structure through `L`) and `b ∈ G(E)` with
`f(b) = relativeExtend k L E H a`.

The proof follows `exists_finiteGalois_coefficient_lifts` (module
`CentralIsogeny.FiniteGaloisCoefficientLift`), with the Galois closure taken over `L` instead of
`k`, so `L` need not be finite over `k`. The scheme fibre `Spec L ×_H G` of `a` is finite and
surjective over `Spec L`, so it has a closed point; its residue field `R` is finite over `L`
(`residueField_finiteDimensional`). `exists_finite_galois_algHom` embeds `R` in a finite Galois
extension `E/L`, and the composite `Spec E → Spec R → G` is the lift.

## Kernel points

* `target_relativeExtend`, `target_relativeConjugate`: extension of coefficients and the relative
  Galois action commute with `f`, by `affinePointsTarget_naturality`.
* `kernelPointInclusion_commute_points`: kernel points are central (`isCentral_kernelι`).
* `exists_kernelPoint_of_target_eq_one`, `target_kernelPointInclusion`,
  `kernelPointInclusion_injective'`: a point lies in the image of the kernel exactly when `f`
  kills it, and the inclusion of kernel points is injective.

From here on `e : kernel f ≅ μ₂`.

* `kernelPoint_mul_self`: every kernel point `c` satisfies `c * c = 1`, since
  `kernelRootsEquiv 2 e N` identifies the kernel points over `N` with `rootsOfUnity 2 N`.
* `kernelPoint_conjugate_eq`: kernel points are fixed by every automorphism `σ` of `N` over `k`.
  Their unit coordinate `kernelUnitMap` is a square root of `1` in the field `N`, hence `±1`, and
  `kernelUnitMap_naturality` turns the action of `σ` into `σ` applied to that coordinate.

## Squares lift

`exists_target_eq_mul_self L u` (with `G` and `H` affine and `char L = 0`): for `u ∈ H(L)` there is
`g ∈ G(L)` with `f(g) = u * u`.

Lift `u` to `b ∈ G(E)` over a finite Galois `E/L`. For `σ ∈ Gal(E/L)` the points `σ(b)` and `b` have
the same image, so `σ(b) = c b` for a kernel point `c`. Since `c` is central with `c² = 1`,
`σ(b²) = c b c b = c² b² = b²`. The point `b²` is Galois fixed, so it descends to `g ∈ G(L)`
(`relativeDescend`, `relativeExtend_descend`). Then `f(g)` and `u²` have the same extension to `E`,
and `relativeExtend_injective` gives `f(g) = u²`.

## The Kummer boundary under surjectivity

`isSquare_of_kummerImageTrivial K M hsurj a z hz hK`: let `K ⊇ k` and `M/K` be finite Galois, `G`
and `H` affine, and suppose `f : G(K) → H(K)` is surjective (`hsurj`). If the image in `G` of the
Kummer cocycle of `a ∈ Kˣ` with radical `z ∈ Mˣ`, `z² = a`, is a coboundary
(`KummerImageTrivial hf e K M a z hz`, from `Rational.NumberFieldQuaternionicSpinKernelReduction`),
then `a` is a square in `K`.

Let `b ∈ G(M)` give the coboundary. Applying `f` kills the kernel values, so `f(b)` is fixed by
`Gal(M/K)` and descends to `H(K)`. By surjectivity it is `f(g₀)` with `g₀ ∈ G(K)`, so
`b = g₀ c` for a kernel point `c ∈ G(M)`. As `g₀` and `c` are Galois fixed,
`b σ(b)⁻¹ = 1` for all `σ`. Injectivity of the kernel inclusion and of `kernelRootsEquiv` makes the
Kummer value `σ(z)/z` equal to `1`. Hence `z` is Galois fixed
(`IsGalois.mem_range_algebraMap_iff_fixed`), so `z = t` with `t ∈ K`, and `a = t²`.

## Provenance (derived)

This is the exactness of `G(K) → H(K) → H¹(K, μ₂) → H¹(K, G)` at `H¹(K, μ₂)` together with the
vanishing of the boundary on squares, written for the Library's coefficient points and Kummer
cocycles. The module is internal to the Library.
