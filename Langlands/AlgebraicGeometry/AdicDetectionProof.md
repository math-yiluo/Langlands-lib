# Adic detection of an immersed subscheme of a finite scheme

`Langlands.AlgebraicGeometry.AdicDetection.adicImmersionIsIso.{u}` proves
exactly `Langlands.AlgebraicGeometry.AdicDetection.AdicImmersionIsIsoStatement.{u}`.
For a local Noetherian commutative ring `A`, a finite morphism
`p : X ⟶ Spec A`, and an immersion `i : Z ⟶ X`, the hypothesis is that
the base change of `i` along every canonical map
`Spec(A / m^(n+1)) ⟶ Spec A` is an isomorphism. The conclusion is
`IsIso i`. There are no additional geometric assumptions on `i` or `Z`.
All schemes, rings, and maps retain the arbitrary universe parameter `u`.

The implemented proof follows SGA 3, Exposé IX, Lemme 5.0.
The helpers are derived steps of that argument and use Mathlib's actual
scheme morphisms, spectra, pullbacks, finite morphisms, immersions,
affine comparison, and adic separation theorem.

First, `baseChange_fst` identifies the first projection of the underlying
`Over.pullback` morphism. `factors_of_baseChange_isIso` uses its inverse:
if `t : W ⟶ X` and `s : W ⟶ T` agree over the base, and the base change
along `r : T ⟶ S` is invertible, then `t` factors through `i`.
`range_fst_subset_of_baseChange_isIso` gives the corresponding inclusion
of point-set images.

Second, `closedPoint_mem_range_adicBase_zero` applies the spectrum image
formula for a surjective ring homomorphism to `A ⟶ A/m`.
In `open_eq_top_of_closed_fiber_subset`, the image under the finite
morphism `p` of the complement of an open `U` is closed. Every point of
the spectrum of a local ring specializes to its closed point. Thus a
nonempty complement would meet the closed fibre, contradicting the
assumption that the closed fibre lies in `U`.
`isClosedImmersion_of_closed_fiber` applies this to the open
`i.coborderRange` in Mathlib's closed-then-open factorization of the
immersion. The zeroth adic base-change hypothesis puts the closed fibre
in the image of `i`, so this open is the whole scheme and `i` is closed.
This step does not need Noetherianity.

Third, `finite_algebra_eq_zero` applies Mathlib's
`IsHausdorff (IsLocalRing.maximalIdeal A) B` instance for a finite
`A`-module over a local Noetherian ring. Membership in the ideals
`m^(n+1) B` is translated by `Ideal.smul_top_eq_map` into the
module-theoretic condition used by `IsHausdorff.haus`; the zeroth power
imposes no restriction.

Fourth, `appTop_injective_of_adic_baseChange` writes the finite affine
scheme as `Spec B`, with `B = Γ(X, ⊤)`, using `X.isoSpec`. The structure
map is the spectrum of a finite ring homomorphism `a : A →+* B`.
For each `n`, set `J = (m^(n+1)).map a`. The canonical map
`Spec(B/J) ⟶ X` has a map to `Spec(A/m^(n+1))` given by
`Ideal.quotientMap`; their compatibility over `Spec A` is checked on the
canonical ring maps. The factorization helper makes `Spec(B/J) ⟶ X`
factor through `i`.
`isoSpec_inv_appTop` identifies the global-sections comparison, and
`quotient_eq_zero_of_factors` shows that any `b` killed by `i.appTop`
vanishes in `B/J`. Finite-module Krull intersection therefore makes
`b` zero, proving injectivity of `i.appTop`. This injectivity helper
does not itself assume that `i` is an immersion.

The final theorem combines closedness of `i`, affineness of `X`, and
injectivity on global sections through Mathlib's
`IsClosedImmersion.isIso_of_injective_of_isAffine`.

Source: A. Grothendieck, *SGA 3*, Exposé IX, Lemme 5.0, Gille–Polo
recomposed edition, provisional version of 8 November 2009, recomposed
p.48 (PDF p.18, original margin p.58), registered as
`sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The helper declarations are internal derivations of its proof, rather
than separately attributed assertions of the source.
