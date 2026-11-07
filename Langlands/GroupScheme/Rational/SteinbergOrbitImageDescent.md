# Actual Steinberg products and conditional orbit-image descent

This internal helper compares two constructions on actual group schemes.
Let `k` and `K` be arbitrary fields in universe `u`, with `Algebra k K`, and
let `G` be an actual affine group scheme over `k`. Supply a split pinning `p`
of the actual base change `G_K`, an ordering `e : Fin r ≃ p.base.support`,
normalized simple-root parametrizations `x`, and simple-reflection
representatives `n`. Their meanings and normalization conditions are those of
`SplitPinning.NormalizedSimpleRootParametrizations` and
`SplitPinning.SimpleReflectionRepresentatives`; no existence is inferred.

Supply also `I : Type u` and an equivalence `d : Fin r ≃ I`. This allows the
polynomial-coordinate descent constructions, whose coordinate index has
universe `u`, to be used without restricting `u` to zero. For example, one
can take `I` to be a universe lift of `Fin r`. Throughout, `R` denotes
`MvPolynomial I K`.

`coordinateTestIso` is the actual isomorphism over `Spec K` from
`Spec(K[I])` to the standard vector scheme of dimension `r`. It is obtained
contravariantly from `MvPolynomial.renameEquiv K d`, so its coordinate map
sends the standard variable indexed by `j` to the variable indexed by `d j`.

`factorK i` evaluates the actual normalized root map indexed by
`e (d.symm i)` at the standard coordinate `d.symm i` on the vector scheme,
multiplies by the corresponding actual constant reflection representative,
and precomposes with `coordinateTestIso.hom`. Thus it is an actual `R`-point
of `G_K`. `factor i` applies the multiplicative equivalence
`Lie.affineBaseChangeEquiv` to view that point as an `R`-point of `G`.

For any list of coordinate-index blocks, `blockProduct_eq_flatten` identifies
the nested ordered product with the product along the flattened list.
The proof is induction on the block list using products of concatenated
lists. If that flattened list is exactly `List.ofFn d`, `blockProduct_eq`
identifies the resulting product with the image under
`Lie.affineBaseChangeEquiv` of
`coordinateTestIso.hom ≫ SplitPinning.steinbergProduct e x n`.
The proof distributes precomposition and the multiplicative equivalence
through ordered products and cancels `d.symm (d j) = j` in each factor.
The comparison uses no commutation premise.

`point_blockProduct_eq` uses injectivity of the base-change equivalence and
`OrbitProductImageDescent.affineBaseChangeEquiv_point` to identify the actual
point reconstructed by the tensor-coordinate construction.
`morphism_blockProduct_eq` then takes underlying scheme maps. Consequently
that constructed morphism equals the supplied actual Steinberg morphism
precomposed with the explicit coordinate isomorphism.

`imageIdeal_eq` proves equality of the full kernel ideal sheaves of the
constructed morphism and the supplied Steinberg morphism. It uses the
morphism comparison and `Scheme.Hom.ker_comp_of_isIso`: an isomorphism of
the source preserves the full scheme-theoretic image ideal. This is an
equality of ideal sheaves, not merely of reduced supports or point sets.

For `IsGalois k K`, `definingIdealDescent` constructs
`DefiningIdealDescent` for the actual full image ideal of
`SplitPinning.steinbergProduct e x n` along the actual projection `G_K → G`.
In addition to the exact flattened-order premise, it requires a supplied
action `ρ` of `Aut(K/k)` on `I`, preservation of each block as a multiset,
pairwise commutation of the actual factor points within each block, and
transport of factor `i` to factor `ρ σ i` under the combined coefficient
and variable action `PolynomialGalois.orbitAction`. It rewrites by the full
image-ideal equality and applies
`OrbitProductImageDescent.blockProductDefiningIdealDescent`.
The extension need not have finite degree. There are no perfectness or
infinitude assumptions; the rank-zero case and empty blocks are allowed.

The provenance is internal. This unit specializes the existing actual
coordinate and image descent constructions to the supplied Steinberg
product using polynomial renaming, functoriality and ordered list
multiplication. It claims no new literature-specific theorem. The original
product and the normalization interfaces are documented in
`Rational/SteinbergRootProduct`.

Consumers must still construct a compatible split pinning, normalized
parametrizations and reflection representatives, establish factor transport,
choose preserved blocks in the required order and prove their commutation.
This helper does not prove that these data exist for arbitrary quasi-split
groups. Immersion, regularity, canonical-quotient identification, intersection
geometry and rational lifting remain separate obligations. It asserts no
global section in the exceptional even type A cases. The parent quasi-split
quotient statement and its imported pairs are unchanged.
