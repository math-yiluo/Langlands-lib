# Conditional effectivity for rigidified classes

This internal construction fixes an arbitrary morphism `f : X → S` with a
section, a slice morphism `h : U → T`, and a relative rigidified line bundle
`L` over `U`. The effective-descent result assumes that `h.left` is affine,
flat and surjective, that relative rigidified isomorphisms are unique over
every test scheme, and that the ordinary line-bundle effective-descent
proposition `LineBundleDescentEffectiveStatement` holds. It also assumes
compatibility: the two relative pullbacks of `L` are isomorphic for every
pair of slice maps to `U` whose composites with `h` agree.

`ClassDescent.theta_precomp` rewrites the previously constructed common-point
comparisons using their arbitrary-precomposition identity. Unfolding module
transport yields precisely the naturality formula in the effective-descent
interface. Together with the existing cocycle law, this permits
`ClassDescent.exists_carrier` to apply that interface to the actual map of
relative total spaces. Affineness, flatness and surjectivity transfer through
the Cartesian relative projection square. The result is an ordinary line
bundle `M` over the total space over `T` with an isomorphism `p* M ≅ L` of
ordinary carriers, where `p` is the relative-space map of `h`.

The remaining construction works for any slice morphism `h` and any such
carrier isomorphism, without flatness or descent assumptions. Write `A` for
the restriction of `M` to the relative section over `T`. The original local
rigidification and the section-pullback comparison give
`carrierRestrictionIso : h* A ≅ O_U`. Choose a line-bundle inverse `N` of
`A`, supplied by the proved dual evaluation result, with evaluation
`A ⊗ N ≅ O_T`. Pulling back this evaluation and using `h* A ≅ O_U` gives
`inverseRestrictionIso : h* N ≅ O_U`; no global triviality of `A` is inferred.

Normalize `M` to `M ⊗ π_T* N` using that evaluation and the split relative
section. `normalizedCarrierIso` uses the tensor-pullback comparison, the
relative projection square, and the previous trivialization to identify
its pullback with the ordinary carrier of `L`. The proved carrier-isomorphism
adjustment for a split section turns this into an actual rigidified
isomorphism. Thus `exists_rigidified_of_carrier` produces a relative
rigidified line bundle over `T` whose pullback is isomorphic to `L`.
`exists_rigidified_of_descent` combines this normalization with the ordinary
carrier-descent result under the explicit hypotheses above.

This is a derived intermediate result from the Library's actual pullbacks,
rigidifications, tensor comparisons, dual evaluation and normalization. It
does not prove the ordinary effective-descent proposition, discharge the
uniqueness hypothesis, or prove the full rigidified fppf comparison.
