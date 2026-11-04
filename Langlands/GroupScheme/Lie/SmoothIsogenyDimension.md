# Lie dimensions under smooth group-scheme isogenies

This internal supporting construction compares the actual dual-number Lie
spaces of smooth affine group schemes over an arbitrary field `k : Type u`.
`finrank_kernel_eq_of_isogeny q hq` proves equality of their `k`-finranks for
the existing finite-flat-surjective predicate `IsIsogeny q`. Centrality is
unnecessary. Neither the kernel nor the isogeny is assumed smooth or separable;
no perfection or characteristic restriction is imposed on the field.

The more general `finrank_kernel_eq_of_flat_locallyQuasiFinite` only requires
the underlying homomorphism to be flat and locally quasi-finite. In particular,
surjectivity is not used in the dimension comparison. Smoothness is required
for both ambient groups, and affineness identifies their published Lie-kernel
modules with identity tangent modules. Smoothness supplies local finite type,
so these modules are finite-dimensional.

The implemented proof has three steps. First,
`finrank_kernel_cast_eq_ringKrullDim` composes the published
`Lie.finrank_kernel_eq_cotangent` with
`AlgebraicGeometry.Smooth.isRegularLocalRing_stalk` and
`IsRegularLocalRing.iff_finrank_cotangentSpace`. Thus the natural-number
finrank, cast into `WithBot ℕ∞`, equals the Krull dimension of the actual
identity stalk. The regularity input is imported from the Library's
universe-general port of the Anthropic FLT smooth-stalk theorem; this file
uses its published interface without modifying or reproducing its proof.

Second, the companion module `FlatQuasiFiniteStalkDimension` proves equality
of the Krull dimensions of stalks across flat locally quasi-finite scheme
morphisms. Its proof uses flat going down and quasi-finite incomparability
on prime spectra, then applies equality of prime heights to local maximal
ideals. This companion module is an internal derivation from Mathlib APIs;
its paired Markdown gives the algebraic argument and geometric adapter.

Third, the group-homomorphism law `MonObj.one_comp` identifies the image of
the source identity with the target identity. The stalk-dimension equality
therefore compares the two identity stalks. The two regularity comparisons
and injectivity of the casts yield equality of the natural-number Lie
finranks. Finiteness of an isogeny implies local quasi-finiteness; its
flatness then gives the advertised isogeny corollary.

`kernelLinearEquivOfFlatLocallyQuasiFinite` packages these equal finite
dimensions as an abstract `k`-linear equivalence, using
`LinearEquiv.ofFinrankEq`. This chosen equivalence is not asserted to be the
differential of the given homomorphism. Inseparable isogenies can have a
noninjective or nonsurjective differential even when their ambient Lie
spaces have equal dimension. The central-isogeny consumer uses the finrank
equality together with separate nonzero-weight injectivity and zero-weight
dimension comparisons; none of those remaining inputs follows from this
construction alone.
