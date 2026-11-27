# Transport of stable images through a p-adic field automorphism

`Langlands.Henniart.StableMap.IsStableImage.fieldPullback` transports a stable
image over a p-adic field `K` along a `ℚ_p`-automorphism `f`, given candidate
existence and stable existence in the rank of the original class. The Weil
pullback uses `φ = extensionWeilEquiv K K f.symm` and the supercuspidal pullback
uses `f`.

The absolute Galois map `α` belonging to `φ` is an isomorphism. Its kernel is
trivial by injectivity of `extensionGaloisMap`, and the range has index one by
`extensionGaloisMap_range_index` and `extensionDegree_algEquiv`. The projection
of `φ w` is `α` applied to the projection of `w`. A basis class factors through
`q` exactly when its pullback factors through `q ∘ α`: the same quotient
representation supplies both factorizations, and restriction along `φ⁻¹`
recovers the original Weil class. Reindexing supports gives the corresponding
lattice fact. With `LatticeMap.henniartProperties_fieldPullback`, it shows that
a candidate at `q` pulls back to a candidate at `q ∘ α`.

The conjugate unitary class thus factors through a finite quotient and has a
stable image by stable existence in the given rank. Write `q` for a quotient
witnessing the original stable image and `r` for one witnessing the stable
image of the pullback. Candidate existence supplies a map at the product
quotient `(q, r ∘ α⁻¹)`. Its first projection is `q`, so the map evaluates on
the original class to its stable image. After pullback the second projection
of the transported quotient is `r`. The transported map therefore evaluates
on the pulled-back class to its stable image over `r`. Computing that value by
`LatticeMap.fieldPullback_apply` identifies it with the pullback of the original
stable image. Both uses of stability along a projection are applications of
`IsStableImage.exists_quotient`.

The argument uses the definition of stability derived from Henniart (2000),
§§4.1–4.2, pp. 452–453, literature ID `henniart-2000-simple-proof`, retained PDF
SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
