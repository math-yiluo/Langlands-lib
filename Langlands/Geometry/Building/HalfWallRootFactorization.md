# Half-root factorization at a chamber-simple wall

This module derives a product inclusion for the possible half-direction of a
chamber-simple affine root. It uses the actual root subgroups and valuations of
`KPApartmentData`, with no rank-one factorization or ordered-product premise.

The context is an arbitrary universe `u`, a field `k : Type u`, an affine group
scheme `G`, a commutative group scheme `S`, a monomorphic inclusion
`i : S.toGrp ⟶ G`, a function `ω : kˣ → ℝ`, and actual apartment data
`D : KPApartmentData i ω`. Every subgroup and product below is interpreted in
`rationalPoints G`.

The general supporting theorem
`affineRootGroup_subset_mul_double_of_not_mem_affineRoots` assumes a relative
root `b`, that `2b` is also a relative root, an affine functional `η` with
linear part `rootForm i b`, and `η ∉ D.affineRoots`. It proves

`U_η ⊆ U_{η+} · U_{2η}`,

where the first two groups use direction `b` and the last uses direction `2b`.
Here `U_η` and `U_{η+}` mean the existing `affineRootGroup` and
`affineRootGroupPlus`. The conclusion specifies the doubled factor's depth;
it does not merely put that factor in the whole doubled root subgroup.

For the wall results, the module assumes the AS4 implication

`∀ η ∈ D.extendedAffineRoots, η ∈ D.affineRoots ∨ 2 • η ∈ D.affineRoots`,

and `ψ ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C` for a subset `C`
of the apartment. This simple-root membership includes positivity,
indivisibility of the affine root, and the chamber-wall condition. Given
`c > 0` and a relative root `b` with `(c • ψ).linear = rootForm i b`, it proves

`rootFixer b C = affineRootGroup b (c • ψ)`.

Given also a coroot `v` of `ψ` and the corresponding actual affine reflection
`s = affineReflection ψ hv.1`, it proves

`rootFixer b (s '' C) = affineRootGroupPlus b (c • ψ)`.

Both equalities keep the same direction `b`. No assertion that `b` itself is
indivisible is required.

The final inclusion assumes that `b` and `2b` are relative roots and
`ψ.linear = rootForm i ⟨2b, h2b⟩`. Under AS4, simple-root membership, and the
chosen coroot it proves

`rootFixer b C ⊆ rootFixer b (s '' C) · affineRootGroup (2b) ψ`.

The entry `halfWallRootGroupInclusion` maps the subgroup `rootFixer b C` into
the subtype of this product set. It preserves the ambient rational point.
The product set is not asserted to be a subgroup, and this map is not claimed
to be a multiplicative equivalence or a unique factorization.

The proof of the general inclusion unfolds the existing definition of
`affineRoots`: failure of affine-root membership forces every element of
`U_η` to be a strict factor followed by an element of `U_{2b}(k)`. Both the
original element and its strict factor lie in `U_η`, so subgroup closure puts
the remaining factor there as well. At any apartment point, valuation axiom
V4 doubles its `b` valuation. The depth inequality therefore puts that
remaining factor in `U_{2η}`. The equality of linear parts for the doubled
functional follows from `rootForm_nsmul`.

For the scaled wall equalities, the existing simple-wall geometry supplies a
chamber point and a wall point in its facet closure. The functional `c • ψ`
vanishes at the wall point and is positive on the chamber. The generic
closure-point comparison from `ChamberWallRootGroups` gives the first
equality. The coroot reflection fixes the wall point, transports the
facet-closure condition, and negates `ψ`; thus `c • ψ` is negative in the
reflected chamber. The strict version of the same comparison gives the
second equality.

Finally, affine indivisibility of `ψ` states that `(1/2) • ψ` is not an affine
root. Its derivative is `b` by `rootForm_nsmul`. Apply the general inclusion to
this half functional and rewrite its two `b`-direction groups with the scaled
wall equalities. Its double is `ψ`, giving the final inclusion. The entry map
just packages that inclusion as a function of subtypes.

This is derived content from the existing Library definitions, V4, wall
geometry, and the paired `ChamberWallRootGroups` results. It makes no new
external-source assertion. It does not prove the complete chamber-simple
parahoric factorization, the proportional-root classification and ordered
product assembly needed for it, or `AffineIwahoriTitsStatement`. Those
obligations and the apartment-only closing target remain open.
