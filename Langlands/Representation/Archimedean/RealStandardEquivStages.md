# Induction in stages of actual real standard equivalences

This internal derived module extends an actual bijective standard intertwiner between middle lists of equal rank through arbitrary surrounding blocks. The construction is the existing induced map defined from normalized compact slices and principal-series extension.

`surjective_ind` proves that a surjective compact-equivariant middle map induces a surjective ambient map. It specializes the existing one-step range theorem `exists_sub_mem_range_ind` to the zero subspace and the whole middle target. The remainder has zero compact slices, so `eq_zero_of_sliceK` makes it zero. Together with the published injectivity theorem this proves `standardInd_bijective` for an actual bijective compact and Lie intertwiner.

`standardEquivInd` packages that induced map as a linear equivalence. Both its forward map and its inverse intertwine the compact action and the real Lie derivatives exactly. The inverse intertwining follows by applying the injective forward equivalence to the desired equalities. The final two lemmas give the slice identities for both directions; the inverse identity follows by applying the original middle equivalence to the forward slice formula.

The surrounding lists may contain characters or induction blocks. The original ambient Fourier conditions remain part of the actual standard module and are handled by the published induction construction. No extra Fourier constraint crossing a middle boundary is asserted to be preserved.

The provenance is internal: this is a direct consequence of the Library's actual normalized slices, induced maps, one-step range theorem and injective-intertwiner extension. It uses no external classification assertion.

`RealStandardEquivStagesStatement` packages the existence of this actual ambient equivalence, its exact compact and Lie intertwining in both directions, and both slice formulas, for all ranks, surrounding lists and middle equivalences satisfying the displayed rank and intertwining assumptions. `realStandardEquivStages` proves that proposition using the constructed equivalence. This supporting result does not assert preservation of an additional Fourier condition crossing the middle boundary or the two-induced-block filtration.
