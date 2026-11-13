# Common residue coordinates for elementary Artinian ideals

Let `φ : R →+* S` be a surjective map of commutative Artinian local rings such
that `maximalIdeal R * ker φ = ⊥`, and put `K = ResidueField S`. The ideal sheaf
`ideal φ X` is the actual kernel sheaf of the closed-fibre structure map for a
scheme `X` over `Spec R`. The module `residueModule φ X` is the pushed-forward
structure module of its actual residue fibre.

For an algebra presentation of the ring map and a fixed finite `K`-basis `b` of
its actual kernel, `idealResidueIso` orients the isomorphism constructed in
`ElementaryArtinianIdealResidueProductIso` from the ideal sheaf to a product of
copies of `residueModule`. It requires flatness of the structure morphism.

`idealResidueIso_square` proves the coordinate square for any map `f : Y → X`
and any ideal coefficient map compatible with the actual ideal inclusions.
The proof applies `idealCoordinateCoefficient_compatible` using the common
coefficients `(b j).val`. Its two inverse formulas are the affine and all-open
formulas from `OriginalResidueProduct`, and affine residue-section lifting
follows from surjectivity of the original ring map. Uniqueness of compatible
ideal maps then identifies every compatible map with the transported map,
whose coordinate square uses precisely `residueCoefficient φ f`.

`exists_idealResidueProductIso` allows a bare ring homomorphism `φ` and chooses
one finite index type and one family of ideal-to-product isomorphisms for all
flat schemes over `Spec R`. Their coordinate squares hold simultaneously for
all morphisms and all compatible ideal maps. Internally the proof installs
`φ.toAlgebra`, equips the unchanged kernel with its descended residue-field
module from `ElementaryKernel.residueModule`, and uses
`ElementaryKernel.finiteDimensional` to choose a finite basis. The index type
lies in the same universe as the rings. Zero kernels are included.

This is internal infrastructure derived from the actual kernel tensor
comparison, the finite-basis coordinate construction, and the generic ideal
coordinate square criterion. It proves sheaf-level naturality. It makes no
cohomological comparison or injectivity claim and requires no properness.
