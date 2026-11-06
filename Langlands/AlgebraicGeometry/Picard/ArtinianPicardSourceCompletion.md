# Completeness of the actual Picard source quotient

This internal specialization proves completeness of the actual source
quotient constructed in `ArtinianPicardSourceTower`.

Keep its arbitrary common universe `u`, commutative `k`, field `K` with the
specified `k`-algebra structure, Noetherian local `k`-algebra `R`, surjective
augmentation `ε`, flat proper actual scheme morphism `f`, residue-fibre
line bundle `M`, and initial actual pointed source stage `s₀`.
Assume additionally that `R` is complete for its actual maximal ideal.

The instance `limitRing_isAdicComplete` proves that
`ArtinianPicardSourceTower.limitRing ε hε f M s₀` is complete for its own
actual maximal ideal. This ring is the unchanged actual quotient
`R/J_∞`, with `J_∞` the intersection of the actual stage equation ideals.
The existing tower module supplies its nontrivial, local and Noetherian
ring instances and its specified descended residue augmentation.

The proof applies
`Langlands.Algebra.AdicCompleteSurjection.complete_of_surjective` to the
actual quotient map `Ideal.Quotient.mk J_∞` and its standard surjectivity.
Thus it uses the original complete source and actual quotient; it does
not replace the ring by its completion or transport the stage families
to different tests.

The provenance is internal specialization of that completeness descent.
The exact comparison between the original tower ideals and powers of the
quotient maximal ideal, inverse-limit identification, construction of an
actual adic formal line-bundle system, formal versality and the exact
Picard-stack atlas remain open.
