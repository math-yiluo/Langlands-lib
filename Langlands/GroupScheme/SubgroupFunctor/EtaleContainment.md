# Subgroup containment on the open image of an etale map

This internal module supplies the descent step for the open-neighbourhood
argument in `RelativeParabolicLieContainmentStatement`. It does not prove that
statement.

For a monomorphic subgroup inclusion `i : P ⟶ G`, containment of an arbitrary
subgroup functor in `range i` descends along a surjective flat base map locally
of finite presentation (`le_range_of_fppf_baseChange_le`). This is the fppf
variant of the published `le_range_of_baseChange_le`: replace its
quasi-compactness hypothesis with local finite presentation and use Mathlib's
effective epimorphism instance for surjective flat maps locally of finite
presentation. The rest of the proof is the same pullback-on-tests argument,
using `mem_range_of_comp_mem_range`.

`range_le_comp_baseChange_iff` identifies containment after direct base change
along `c ≫ b` with containment after successive base changes along `b` and `c`.
It uses the published `Descent.pullbackComparison` isomorphisms and their
naturality, together with preservation and reflection of range containment by
an ambient isomorphism and invariance of ranges under source isomorphisms.

Let `b : U ⟶ S` be etale. The existing
`TorusIsomorphismLocus.etaleImage b` is the open subset with underlying set
`Set.range b`. The theorem `range_le_etaleImage` says that containment of
`range j_U` in `range i_U` descends to this open subset of `S`. Its only
subgroup hypothesis is that `i` is a monomorphism of schemes over `S`.
The proof factors `b` through its open image; the factor is etale and
surjective. The fppf reflection theorem, after transport across the
direct/iterated pullback comparisons, gives the result.

When both `j : Q ⟶ G` and `i : P ⟶ G` are monomorphic, the actual construction
`factorOnEtaleImage b j i h` is the induced homomorphism `Q_V ⟶ P_V`,
where `V` is the open image of `b` and `h` is the supplied containment over
`U`. It uses the published `factorOfRangeLE` on the descended containment.
The theorem `factorOnEtaleImage_comp` proves that composing this homomorphism
with `i_V` gives `j_V`.

Finally, `exists_open_range_le_of_etale` gives the open containment
neighbourhood of `b u` for each `u : U`. Thus if `b u = s`, rewriting by this
equality produces a neighbourhood of the specified point `s`.

All constructions and conclusions are polymorphic in the universe of the
schemes. No affine, smoothness, reductivity, closedness, quasi-compactness, or
finiteness hypothesis on the base is used. Relative parabolic inclusions supply
the required monomorphisms, so the results apply to them.

## Provenance

This is a derived internal construction, assembled from the published
subgroup-functor descent and range-transport interfaces and Mathlib's
effective-epimorphism theorem. The open-image construction is reused from the
torus-isomorphism-locus module; no new open image or external literature
transcription is asserted. Worker 606 identified the etale-image descent step
needed in the parent proof, and Worker 652 implemented the general form here.
