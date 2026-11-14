# Reduction of the prescribed-torus Levi theorem to structure inputs

This internal construction composes the local prescribed-torus construction,
overlap matching, effective Levi descent, and global containment and uniqueness.
It retains three proposition inputs:
`RelativeTorusDynamicPresentationStatement`,
`DynamicRelativeLeviStatement`, and `RelativeUnipotentRadicalStatement`.
It does not prove these inputs.

`RelativeLevi.torusLeviWitness` works over an arbitrary scheme in every universe.
Its other hypotheses are exactly those of `RelativeTorusLeviStatement`:
reductivity of the ambient group, relative parabolicity of the supplied
inclusion, a prescribed closed relative torus, and maximality of that torus on
every residue-field fibre of the parabolic. Its output is an actual
`TorusLeviWitness`: a group scheme, an inclusion into the original parabolic,
the full relative Levi predicate, containment of the prescribed torus range,
and uniqueness of that range among every competing relative Levi containing
the torus on all test schemes.

The proof first obtains `EtaleTorusLeviData` from the three structure inputs.
The canonical pullback-square comparisons and local uniqueness give the
all-test matching predicate on the cover. The effective descent construction
chooses a global radical, compares its local pullbacks with the local Levi
radicals using radical uniqueness, and constructs an actual global Levi
representative. The gluing constructor equips that representative with
containment and global uniqueness. Affineness of the parabolic, needed for
radical transport and for base change of competing Levis, follows from the
given relative parabolic predicate.

`relativeTorusLevi_of_structureStatements` extracts the five fields of this
actual witness to prove the unchanged `RelativeTorusLeviStatement` under the
same three explicit structure inputs. It adds no field, reducedness,
splitness, affine-base, or global-cocharacter hypothesis. Equality of ranges
is equality of subgroup functors on every test scheme.

The provenance is derived from the imported local construction and descent
lemmas. This is the complete conditional reduction of the host target;
unconditional proofs of the three structure inputs remain necessary to
conclude the host task.
