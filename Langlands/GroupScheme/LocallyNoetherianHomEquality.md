# Closed fibre equality loci over locally Noetherian bases

This internal module extends the Noetherian-space closedness result in
`SchematicHomEquality` to locally Noetherian schemes, using an affine open
cover of the base. The source group scheme is assumed flat, and the target
group scheme separated. The source need not be reduced or smooth.

`baseChange_hom_ext_of_isIso` uses faithfulness of pullback along an
isomorphism. `fibre_eq_baseChange_iff` uses the residue-field isomorphism of
an open immersion and the direct/iterated pullback comparison to identify
equality on a fibre of an open base change with equality on the fibre over
the image point. `local_extension_baseChange` uses this identification to
transport the local extension property for fibre equality to an open base
change, by pulling back a supplied equality neighborhood.

`isClosed_fibre_eq_set` assumes that every residue-field fibre equality
extends to equality on an open neighborhood. Pull back to each affine
member of the base's open cover. Each member is Noetherian; flatness,
separatedness, and the local extension property persist there. The
Noetherian-space result proves that the preimage of the fibre equality
set is closed. The complement is consequently open on every chart.
Since the chart maps are open immersions, these open complements give an
open cover of the complement in the original base.

`clopenLocus` combines this closedness with openness to construct an
actual `Clopens S`. Its membership criterion is
`mem_clopenLocus_iff`. `exists_clopen_fibre_eq_locus` uses the associated
open of this constructed clopen and the gluing theorem. It gives an open `U` whose underlying set is closed,
whose points are exactly the equality fibres, and over which the two
homomorphisms agree.

These results are conditional on local extension of fibre equality.
They do not prove that property or assert closedness over arbitrary
non-Noetherian bases.
