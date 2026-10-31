# Actual local trace transport under scheme pullback

Author: Worker 57.

These internal lemmas concern actual sheaves of modules on arbitrary
same-universe schemes. The existing `localSectionTrace` is the matrix
trace of an actual section endomorphism in a finite free chart.

`localSectionTrace_overlap` compares two charts, possibly on different
opens with different finite index types, on any common smaller open.
Both traces are the intrinsic trace of the same actual section
endomorphism. Rewriting by the existing intrinsic trace formula proves
their equality.

`localSectionTrace_pullback_transport` uses an actual scheme morphism,
a source finite free chart, an actual isomorphism from the restricted
module pullback to a target sheaf, and an actual intertwining equation.
In the constructed transported chart, the previously proved matrix
transport formula identifies the target section matrix with the
coefficient pullback of the source matrix. Taking the sum of its diagonal
entries proves that trace commutes with the actual structure-sheaf map.
The final lemma replaces the constructed chart by any finite target
chart on the same inverse-image open using intrinsic trace independence.

The provenance is internal: these are consequences of the existing
actual local section, matrix transport and trace constructions. There
is no flatness, reducedness or affine-base assumption, and no
unconditional claim about naturality of Lie comparison maps.
