# Function and morphism detection on bounded split-torus points

This internal derived module upgrades Laurent polynomial detection on tuples of
valuation-one units to function detection on the actual character-valuation
kernel of any split torus over a valued field with infinite residue field.

The proof first checks that the diagonalizable-to-product isomorphism preserves
affine coordinates. The spectrum of the Laurent evaluation map then supplies
points with those coordinates. Valuation-one tuples belong to the character
kernel by the published coordinate characterization. Pullback by the split
isomorphism reduces vanishing of global sections to the Laurent polynomial
result in `SplitTorusUnitDetection`. Detection is invariant under group-scheme
isomorphisms because homomorphisms preserve character kernels.

For morphisms into an affine target, the proof compares the pullbacks of an
arbitrary global section: their difference vanishes on the kernel, hence is
zero. Affine morphism extensionality gives equality of the morphisms. These
results are internal tools for the descended-apartment torus comparison; no
additional theorem is attributed to external literature.
