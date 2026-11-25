# Relative quasi-split data from compatible actual descent solutions

This internal assembly works over arbitrary schemes along any surjective étale
map. It assumes actual solutions of the ambient, Borel and torus data; it does
not assume the downstairs Borel or maximal-torus properties.

`RelativeQuasiSplitTorusData` records a reductive group with an actual relative
Borel, an actual commutative relative torus with a closed fibrewise maximal
inclusion, and containment of the torus in the Borel. Its `quasiSplit` theorem
uses the supplied actual Borel presentation.

`Descent.Solution.commGroupSchemeOfEtale` equips the actual downstairs group of
a solution of data on a commutative group with its descended commutative
structure. The solution comparison transfers commutativity upstairs, and
faithful étale pullback reflects it.

`Descent.Solution.relativeQuasiSplitTorusData` takes three actual solutions,
a reductive ambient group upstairs, a closed relative Borel, a closed
fibrewise maximal relative torus contained in it, and compatibility of both
inclusions with the supplied data. Actual homomorphism descent constructs both
downstairs inclusions. Their recovery squares prove closedness by étale
reflection. Reductivity reflects after the ambient solution comparison.
Source and ambient isomorphism transport of the upstairs relative Borel,
followed by étale reflection, gives the downstairs Borel.
The torus property and fibrewise maximality reflect using their actual source
comparison. Reflection of represented subgroup containment gives the final
torus-in-Borel containment.

There is no affine-base or quasi-compact-cover assumption. Effective object
descent remains an input through the three actual solutions; this construction
does not supply invariant data, those solutions, or an innerness witness.
