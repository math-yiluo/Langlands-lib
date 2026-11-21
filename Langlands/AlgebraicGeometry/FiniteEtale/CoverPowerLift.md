# Lifting positive powers to a pointed finite étale cover

For a finite étale cover and a supplied lift of the geometric point,
the Library identifies the image of its fundamental group with the
stabilizer of that lift. The orbit of the lift lies in a finite fibre,
so the image has finite index.

`liftPowerToCover` raises a fundamental group element to the order of
the permutation group of the fibre. This positive exponent makes the
result act trivially on the fibre. The Library's stabilizer lift then
gives an element of the fundamental group at the supplied lift with the
prescribed image. If a group homomorphism kills the cover image, the
same exponent kills the image of every element.

`fieldExtensionCover` applies the construction to the actual spectrum
of a finite separable extension. `fieldExtensionCoverPoint` lifts a
given geometric point by extending its field embedding into the same
algebraically closed field.

These constructions use the finite permutation action and the
published pointed-cover stabilizer comparison. The uniform power lift
is used to bound local monodromy after finite field extension.
