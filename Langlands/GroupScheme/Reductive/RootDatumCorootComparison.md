# Coroot uniqueness from finite normalizer image

Author: Worker 1283.

This internal unit constructs the root index equivalence between any two
supplied actual root data of the same torus embedding. It proves that the
equivalence also matches coroots provided that the full normalizer image
on the character lattice is finite. It then conditionally derives the
published `RootDatumUniquenessStatement` from
`SplitTorusWeylImageFiniteStatement`.

The algebraic argument avoids choosing an invariant inner product.
Two integral reflections along the same vector, with defining
functionals both taking value two on that vector, have product
`y ↦ y + (g(y) - f(y)) x`. This product fixes `x`, so its `n`th power
adds `n (g(y) - f(y)) x`. If the product has positive finite order,
applying `f` to that identity gives
`n (g(y) - f(y)) 2 = 0` in the integers. Thus the two functionals agree.
This proof does not require torsion-freeness or finite generation of the
ambient additive group.

For two actual root data `P` and `Q`, `IsRootDatumOf` realizes each
reflection by an actual normalizing point. Their product belongs to the
finite subgroup `weylImage i`, so it has finite order. The actual lattice
pairing expresses the defining functionals as pairing with the coroots;
the self-pairing is two by each root datum's axiom. The algebraic lemma
identifies the functionals, and perfectness of the pairing identifies the
coroots.

`IsRootDatumOf.rootIndexEquiv` is constructed by identifying each root
index type with the range of its embedded root map, and then using the
common actual root range. Its root formula needs no finiteness premise.
`rootIndexEquiv_coroot` applies the preceding coroot comparison. The two
root index types have independent universes and need not carry finite
instances.

The final conditional theorem retains the exact published reductive
uniqueness target at arbitrary universe `u`. It obtains affineness and
local finite type from connected reductivity, and monomorphism from the
maximal torus's closed embedding. It applies the supplied general
finite-image proposition and the constructed index equivalence.
Finiteness of the actual full normalizer image is still an explicit
geometric obligation. This module does not prove that proposition, the
unconditional root-datum uniqueness theorem, or the central-isogeny
root comparison.

The construction and proof are internal deductions from the published
actual-normalizer, root-datum and lattice-pairing interfaces and finite
group order. They implement the finite-Weyl-image coroot-uniqueness
argument by an integral finite-order calculation rather than averaging a
positive form.
