# Exact semigroup products in a central extension

The local assembly theorem
`hasOrderedSemigroupProducts_of_centralExtension_of_comap` assumes the existing
semigroup realization and smooth quotient statements and the exact equalities
`(semigroupSubgroup b A).comap z = semigroupSubgroup bZ A` for every
additive semigroup `A`. It also assumes the exact
per-action ordered product property for a supplied central subgroup and its
actual smooth fppf quotient. It proves that property for the ambient action.
These inputs remain explicit; this unit does not prove the general geometric
prerequisites or the full `SemigroupOrderedProductStatement`.

For the assembly theorem, `k` is an arbitrary field in universe `u`, `S` is a
split `k`-torus, and `b`, `bZ`, and `bQ` are its supplied actual automorphic
actions on the group schemes `G`, `Z`, and `Q`. The inclusion `z` is closed and
central, the quotient map `q` has the represented fppf kernel `range z`, and
both maps intertwine these actions. All three groups are affine, and the
ambient group and quotient are smooth. The local version does not require
smoothness or connectedness of the whole central subgroup. The original theorem
`hasOrderedSemigroupProducts_of_centralExtension` retains its original signature:
it assumes a smooth connected central subgroup and the full intersection
statement and supplies the local equalities using its normal-subgroup branch.

`centralSemigroupKernelFamily` assembles the canonical `factorKernelHom` maps
for a finite family of actual commuting quotient squares. It maps each actual
factor kernel into the chosen representative of the ambient kernel. The
assembly theorem uses this same family for its kernel product.

The proof first includes the central subgroup's actual Lie support in the
ambient support using equivariant monomorphism transport. It includes the
quotient's support using surjectivity of every weight-space differential of a
smooth equivariant map. The support-restriction theorem therefore applies both
supplied product properties to the original ambient blocks. It preserves the
actual semigroup subgroup functors and their ordered multiplication.

Semigroup realization chooses smooth connected closed representatives of the
ambient factors. The smooth quotient input supplies actual smooth surjective
maps from each ambient representative to the corresponding quotient factor.
The canonical `factorKernelHom` maps their actual scheme-theoretic kernels into
the supplied central subgroup and represents the exact preimage of the ambient
factor. The supplied local inverse-image equality identifies this preimage
with the corresponding central semigroup factor, including when zero belongs to its
positive semigroup. Invariance under replacing representatives transfers the
central ordered-product isomorphism to these actual factor kernels.

The represented fppf-kernel isomorphism identifies the central subgroup with the
actual kernel of `q`. Postcomposition transfers the kernel product and its
inclusion equations to that kernel. Smoothness of the factor maps supplies
flatness and local finite presentation. A point killed by `q` factors through
`z`, so it commutes with every ambient point over the same test. The existing
central-extension descent theorem now gives an isomorphism for the original
ambient ordered multiplication.

The exact original-block-versus-positive-closure exclusion, occurring zero,
positive generation without automatically inserting zero, arbitrary orders,
and empty indexing are retained. No disjointness of generated semigroups is
assumed. The argument is derived entirely from the imported actual constructions
and the named explicit premises, without a new literature assertion.
