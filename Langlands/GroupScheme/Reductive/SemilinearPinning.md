# Actual pinned lifts along field automorphisms

Let `k` be a field in an arbitrary universe, `G` an actual affine `k`-group
scheme, and `p : SplitPinning G` a supplied complete split pinning. For a field
ring automorphism `σ : k ≃+* k` and a supplied based full root-datum
automorphism `e : p.basedRootDatumAut`, `p.semilinearPinnedIso σ e` is an
actual pinned isomorphism from the pullback of `p` along `Spec σ` to `p`.
The coefficient spectrum map uses `σ` itself, without inversion.

The underlying actual group isomorphism has source
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom σ.toRingHom))).obj G`
and target `G`. Its prescribed full root-datum equivalence is the inverse
canonical scalar-extension equivalence followed by `e`. Thus the construction
uses the entire integral character and cocharacter lattices, including central
directions, and carries the chosen simple-root Lie vectors as required by
`SplitPinning.Iso`.

`semilinearNegativeBorelIso` constructs an actual isomorphism from the
coefficient pullback of `p.negativeBorel` to `p.negativeBorel`.
`semilinearNegativeBorelIso_hom_comp` proves its inclusion square with the
ambient group isomorphism. Consequently `range_semilinear_negativeBorelHom`
proves equality of the transported and original subgroup ranges on all relative
scheme tests.

## Implemented construction

The preliminary `baseChangeAlong` construction applies more generally to a
ring equivalence between two fields `k` and `K` in the same arbitrary universe.
Surjectivity of this equivalence writes every target element as a scalar,
which is algebraic. This gives the algebraicity needed by the published
complete-pinning scalar extension. The induced algebra structure is used only
inside the construction, so a self-equivalence does not replace the canonical
self-algebra in the public Lie-vector specifications.

`baseChangeAlongRootDatumEquiv` reuses the canonical full lattice equivalence
of `PinningBaseChange`. `baseChangeAlong_simple_iff` uses the published
simple-support specification, which retains the original root indices.
`negativeBorelBaseChangeAlongIso` specializes the actual Borel comparison of
`PinnedBorelBaseChange` to the equivalence's scalar map. Its inclusion equation
is specialized in the same way.

For a self-equivalence, `semilinearRootDatumEquiv` composes the inverse
canonical root-datum equivalence with `e`. Because the first map retains the
root indices and the second preserves the chosen simple support, the composite
preserves support membership in both directions. The published actual pinned
isomorphism theorem then supplies `semilinearPinnedIso` with precisely this
prescribed root-datum equivalence.

Finally the actual scalar Borel comparison is composed with the Borel
isomorphism induced by this pinned isomorphism. Their inclusion equations give
the stated square by associativity. Invariance of subgroup ranges under an
isomorphism of the representing source proves the all-test range equality.

## Provenance and scope

This is an internal application of the published complete-pinning scalar
extension, actual pinned isomorphism theorem, dynamic Borel transport and Borel
base-change comparison. It introduces no external structural assertion.
The field and its universe are unrestricted; a complete pinning and a based
root-datum automorphism are still inputs. No family composition law, Galois
cocycle, pinning existence, effective descent, full-centre quotient or
unconditional quasi-split inner-form existence is established here.
