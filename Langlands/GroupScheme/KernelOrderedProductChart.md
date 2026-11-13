# Kernel comparisons for ordered multiplication charts

This internal adapter applies the published actual ordered-multiplication
and product-chart kernel constructions. Its derivation uses identity points,
the ordered-multiplication compatibility square, and the existing kernel
comparison; it introduces no additional assertion from the literature.

The base is an arbitrary scheme. Two finite families of group-scheme
homomorphisms `j` and `k` map the respective factors into ambient groups.
A homomorphism `q` between the ambient groups and a homomorphism `f i` for
each factor must satisfy `j i ≫ q = f i ≫ k i`. Both ordered multiplication
charts must be monomorphisms. The empty finite family is included.

`one_comp_orderedMultiplication` proves that the identity point of the
source product maps to the identity point of the ambient group on every
test scheme. Product coordinates preserve the identity, every factor map
is a group homomorphism, and the ordered product of identity elements is
the identity. `unit_orderedMultiplication` recovers preservation of the
unit section by precomposing the identity-point equation with that section.
Neither assertion says that ordered multiplication preserves group products.

`finiteProductUniverseIso` reindexes the categorical product along the
canonical equivalence from `ULift (Fin n)` to `Fin n`, then forgets the group
structure. This lets the general kernel-product API use its index type in
the base universe while leaving the ordered charts indexed by `Fin n`.
Projection equations prove naturality with respect to the factor maps.
`orderedProductKernelChart` precomposes the original ordered multiplication
with this isomorphism. Its monomorphism instance, compatibility square and
unit equation follow from the corresponding original-chart hypotheses,
naturality, and the fact that the reindexing is a group homomorphism.

`orderedMultiplicationKernelIso` assumes a morphism from the entire actual
scheme-theoretic kernel of `q` into the source product whose composite with
the source chart is the kernel inclusion. The existing
`orderedMultiplication_map` supplies the chart compatibility square, and
the new unit lemma supplies the unit hypothesis of `KernelProductChart.iso`.
The lift is postcomposed with the inverse reindexing isomorphism. A second
inverse reindexing on the product of factor kernels gives the result with
the original `Fin n` index.
The conclusion is an isomorphism over the same base between the product
of the actual factor kernels and the actual ambient kernel.

`orderedMultiplicationKernelIso_baseChange` uses the same factorwise
compatibility and monomorphism hypotheses over the original base. After
an arbitrary base change, its full-kernel lift has target the pullback
of the original source product and must compose to the actual base-changed
kernel inclusion. `KernelProductChart.iso_baseChange` converts that lift
using the canonical product comparison and gives the isomorphism over
the new base. Before applying it, the lift is postcomposed with the pullback
of the inverse reindexing; functoriality and the inverse equation prove its
required chart composite. Reindexing the resulting kernel product back to
`Fin n` yields the displayed isomorphism. This is the form consumed by
special-fibre containment.

`smooth_connected_orderedMultiplicationKernel_baseChange` specializes the
new base to the spectrum of an arbitrary field. Every actual base-changed
factor kernel is additionally required to be smooth, affine and connected.
The existing finite-product geometry and scheme-isomorphism transfer give
smoothness and connectedness of the full kernel.

These are scheme isomorphisms, with no assertion that the factors commute
or that the isomorphism preserves multiplication. No unipotence conclusion
is drawn. Existence and monomorphism of the ordered charts, construction
of the full-kernel lift, and factor geometry remain explicit inputs. This
module does not prove the root-depth kernel theorem or KP Proposition 8.4.15.
