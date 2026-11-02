# Finite representatives in Renard's actual valuation image

Author: Worker 454.

Let `F` be any actual nonarchimedean local field with the Library's field,
valuation and topology instances. Let `s : T.toGrp ⟶ Z` be an actual
homomorphism of group schemes, with `T` commutative. This module uses
`Langlands.Plancherel.rationalCharacterValuation Z`, whose coordinates
are the positive integer orders of actual rational character values, and
its actual range `rationalCharacterValuationImage Z`. No finite-rank,
discreteness, full-rank or index assertion is part of that range definition.

In the Cartan application, `Z` is the algebraic centralizer of the chosen
maximal split torus `S` of `G`, and `s` is `S → Z`. The quotient by the
kernel of this valuation is the quotient by `rationalCommonNormKernel Z`,
by the published `rationalCharacterValuation_ker` and
`rationalNormKernelQuotientEquiv`. This is the norm-kernel quotient used
by Renard. No identification with the smaller KP parahoric subgroup
`Z(F)^0` is made.

## Full lattice representatives

`splitValuationImage s` is the range of the actual point map
`S(F) → Z(F)` followed by the valuation, restricted to its actual image.
Thus it is a subgroup of `rationalCharacterValuationImage Z`, not an
assumed copy of the full cocharacter lattice. `latticeResidue s` is the
composite into the quotient of this actual range by that actual subgroup.

`IsFiniteLatticeTransversal s F0` means that `F0` is a finite set of actual
points of `Z` and its map to this quotient is bijective. It therefore
requires one representative for every coset, with no two representatives
in the same coset. It does not assert finite index for arbitrary inputs.

`tildeC0 s F0` is the pointwise product `C0 T s * F0`.
`tildeC0Plus s F0 dominant` is its intersection with the supplied set
`dominant`. The two membership lemmas unpack precisely these definitions.
The intended `dominant` is the nonnegative chamber of the actual
centralizer valuation, not a replacement subgroup or a cocharacter
parametrization. These generic constructions do not define that chamber.

`IsValuationSection A` requires the valuation-image projection on the
actual set `A` to be bijective onto the entire actual image.
`IsDominantValuationSection dominant A` requires `A ⊆ dominant` and a
bijection, restricted to `A`, onto the image of `dominant`.
The latter image is a set in the actual image subgroup; it is not
required to be a subgroup. These predicates describe representative
sections. Their existence and their comparison with double cosets are
separate propositions.

## Positive products and the additional chamber condition

`IsChamberCompatibleTransversal s positiveRoots dominant F0` requires all
three of: the full finite lattice transversal property, `F0 ⊆ dominant`,
and the equality

`(C0 T s * F0) ∩ dominant = C0Plus T s positiveRoots * F0`.

The equality is an explicit additional condition. In particular neither
finite index nor positivity of the selected representatives is defined
to imply it.

`IsFinitePositiveProductCover s positiveRoots dominant Fcover` requires
the set `Fcover` to be finite and dominant, the product `C0Plus * Fcover`
to remain dominant, and the valuation-image projection of that product
to cover the image of `dominant`. Several elements of `Fcover` may have
the same residue modulo `splitValuationImage s`. The valuation-image
projection need not be injective on the product.

`HasNonrepeatingPositiveProducts s positiveRoots F0` is a separate
injectivity requirement on the map from pairs `(c,f)` to the valuation
of `c*f`. It distinguishes a product covering from a disjoint
parametrization by pairs. If the K0 double-coset relation on the chamber
is subsequently identified with equality of these valuation values, a
dominant valuation section indexes distinct double cosets; a finite
positive product cover alone supplies only a covering. No K0 or
double-coset comparison theorem is proved here.

## Original sources and derived provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
V.2.3 (printed page 105, PDF page 111) defines the actual image `Λ(M)`;
V.2.5 (printed page 107, PDF page 113) defines the uniformizer section
`C_A`; V.3.23 (printed page 117, PDF page 123) defines a finite
transversal `F_M`, `C_A F_M` and its dominant intersection, then makes
the additional chamber-compatible choice. V.5.1(4) (printed page 122,
PDF page 128) writes both the chamber-representative union and the
positive-product union as disjoint.

The Lean predicates package these choices and distinguish their
mathematical requirements. The finite positive covering predicate and
the separate nonrepetition predicate are derived interfaces for stating
exactly which part of the product formula a later result establishes.
They do not assert that Renard's stronger chamber-compatible choice has
been constructed, or that it follows from finite index. The original
disjoint-union typography is retained in this source account without
claiming a verified actual-group counterexample.

## Remaining obligations

For the actual centralizer, prove the split-component comparison, finite
index, uniformizer-image identification, and injectivity on the
uniformizer subgroup. Then construct finite representatives, prove the
full and dominant section properties, and state the additional
chamber-compatible or finite-cover assertions with their exact hypotheses.
The corrected KP quotient by `Z(F)^0`, the maximal-compact comparison,
and the same-K0 standard-Levi compatibility remain separate tasks within
the Cartan statement family.
