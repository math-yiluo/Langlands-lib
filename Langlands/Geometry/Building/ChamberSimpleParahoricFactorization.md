# Full parahoric factorization across a chamber-simple wall

This derived unit proves the full generated-parahoric simple-wall
factorization from three retained algebraic inputs. It works in arbitrary
universe `u`, over a nonarchimedean local field `F : Type u`, with the
existing actual `P : ParahoricBuildingData G` for an affine group scheme.
The apartment satisfies `P.apartment.SatisfiesApartmentAxioms P.centralizer`.
The retained inputs are:

- `RelativeRoot.HasRankOneFactorization P.i`, for this actual embedding.
- `P.zeroDatum.CoverImageCentralizerNormKernelStatement`, for the supplied
  cover and centralizer-zero subgroup.
- `RelativeRoot.DynamicRootOrderedProductStatement.{u}`.

Let `ψ ∈ simpleAffineRoots P.affineRoots C`, let `α : relativeRoots P.i`
satisfy `ψ.linear = rootForm P.i α`, and let `v` be a coroot of `ψ` for
`P.affineRoots`. Simple-root membership includes the chamber condition.
Write `s` for the geometric reflection `affineReflection ψ hv.1`.
The theorem
`parahoric_subset_reflection_mul_wall_of_rankOneFactorization` proves

`P.parahoric C ⊆ P.parahoric (s '' C) · P.apartment.affineRootGroup α ψ`

as an inclusion of subsets of the existing `rationalPoints G`.
The membership theorem `simpleFactorization_of_rankOneFactorization`
states that each `g ∈ P.parahoric C` has factors `b' ∈ P.parahoric (s '' C)`
and `u ∈ P.apartment.affineRootGroup α ψ` with `g = b' * u`. Its quantifiers
and factor order supply the `simpleFactorization` field of the existing
`AffineIwahoriTitsInputs` when the three algebraic inputs are available.

The entry
`chamberSimpleParahoricProductInclusion_of_rankOneFactorization` sends a
point of `P.parahoric C` to the same ambient point in the subtype of the
displayed product set. It does not choose factors, assert uniqueness,
or assert that the product set is a subgroup. No point, cocharacter,
root enumeration or decomposition is an additional premise of these
full-parahoric results.

The preliminary theorem
`KPApartmentData.negativeChamberRootGroups_le_reflection` works over any
field with actual apartment data `D`. It assumes the affine-root-system
condition for `D.affineRoots`, AS4 for the extended roots, the same
simple-root, derivative and coroot data, a cocharacter `ν` positive on
`α`, and a point `x ∈ C`. It proves the subgroup inequality

`(⨆ b : positiveRelativeRoots i (-ν), D.chamberRootGroup x false b)`
`  ≤ D.sharpFixer (s '' C)`.

Here `false` selects depth zero. This preliminary result needs neither
genericity of `ν` nor splitness or root finiteness.

The negative-subgroup proof reduces the supremum inequality to each
root direction. Facet constancy identifies its depth-zero point group
with the chamber root fixer. Positivity on `-ν` is negativity on `ν`.
The existing `rootFixer_le_reflection_of_pairing_neg` therefore puts
this group in its reflected-chamber root fixer, which is contained in
the reflected sharp fixer. Subgroup-supremum induction gives the result.

For the full factorization, the actual maximal split torus supplies
splitness. Smoothness of the actual connected reductive group supplies
local finite type, hence finiteness of its relative roots. The existing
`RelativeRoot.exists_genericCocharacter_pairing_pos` chooses a generic
integral `ν` positive on `α`. Nonzeroness of `α` is part of actual
relative-root membership. A chamber point exists, and finite injective
enumerations of the positive indivisible roots for `-ν` and `ν` exist.

The existing
`chamberIwahoriDecomposition_of_rankOneFactorization` uses the retained
three algebraic inputs and apartment axioms to supply the full chamber
Iwahori conclusion. Its ordered-product range at depth zero writes
every element of `P.parahoric C` as a negative block product, followed
by a mapped centralizer-zero point, followed by a positive block product.
The existing `range_orderedPositiveChamberBlockProduct_eq_iSup` puts
each block product in its corresponding generated root subgroup.

The preliminary negative-subgroup result puts the first factor in the
reflected sharp fixer and hence the reflected full parahoric. The mapped
centralizer-zero point lies in every full parahoric by the defining
join. The imported
`positiveChamberRootGroups_subset_reflection_mul_wall` splits the last
factor into a reflected sharp-fixer point and a wall-root-group point.
Closure of the reflected full parahoric under multiplication and
associativity give the claimed factorization. Reversing the product-set
membership equality gives the membership theorem. The entry then
packages the inclusion without changing the ambient point.

All content is derived from the current Library's actual apartment,
collection, generic-cocharacter and conditional Iwahori results, and the
unchanged wall-product helper modules bundled while their publication
is pending. No new external-source assertion is introduced. The three
algebraic inputs remain hypotheses: this unit proves neither their
universal versions nor the unconditional
`ChamberSimpleFactorizationStatement` or `AffineIwahoriTitsStatement`.
The unchanged apartment-only endpoint remains open.
