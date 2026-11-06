# Apartment comparison in a restricted Tits building

This module derives the group argument of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 1.5.6(5), printed pp.56–57 / PDF pp.87–88, for the Library's parabolic description of restricted apartments. It uses the existing Tits-system axioms; it assumes no apartment-comparison conclusion.

`exists_normalizer_doubleCoset_factor` applies the published parabolic double-coset equivalence to two arbitrary subgroups containing the distinguished Borel subgroup. Bruhat classification writes them as standard parabolics. Equality of the double cosets of two normalizer elements gives Weyl factors in the corresponding standard Weyl subgroups. A normalizer lift of the left factor belongs to the left parabolic and moves the first representative into the right coset of the second.

`exists_normalizer_mem_two_parabolics` uses this factor to adjust an apartment representative already in the first parabolic so that the adjusted element also belongs to the normalizer conjugate of the second parabolic. The remaining lemmas record subgroup conjugation, normalizer invariance and membership for the existing restricted apartments.

`exists_mem_two_parabolics_restrictedApartment_eq` is the comparison conclusion. If a restricted apartment contains a standard parabolic P and a normalizer conjugate nQn⁻¹ of another standard parabolic, then a group element k belonging to both subgroups represents that same apartment. Membership implies that k fixes by conjugation every subgroup containing either one. In the parabolic model, these are precisely the faces which need to be fixed in Proposition 1.5.6(5).

The implemented proof first changes the apartment representative on the right by a normalizer element so that it belongs to P. Conjugacy rigidity justifies this adjustment and puts the second transporter in Q. The normalizer double-coset adjustment finishes the proof, as in the source.

`twoParabolicApartmentTransport` chooses such an element in the intersection subgroup itself. `restrictedApartment_twoParabolicApartmentTransport` records that its restricted apartment is the specified one. These constructions work with arbitrary group universes and do not require finiteness of the simple-generator set; the source assumes finiteness to interpret its facets as a simplicial complex, whereas this subgroup argument uses no finiteness.

This is an intermediate group-theoretic result. It does not construct a distance, identify parabolic stabilizers with pointwise fixers in an affine realization, or prove the global metric realization statement.
