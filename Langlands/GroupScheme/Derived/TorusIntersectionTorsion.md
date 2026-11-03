# Torsion bounds for split-torus intersections with derived subgroups

This internal adapter concerns the full subgroup functors on every test scheme.
Let `d : D ⟶ G` exhibit the actual scheme-theoretic derived subgroup, and let
`i : B ⟶ G` have split-torus source. If one natural number `n` times every
character of `B` is the restriction of a character of `G`, every point `x` of
`B` whose image belongs to the range of `d` satisfies `x ^ n = 1`.

The implemented proof first shows that characters detect the identity of a
split torus over an arbitrary scheme base. An isomorphism to a finite product
of copies of the multiplicative group reduces this to the coordinate
characters and the all-test point equivalence for that product. For a
character `χ` of `B`, choose a character of `G` restricting to `n • χ`.
The published derived-subgroup annihilation lemma makes its value on the
image of `d` equal to one. Evaluation of a character multiple is a power,
so every character of `x ^ n` is one, and identity detection finishes.

For commutative `B`, the preimage of the full range of `d` therefore lies
in the range of the actual integer-multiplication kernel `torsion B n`.
`IsDerivedSubgroup.torusIntersectionTorsionFactor` constructs a group-scheme
morphism into this kernel from any morphism `c : C ⟶ B` whose range is in
that preimage. It uses the existing factorization through a represented
subgroup. `torusIntersectionTorsionFactor_comp` states that composing this
factorization with the torsion inclusion recovers `c`.

If the character restriction has finite-index range, its index is nonzero
and multiplication by that index lands in the range. This supplies a
uniform nonzero exponent. Over an arbitrary field, the published
`CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict`
supplies this premise for a central split torus in an affine group scheme
locally of finite type. No reductivity assumption is needed for this
specialization. All point statements include nonreduced test schemes.

The construction and proof are an internal combination of the published
character evaluation, split-torus point model, actual derived-subgroup
annihilation, character finite-index restriction, and torsion-kernel APIs,
together with Mathlib's finite-index subgroup identity. This file proves
neither finiteness of the torsion kernel nor the full centre of a reductive
group being a finite extension of a torus. Those structural inputs remain
separate obligations in the derived-subgroup semisimplicity proof.
