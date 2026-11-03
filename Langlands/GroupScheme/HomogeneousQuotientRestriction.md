# Restricting a supplied homogeneous quotient to a closed subgroup

This is an internal adapter derived from the published homogeneous-quotient
fiber and smooth-source descent interfaces. It works over any base scheme `S`
in universe `u`, with actual group schemes `H`, `P`, `K`, and `G` over `S`.
It introduces no structural existence theorem.

Let `d : H ⟶ G`, `i : P ⟶ G`, and `q : G.X ⟶ Q` be supplied maps.
Assume that, on every relative scheme `T`, the equality `a ≫ q = b ≫ q`
is equivalent to membership of `a⁻¹ * b` in the actual functorial range of
`i`. This assumption retains the original right-coset convention and includes
nonaffine and nonreduced tests.

The definition `productMap d i` is the actual morphism
`H ×_S P → G` sending `(h,p)` to `d(h)i(p)`. The lemma `productMap_comp`
uses the given fiber equivalence to prove that its composite with `q` equals
the first projection followed by `d ≫ q`: the difference of these two group
elements is the image of `p`.

For any `j : K ⟶ H` whose functorial range is the full preimage of
`range i` under `d`, `fibers` proves the same exact right-coset equivalence
for the restricted projection `d ≫ q`, on every relative scheme. Its proof
rewrites the original equivalence and uses that a group-scheme homomorphism
preserves products and inverses.

The geometry lemmas retain explicit hypotheses on multiplication:

- `smooth` assumes that `i` is a monomorphism, `q` is smooth, and
  `productMap d i` is smooth. The existing exact-fiber theorem
  `HomogeneousQuotient.smooth_subgroup_of_smooth_quotient` makes `P` smooth
  over `S`. Thus `H ×_S P → H` is smooth; the identity section of `P`
  makes it surjective. The equality `productMap_comp` makes the composite
  with `d ≫ q` smooth, so the published smooth-source descent theorem
  proves that `d ≫ q` is smooth.
- `surjective` assumes that `q` and `productMap d i` are surjective.
  Their composite is surjective, and the same composite equality implies
  that `d ≫ q` is surjective.
- `quasiCompact` assumes that `d` is a closed subgroup embedding and
  `q` is quasi-compact. A closed immersion is quasi-compact, so their
  composite is quasi-compact.

Finally, `restrict` packages these results as an existing
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient j`. Besides the
hypotheses just listed, it assumes the original projection is smooth,
surjective, and quasi-compact, and that the supplied target is separated,
locally of finite type, and quasi-compact over `S`. Its target is exactly
`Q`, its projection is exactly `d.hom.hom ≫ q`, and the target's three
geometry fields are inherited directly.

This construction does not prove that subgroup-stabilizer multiplication is
smooth or surjective in any particular application. It does not assert
existence of a quotient, a subgroup representative, a rational point, or a
rational lift. Applying it to a torus envelope still requires the structural
multiplication properties and the represented full-preimage stabilizer.
