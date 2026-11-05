# Actual normalizer lifting through a central cover

This is an internal derivation from the Library's split-torus image theorem,
maximal-split-torus universal property and all-test centralizer reflection for a
central isogeny. It is a bridge for the upper inclusion in KP Theorem 7.5.3(2);
it does not assert the final apartment-action theorem.

Over a field `k` in any universe `u`, let `π : C → D` be a central isogeny and
let `d : D → G` have monomorphic underlying scheme map. Assume that `C` is
affine over `k`, that `i : T → C` is a maximal split torus, that `S` is a
commutative group scheme, and that supplied maps `t : T → S` and `j : S → G`
satisfy `i ≫ π ≫ d = groupHom t ≫ j`. Every chosen point `c ∈ C(k)` whose
image under `π ≫ d` normalizes `j` then normalizes `i`.

The proof uses `IsMaximalSplitTorus.exists_factor_of_commute` from
[`SplitTorusFactorization`](SplitTorusFactorization.md): any split torus
commuting with a maximal split torus factors through it. The commuting pair gives a homomorphism from their
product. The split-torus image theorem factors that homomorphism through a
closed split torus. Maximality makes the map from the original maximal torus
to that image an isomorphism, giving the required factorization of the other
torus. In particular, if a maximal split torus commutes with its conjugate,
the factor between them is an isomorphism by maximality of the conjugate.
This is precisely normalizer membership.

For the main result, conjugate `i` by `c`. Both the original and conjugated
maps, after `π ≫ d`, factor through the same commutative group `S`, because
the image of `c` normalizes `j`. Their values therefore commute on every test
scheme. Monicity cancels `d`. The central-isogeny centralizer-reflection
theorem then reflects all-test centralization through `π`. The resulting
commutation of the original and conjugate source tori implies source
normalizer membership by the preceding argument.

The module also constructs a group homomorphism from the inverse image of
the target normalizer to the source normalizer, with unchanged underlying
cover point, and proves existence of a normalizer lift for any target
normalizer point belonging to the actual image of `C(k)`.

No surjectivity of `t` or of a rational-point map is assumed. The target
commutative group need not be a torus, and its map `j` need not be monic or
maximal. The result supplies normalizer lifting only; the derived-group
torus data, apartment comparison, facet fixing and affine Weyl conclusion
remain separate obligations.
