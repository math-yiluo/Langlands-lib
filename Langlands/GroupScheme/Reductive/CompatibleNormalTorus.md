# A normal subgroup's maximal torus inside a chosen ambient maximal torus

This module constructs an actual compatible maximal torus under the explicit
premise that maximal tori in the ambient group are conjugate over the ground
field. It uses the existing `MaximalToriAreConjugate` predicate and does not
prove that predicate. Its construction works over any field and universe.

`CompatibleNormalMaximalTorus h t` contains a commutative group scheme `S`,
an inclusion `s : S.toGrp ⟶ H`, and a commutative group scheme homomorphism
`f : S ⟶ T`. The map `s` is a maximal torus of `H`. The map `f` is a closed
subgroup inclusion, and its composite with the given ambient torus map is
exactly `s ≫ h`. Thus both routes to the original ambient group agree as
actual morphisms, not only on rational points.

The existence theorem assumes that the ambient group `G` is affine and
locally of finite type, that `h : H ⟶ G` is a closed subgroup with normal
full range on all tests, that `t` is a maximal torus of `G`, and that
`MaximalToriAreConjugate G` holds. Closedness supplies affineness and local
finite type for `H`. The existing maximal-torus existence theorem gives
`s₀ : S ⟶ H`. Extend the closed torus `s₀ ≫ h` to a maximal torus
`m : M ⟶ G`. The conjugacy premise supplies `g` and an isomorphism from
`M` to `T` with `m ≫ int(g)` equal to the isomorphism followed by `t`.

The published `SubgroupFunctor.IsRepresentedBy.conjugateIso` restricts
`int(g)` to an actual automorphism `c` of the specified representative `H`,
using its all-test normality. Set `s = s₀ ≫ c.hom` and compose the extension
map with the isomorphism of ambient tori to obtain `f`. The conjugation
composite formula gives the required commuting square. Maximality of `s`
is preserved by `c`; closedness of `f` follows by cancelling the closed
ambient torus inclusion from that square.

`compatibleNormalMaximalTorusOfConjugacy` chooses this data. When the field
is algebraically closed, `CompatibleNormalMaximalTorus.isSplitSubtorus`
uses the published finite Galois splitting theorem to show that `s` is
a split subtorus. Splitting needs no additional conjectural premise.

The provenance is internal. The construction reuses the first part of the
published `exists_radicalTorusIntersection_of_complement` argument in
`Absolute.MaximalRankRadicalTorusIntersectionOfComplement`. That earlier
theorem continues to identify a whole torus intersection using a unipotent
complement. The present construction extracts compatibility for arbitrary
closed normal subgroups and requires no such complement, solvability or
intersection equality. The generic conjugation automorphism is imported
unchanged from that module.

This result discharges the compatible-torus construction needed by the
normal-root dichotomy once ambient maximal-torus conjugacy is supplied.
The general conjugacy theorem remains an existing separate proof obligation;
this module does not establish the unconditional semisimple generation
theorem.
