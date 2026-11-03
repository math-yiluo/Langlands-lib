# Split parts of maximal tori in minimal rational parabolics

Author: Worker 1308.

`MinimalParabolicTorusSplitPartStatement.{u}` is an unproved proposition
definition. For every field `k : Type u`, connected reductive group scheme
`G`, minimal rational parabolic `j : P → G`, and rational maximal torus
`t : T → G` with a specified factorization `f ≫ j = t`, it considers any
maximal split subtorus `a : A → T`. It asserts that `a ≫ t` is a maximal
split torus of `G` and that its whole-torus centralizer is contained in
`P` on every test scheme.

The hypothesis `IsMaximalSplitTorus a` concerns maximality inside `T`.
The first conclusion concerns maximality inside `G`. The statement uses
existing group-scheme homomorphisms, closed immersions, the published
maximal-torus predicates, and the all-test subgroup functors. It adds no
assumption on the characteristic, perfectness, splitness or cardinality
of the field. The torus `T` is not assumed split. The statement does not
assert existence of `T`, `f` or `a`.

This is a derived input to the proof of Borel–Tits 4.18. The source is
Borel and Tits, *Groupes réductifs* (1965), source ID
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
The relevant passages are 2.15(d), printed p.70 (PDF p.17); 4.2–4.3,
printed pp.85–86 (PDF pp.32–33); and 4.15(b), 4.16, and the split-part
step in the proof of 4.18, printed pp.91–92 (PDF pp.38–39). The source's
0.3, printed pp.57–58 (PDF pp.4–5), permits the interpretation as affine
geometrically reduced group schemes. The Lean statement retains actual
subgroup morphisms and scheme-theoretic centralizer containment.

The mathematical derivation, still to be proved in Lean, is as follows.
For such a maximal torus `T` in `P`, the source identifies
`S = T ∩ R(P)` as a rational maximal torus of the radical and
`L = C_G(S)` as a rational Levi subgroup of `P`. The standard parabolic
structure identifies `S` with the connected central torus of `L`
(the connected center in the source’s reduced-group convention). By
4.16(iii), minimality of `P` makes `L` the centralizer of an ambient
maximal split torus `S₀` contained in `R(P)`. That split torus is
central in `L`, hence lies in this connected central torus `S` and then in `T`.
The largest split subtorus of the commutative torus `T` contains `S₀`;
ambient maximality forces equality of their subgroup images. It follows
that this split part is ambient maximal and its centralizer is `L`,
which lies in `P`.

The printed proof of 4.18 cites “4.6” at its Levi-to-split-torus step.
The derivation just described instead records the sufficient inputs
4.15(b) and 4.16(iii) explicitly. It neither takes the conclusion of
4.18 as an assumption nor treats the split-group hypothesis of 4.6 as
available over an arbitrary field. The rational Levi construction,
connected-center identification and use of 4.16 remain proof
obligations. This module contains no proof of them.

The phrase “maximal split part” uses the usual largest split subtorus of
a commutative torus. The separately derived module
`Rational.TorusSplitPart` constructs the largest split subtorus for
commutative affine groups of finite type and proves its equivalence
with maximal splitness inside that commutative group. This statement
only uses the previously published maximal-split predicate, so its
interface does not depend on that additional construction.
