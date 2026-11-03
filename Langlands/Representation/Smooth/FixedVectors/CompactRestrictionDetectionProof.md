# Proof of fixed-vector detection from a finite compact restriction

Worker 189. The theorem `Langlands.compactRestrictionFixedVectorDetection`
proves `Langlands.CompactRestrictionFixedVectorDetectionStatement` with
independent group, carrier, and finite-family index universes.

For the supplied irreducible compact subrepresentations of `D|N`, form the
finite set `t` of their compact-coefficient isomorphism classes. The
published conjugation theorem makes `t` stable under ambient conjugation:
the inclusions of those subrepresentations are injective and their
underlying submodules span `D|N`.

The topological assumptions on `N` give compact open subgroups cofinal
among its open subgroups. The published compact-coefficient complement
theorem then supplies the intrinsic isotypic/annihilator complements for
every class and every smooth object of `N`. Thus `selectedBlockPair`
constructs an actual ambient invariant annihilator `Q` inside `A`. Its
underlying submodule is the common annihilator of all the classes in `t`
on `A|N`.

Suppose every `K`-fixed vector of `D` is zero. Take `v ∈ A^K`. Every
`N`-intertwiner from `A|N` to a chosen irreducible member sends `v` to a
vector fixed by `K.comap N.subtype`, since `K ≤ N`. The inclusion into
`D|N` therefore sends that vector to `D^K`, so it is zero. Injectivity of
the inclusion shows that the original image was zero. The representative
formula for intrinsic annihilators now puts `v` in every selected
annihilator, hence in `Q`.

The ambient generation hypothesis forces `Q = ⊤`. On the other hand, the
published `selectedBlockPair_not_isSubquotient` excludes `D` as a
subquotient of the actual representation on `Q`, using any index in the
nonempty family. The supplied subquotient presentation of `D` in `A`
becomes a presentation in `Q` by restricting the codomain of its
injective map; `Q = ⊤` justifies that restriction. This is a contradiction.

The mathematical provenance is the supercuspidal detection argument in
Renard VI.6.3, printed pages 178–179 / PDF184–185, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof uses the published compact-coefficient selected-block
construction in place of assuming the source's inertial decomposition.
The finite compact restriction remains an explicit input; the theorem
does not realize it for reductive rational points or prove Howe's theorem.
