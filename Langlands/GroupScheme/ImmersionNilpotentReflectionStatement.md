# Reflection of immersions across a nilpotent thickening

`Langlands.GroupScheme.ImmersionNilpotentReflectionStatement.{u}` is a
`Prop`-valued statement definition, with no proof or additional axiom.

For every commutative ring `A : Type u`, nilpotent ideal `J`, schemes `X, Y` over
`Spec A`, and morphism `f : X ⟶ Y` in the over category, it asserts that `f.left`
is an immersion if its pullback to `Spec (A/J)` is an immersion. The pullback is
Mathlib's actual `Over.pullback` along `Spec.algebraMap A (A ⧸ J)`. An immersion
means an embedding with locally closed range and surjective maps on stalks.
No flatness, finite-type, separatedness, or group-law hypothesis is imposed.
The namespace places this prerequisite near its group-scheme consumer; the
quantified objects themselves are arbitrary schemes over the affine base.

## Source and rationale

A. Grothendieck, SGA 3, Exposé IX, *Groupes de type multiplicatif : homomorphismes
dans un schéma en groupes*, Gille–Polo recomposed annotated edition, version
8 November 2009, registered as `sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`, proof of
Theorem 3.6 bis (a), recomposed pp.39–40 (original margins 49–50), uses precisely
this reflection step for a group homomorphism. Its explanation uses the unchanged
underlying topological spaces and surjectivity on local rings after reduction.

This statement isolates that scheme-theoretic step for arbitrary over-scheme
morphisms. Removing the group laws is an internal generalization: they play no
role in the topological or local-ring argument. The nilpotent closed immersions
of `X` and `Y` induced from the base are homeomorphisms, so the underlying map of
`f` is a locally closed embedding if and only if its reduction is. For a stalk map,
surjectivity modulo the ideal from `J` says that its cokernel `C` satisfies
`C = JC`; nilpotence then gives `C = 0`. The base-ring action is compatible with
the stalk map because `f` is a morphism over `Spec A`. This explains why flatness
is unnecessary. It is a rationale for the statement, not a formal proof here.
