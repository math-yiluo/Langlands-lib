# Homomorphisms into complete-local deformations of multiplicative-type groups

This module proves the unchanged
published `MultiplicativeTypeCompleteLocalDeformationStatement` in every
universe, with exactly its stated hypotheses. No target or imported Library statement is changed.

Let `A` be complete local noetherian, `G` affine, locally of finite type and
flat with multiplicative-type special fibre, and `H` split by a finite etale
surjective cover. First choose a finite etale local extension `B` of `A`
that splits both `H_B` and the actual special fibre of `G_B`. This extension
is faithfully flat, noetherian and complete.

On each quotient of `B` by a power of its maximal ideal, the target becomes
diagonalizable by nilpotent deformation of its special fibre. Character
duality over local rings makes every successive Hom restriction bijective.
Recursion constructs compatible formal maps, and the split adic comparison
algebraizes them uniquely. Comparing the first quotient with the actual
residue fibre gives special-fibre Hom bijectivity over `B`.

For a prescribed special-fibre map over `A`, lift its transport over `B`.
The two pullbacks to `B` tensor `B` agree modulo the extension of the maximal
ideal of `B`. This quotient of the target is diagonalizable. Rigidity over
finite algebras over a noetherian local base makes the pullbacks equal.
Fpqc Hom descent gives a global map, and faithfulness over the residue-field
extension identifies its special fibre with the prescribed one. Equality
of two lifts is checked over `B` using split-case uniqueness and then fpqc
faithfulness. Surjectivity and injectivity give the required unique lift.

For the second clause, the separate special-isomorphism immersion theorem
constructs a surjective coordinate map with idempotent-generated kernel over
a local splitting cover and descends the resulting open and closed immersion.
This criterion needs no target flatness or special-fibre multiplicative-type
assumption, so it applies under the full statement's hypotheses.

The implemented proof combines these actual group-scheme comparisons; it
does not replace group morphisms by rational points. The source comparison
is Conrad, *Reductive group schemes* (2014), Theorem B.3.2(2), pp.288-290;
the implemented immersion proof uses the coordinate criterion rather than
the formal-completion argument of the source. Split adic effectivity is
provided by the separate SGA 3 IX 7.1 comparison.
