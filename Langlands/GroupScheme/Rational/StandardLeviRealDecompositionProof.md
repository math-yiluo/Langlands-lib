# Proof of the corrected standard Levi real decompositions

Worker 624, Task 6348. The theorem
`Langlands.GroupScheme.standardLeviRealDecomposition.{u}` has type exactly
`Langlands.GroupScheme.StandardLeviRealDecompositionStatement.{u}` from the
unchanged module `Langlands.GroupScheme.Rational.RelativeRealCorootStatements`.
The proof covers every field, connected reductive group scheme, maximal split
torus, generic cocharacter and supplied integral reflection data in that target.
It includes the empty and nonreduced relative-root cases.

The source interpretation and correction of Renard V.3.13 are those of the
[published statement](RelativeRealCorootStatements.md), especially its section
“Source issue I4 and its correction”: the Levi pieces are intersections with
the larger root or coroot span and are spanned by projected generators. The
registered source there is David Renard, *Représentations des groupes réductifs
p-adiques*, version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, V.3.13, printed
pp.112–113 / PDF pp.118–119. This module supplies an internal derived proof of
that existing target; its route is the following linear algebra.

The proof uses the published full real spaces `Vstar T` and `V T`, their pairing
`pair T`, its perfectness for a split torus, and finite dimension of its character
space. Finiteness of the actual relative Weyl group permits the existing averaged
form `relativeWeylInvariantForm`, whose symmetry, positivity and invariance are
already proved in `RealTorusInvariantForm`.

For a set `J` of actual roots, `StandardLevi.corootAnnihilator_eq_leftAnn` identifies
its coroot annihilator with the left annihilator of the span of its real coroots.
`StandardLevi.rootAnnihilator_eq_rightAnn` identifies its root annihilator with
the right annihilator of the real root span. These are direct consequences of
the defining equations and the universal property of span. The published
`corootAnnihilator_eq_orthogonal` identifies the first annihilator with the
orthogonal of the root span under the positive invariant form. The helper
`Langlands.LinearAlgebra.isCompl_orthogonal_of_positive`, followed by
`IsCompl.symm`, gives the character-side complement.
Double annihilation and duality transport it to the cocharacter-side complement.
The two disjointness statements make both kernels of the restricted pairing
zero, so that pairing is perfect. This is `StandardLevi.complements`; it works
for every subset of the actual roots without requiring linear independence.

`StandardLevi.simpleRootSpan_eq` starts with the published rational spanning
lemma `ratSpan_simpleRelativeRoots_eq_relativeRootSpan`. Its negation-stability
premise follows from the published actual normalizer element negating each
root and stability of the root set under that element. The published
`map_ratSpan_baseChange` and `map_relativeRootSpan_baseChange` extend this span
equality to the real spaces. Consequently the simple-root annihilator is the
common root annihilator `relativeCentralDirections i`.

For the full simple set, the published `relativeCharacterRootComplement` gives
another complement of the full root span: the range of restricted real rational
characters of the group. The published `restrictedCharacter_coroot` puts this
range inside the simple-coroot annihilator. Comparable complements of the same
subspace are equal, by the modular-lattice identity used in
`StandardLevi.full_simple`. Double annihilation then identifies the span of the
simple coroots with the cocharacter annihilator of that character range. These
are the first three clauses of the target.

For `J ⊆ K`, the annihilator for `K` lies in that for `J`. Applying
`nested_complement` to the complement for `K` proves disjointness and the sum
equality with the intersection defining the Levi piece. Applying
`projected_span` to the complement for `J` proves the spanning assertion by the
projected roots of `K ∖ J`. The same argument on cocharacters is indexed by
actual roots, with the map `D.realCoroot`; rewriting the image-set condition
recovers precisely `D.projectedCoroots J (K ∖ J)`.

The final orthogonality clauses quantify over every invariant product, including
products unrelated to the averaged one used to obtain complements. On characters,
the published orthogonal description of the coroot annihilator applies directly,
since the Levi piece lies in the root span of `K`. On cocharacters,
`StandardLevi.real_coreflection` derives

`v ↦ v - ⟨α, v⟩ • D.realCoroot α`

for the actual action of `D.representative α`. It uses the published character
reflection formula, simultaneous pairing invariance and perfectness. The
formula fixes any vector annihilated by `α` and negates its coroot, since
`⟨α, D.realCoroot α⟩ = 2`. Invariance of any cocharacter inner product therefore
forces the pairing of such a vector with that coroot to vanish. Extension over
the coroot span proves `StandardLevi.cocharacter_orthogonal` and the last clause.

`StandardLevi.nested` assembles the nested clauses, and the final theorem
combines it with `StandardLevi.full_simple`. The auxiliary abstract lemmas are
in [StandardLeviLinearAlgebra](StandardLeviLinearAlgebra.md). The proof uses the
published character/root complement and rational spanning results directly;
it does not assume any of the sibling real-coroot, real-basis or fundamental-weight
targets. It asserts no separate existence of reflection data or geometric
identification of split components beyond the scope of the named target.
