# Induction from a conjugate decomposition and standard Weyl classes

This internal adapter combines the published actual induction conjugation
isomorphism with the existing standard induced-Weyl class comparison. The group
is any locally compact nonarchimedean group in universe `uG`, and representation
carriers lie in `max uG uV`. The root-label universe `uI` is independent.

For actual decompositions `Q = L ⋉ V` and `P = M ⋉ U`, the three membership
hypotheses say that `P`, `M` and `U` are respectively the conjugates by `g` of
`Q`, `L` and `V`. Both radicals are closed. The published
`inductionConjugationIso` identifies normalized induction from `Q` with
inverse-conjugation pullback from `L` to `M` followed by normalized induction
from `P`. Its component sends a section `f` to `y ↦ f(g⁻¹*y)`.

`conjugateInduction_preservesFiniteLength` composes the published finite-length
preservation of equivalence pullback with finite-length preservation of
induction from `P`, then transfers it across this actual natural isomorphism.
`conjugateInduction_preservesShortExact` does the same for preservation of short
exact sequences of finite-length objects, using the pullback exactness theorem.
Neither lemma assumes the corresponding preservation property for `Q`.

`conjugateDecompositionInductionK0` is the actual normalized-induction map on exact
finite-length Grothendieck groups, using those transported preservation proofs.
These are the groups quotiented by all actual short-exact-sequence relations.
`conjugateDecompositionInductionK0_eq` identifies this map with `inductionK0` from `P`
composed with the actual `conjugationK0` map. It applies the published
`inductionK0_comp_conjugationK0` law.

Now fix a standard family indexed by finite subsets of a type, with
`ParabolicFiniteLength` for every member. Suppose `Q = M I ⋉ V` is conjugate
by an actual normalizer element `n` to the standard decomposition at `J`.
The Levi hypothesis is literally
`x ∈ M J ↔ n⁻¹*x*n ∈ M I`, as in the existing
`inducedClassWeylConjugacy` predicate. Under that predicate,
`conjugateDecompositionInductionK0_eq_of_weylConjugacy` proves that the constructed induction
map from `Q` equals standard induction at `I`. The proof converts the existing
class predicate to its equivalent map predicate by
`inducedK0WeylConjugacy_of_inducedClassWeylConjugacy` and applies it to this exact
normalizer lift. No enumeration or choice of representatives is involved.

`conjugateInductionClass_eq_of_weylConjugacy` states the same consequence on
actual finite-length inducing objects, allowing arbitrary finite-length proofs
for both outputs. Its proof first uses the actual induction-conjugation
isomorphism to identify the first class with standard induction at `J` of the
transported object, and then applies the supplied standard class comparison.
The transported finite-length proof comes from equivalence pullback.

This is derived solely from the named published conjugation, pullback,
isomorphic-object and exact-K0 laws. The adapter does not prove the standard
induced-Weyl predicate. It constructs no opposite parabolic or normalizer element
and proves no opposite-to-standard subgroup equality. Applied to an actual
opposite decomposition, those three subgroup equalities remain mathematical
prerequisites. There is no claim here of an isomorphism between induction from
`Q` and induction from the standard parabolic at `I`, nor of induction or Jacquet
duality or the closed rational-point contragredient commutation statement.
