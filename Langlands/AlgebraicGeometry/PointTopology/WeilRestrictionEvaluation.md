# Original Weil counits on arbitrary compatible coefficient tests

This is a derived algebraic interface for the compatibility step of
Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
Example 4.2, printed pp.9–10. It uses the existing actual glued Weil model
and its original representing comparison. No topology or new
representability assertion is introduced.

Let A and B be commutative rings, with B an A-algebra. Let R be a lower
A-algebra and D an upper B-algebra. A ring map f from R to D is compatible
when its composition with the A-action on R equals the composition of the
B-action on D with the original A-to-B map.
`weilRestrictionEvaluationTest` is the actual map from Spec D to the
pullback of Spec R along Spec B to Spec A. Its two projections are the
spectrum of f and the original structure map to Spec B. The construction
uses the universal property of that pullback. Its first-projection theorem
retains exactly the specified f.

Assume B is finite and projective over A, and Y is an actual locally
finite-type B-scheme. `weilRestrictionEvaluation` composes this test map
with the existing `affineChartWeilRestrictionComparison` counit for a
point of the actual glued Weil scheme over R. It is an actual Y-point
over D. This construction does not require Y to be affine, quasi-compact
or separated.

The lower naturality theorems compare compatible tests for a specified
A-algebra map from R to R'. They prove that extending a lower Weil point
to R' and evaluating with f' gives its original evaluation with f when
f' composed with that map equals f. The upper naturality theorems prove
that extending an evaluated Y-point along a specified B-algebra map from
D to D' gives evaluation with f' when that map composed with f equals f'.
Both test-map identities follow from equality of their two pullback
projections. The point identities then use the original comparison's
naturality and associativity.

Finally, suppose the original completed-tensor data identify C tensor_A B
with a product of original upper coefficient rings D_i, with the original
B-coefficient formula. For a specified A-algebra map from R to C, and a
compatible original f from R to one factor D_i, assume that composing that
map with the original C-action on D_i gives f. The two
`completedTensorWeilRestriction..._eq_evaluation` theorems identify the
existing factor test and local counit after coefficient restriction with
the canonical evaluation on the original whole R. The proof compares
first projections using the existing factor test theorem and the stated
ring-map equality; the second projections agree because the maps are
over Spec B. Naturality of the original counit completes the point proof.

All rings and schemes share an arbitrary universe. These identities allow
adelic support compatibility to be proved using literal coefficient maps
without identifying changing tensor-factor indices. Their arithmetic
specializations and the full adelic comparison remain host obligations.
