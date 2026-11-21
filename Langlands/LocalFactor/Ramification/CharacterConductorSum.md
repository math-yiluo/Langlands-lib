# Sums over the characters of a finite abelian quotient

The characters of a finite abelian group that are trivial on a subgroup
form the dual subgroup. Their number is the index of the subgroup. For an
element of the subgroup each value is one. For an element outside it,
finite abelian duality provides a character in the dual subgroup whose
value there differs from one. Translation by that character permutes the
summands and multiplies their sum by its value, forcing the sum to vanish.

The second lemma applies this character orthogonality to a weighted sum of
rank-one trace deficits. It is independent of the weights. In the local
conductor application, the weights count the lower ramification groups
containing the given element.

`sum_artinConductor_twists_trivial_on` applies the weighted identity to the
Library's class-function expression for the Artin conductor. The lower
group membership test for a subgroup action is the restriction of the
original test. The class sum on the subgroup is consequently the Artin
conductor of the restricted character times the cardinality of subgroup
inertia. The other contribution is the sum of the conductors of the
quotient characters. The proof casts to complex numbers for the character
values and uses injectivity of the rational cast to recover the rational
Artin conductor identity.

For the quotient characters alone, the weight sum off the subgroup is
`∑ (|G_i| - |H_i|)`. The Lean proof counts pairs consisting of an element
and a lower index containing it in both orders, once in the ambient group
and once in the subgroup. This is the finite group part of the
conductor-discriminant comparison.
