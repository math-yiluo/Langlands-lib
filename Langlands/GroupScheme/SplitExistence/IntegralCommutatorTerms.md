# Integral monomial parameters for Chevalley commutators

Module `Langlands.GroupScheme.SplitExistence.IntegralCommutatorTerms`.

`CommutatorTerm P α β` records a root `γ`, positive natural exponents `i, j`
with `γ = iα + jβ`, and an integer coefficient `c`. Its `parameter` over a
commutative ring is `c s^i t^j`. `IntegralCommutator` packages a list of such
terms with an integral height positive on the two input roots. The list has
distinct roots and nondecreasing height. Its matrix identity over
`ℤ[t][s]` uses the commutator convention `xyx⁻¹y⁻¹`. The outer polynomial
variable is `s`, and the inner one is `t`.

`ChevalleyLieData.commutatorExpansion` chooses this list for each nonopposite
pair of a finite reduced based root datum, using the root operators from
`toLieRootData`. For distinct roots, evaluating against the coroot
combination `(2 − ⟨α, β∨⟩) α∨ + (2 − ⟨β, α∨⟩) β∨` witnesses that a
positive height exists. This witness takes the common positive value
`4 − ⟨α, β∨⟩⟨β, α∨⟩` on the two roots. The definition chooses a height
positive on both roots and uses it to order the list. For an equal pair
the height is evaluation against the coroot, and the list is empty by
additivity of the divided-power exponential.
`IntegralCommutator.specialize` evaluates the identity in any commutative ring.

The proof of `LieRootData.exists_list_commutator_terms` starts with the
integral polynomial factorization in `LieRootData.exists_list_commutator_int`.
The bidegree `(a, b)` of a nonzero matrix coefficient forces the weight
difference of its entry to be `aα + bβ`. Divided powers have this weight
property for each monomial input, and matrix multiplication preserves it by
coefficient convolution. In an entry where the first root operator has a
nonzero coefficient, `LieRootData.prod_cons_apply` isolates that operator
times the first parameter. Since distinct nonopposite roots are linearly
independent, the parameter is supported at a single bidegree. Multiplying
by the inverse of this first factor preserves the weight property and
allows the argument to continue down the list.

The monomial product and weight grading come from Robert Steinberg,
*Lectures on Chevalley Groups*, AMS 2016, Chapter 3, Lemma 15 and its
corollary, printed pp. 19–20 (PDF pp. 32–33). The construction uses the
divided-power matrix representation and a positive height order.
Literature ID `steinberg-2016-lectures-chevalley-groups`, SHA-256
`e3f9ab93111dd88ff3d944a951f4d39b7e08539f6a9b57f22fba0d9bbc19eb89`.
