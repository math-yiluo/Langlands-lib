# The weak constant term along the whole group

Let `fam` be a standard parabolic family for a connected reductive group over a number field. Its
full index `fam.top` contains every simple relative root. `isWeakConstantTerm_top_of_unitary`
identifies an automorphic form `φ` on `G(F) \ G(𝔸)` with its weak constant term at `fam.top`
when it transforms through a unitary character of the canonical positive split centre of `G`.
`isWeakConstantTerm_top` applies the same result to a logarithmically square-integrable
form using the unitary character in `IsLogSquareIntegrableAutomorphicForm`.

The full parabolic and its Levi represent the full subgroup functor by `standardParabolicEndpoints`.
Their maps to `G` therefore give isomorphisms. Transporting the top split component across the
Levi isomorphism and using `RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup` identifies
its positive image in `G(𝔸)` with the canonical positive split centre. The top unipotent
radical has trivial image, and Levi rational points map to rational points of `G`. These facts
supply the left invariance of the single exponent component in the parabolic quotient.

The ordinary constant term is the identity by `constantTerm_top`. The half modulus vanishes by
`connectedReductiveAdjointDeterminant` on the full parabolic. Pull the real character parameter
back to the full parabolic and take its imaginary image. The unitary transformation law gives
the polynomial orbit condition with degree zero, and the real part of the exponent is zero.
The singleton decomposition with component `φ` thus has weak sum `φ`.

Source. P. Delorme, *On the spectral theorem of Langlands*, published PDF in the registered
`delorme-2023-spectral-theorem-langlands` collection, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`. See (3.2) on p.10,
Definition 3.7 on p.13 and the last step of Lemma 3.10 (ii) on p.16.
