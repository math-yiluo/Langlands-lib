# Restriction, twisting and nonemptiness of simple characters

`simpleCharacterRestrictionTheorem` proves
`SimpleCharacterRestrictionStatement` in independent universes for the field
and vector space. The sources are Bushnell and Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), (3.2.4)–(3.2.5) and
(3.3.18)–(3.3.21), printed pp. 99–100 and 112–114.

Write \(n\) for the stratum level, \(r\) for the finite critical depth, and
\(d=\lfloor r/2\rfloor\). The restriction maps are between character indices
in the range \(0\le m<n\).

1. At \(m\ge\lfloor n/2\rfloor\), the recursive lattice formulas give the
   absolute unit subgroup. The trace formula defines a homomorphism there.
   Conjugation by relative endomorphism units preserves its values on the
   overlap, so the determinant criterion gives the required factorization.
   Induction along the defining sequence establishes membership and the
   defining conditions identify every member with this trace character.
2. For a nonscalar parameter and \(m\le d\), the group-properties theorem
   writes the domain as the product of a relative unit subgroup and the
   cutoff domain. Extend the determinant character on the image of their
   intersection to \(F[\beta]^\times\) using divisibility of
   \(\mathbb C^\times\). Agreement on the intersection and invariance of the
   deeper character under the relative units give a character on the product.
   The relative order normalizer preserves the domain and acts on its two
   factors, preserving the relative determinant on the first and the deeper
   character on the second. This gives the normalization needed for the
   recursive membership condition and hence surjectivity onto the simple
   characters at \(d\). The ratios of two lifts are exactly the
   determinant-factoring characters with trivial restriction.
3. For the chosen successor of the defining sequence, the high-layer formula
   identifies the domains and the recursive character condition gives forward
   twist membership. The conjugation formula on the common domain cancels the
   trace error for units centralizing the original parameter. The determinant
   criterion and the subgroup normalizer then give reverse membership. The
   equivalent-stratum formula compares the chosen successor with any critical
   approximation. Composing the twists gives the stated equivalence and its
   inverse trace factor.
4. Adjacent restriction with \(m+1\le d\) uses the same product argument.
   For \(m\ge d\) in a nonterminal step, restriction commutes with the twists
   for the two adjacent indices, so surjectivity follows by induction on
   the defining sequence. The perturbation is trivial at every index at or
   above \(r\) by the filtration bound. This gives the same restriction square
   when the adjacent indices reach or exceed \(r\), including the step from
   \(r-1\) to \(r\). In the terminal high case, both characters have the same
   trace formula.
5. The index \(n-1\) lies in the high-index range because \(n>0\).
   Surjectivity at adjacent indices gives a character at every lower index
   by descent.
