# Compositum degrees for auxiliary quadratic fields

This module gives internal algebraic support and a conditional construction for
`SplitAuxiliaryQuadraticsStatement`. It does not prove the two arithmetic
prerequisites.

`rationalFieldImage K C` is the actual image of the canonical embedding of a
characteristic-zero field `K` into a characteristic-zero extension `C`, regarded
as a rational intermediate field. Both fields may lie in the same arbitrary
universe. This image is used to perform compositum calculations with the actual
supplied copy of `K`.

For a rational square root that remains nonsquare in a finite rational
intermediate field, `squareRoot_sup_finrank` proves that adjoining its rational
root field doubles the rational degree. It uses the square-root minimal
polynomial and the dimension formula for a tower.

`quadraticTower_linearDisjoint` proves that two rational quadratic fields are
linearly disjoint, and their compositum is linearly disjoint from a third finite
rational intermediate field, when adjoining them successively multiplies the
third field's rational degree by four. The proof uses the upper bound for
compositum dimensions, positivity of the third field's degree, and the dimension
criterion for linear disjointness.

`splitAuxiliaryQuadratics_of_prerequisites` proves the existing
`SplitAuxiliaryQuadraticsStatement.{u}` from the conjunction
`SplitQuadraticPrerequisitesStatement.{u}`. For a supplied prime `p` and totally
real number field `K : Type u`, put `C = AlgebraicClosure K` and let `B` be the
canonical rational image of `K` in `C`. The canonical rational algebra
equivalence `K ≃ₐ[ℚ] B` proves that `B` is a number field.

The signed square-class supply first gives a positive rational `d` that is a
square in `Padic p` and remains a nonsquare in `B`. An algebraic-closure root
`x` defines the actual intermediate field `R = ℚ⟮x⟯`. It has rational degree
two, is totally real, and its compositum with `B` has degree twice the degree
of `B`. Apply the same supply to the number field `M = B ⊔ R`, choosing a
negative rational `a` that is a square in `Padic p` and remains a nonsquare in
`M`. A root `y` in the same `C` defines `I = ℚ⟮y⟯`, of rational degree two
and totally complex.

The second nonsquareness condition gives
`[M ⊔ I : ℚ] = 4 * [B : ℚ]`. The compositum upper bounds then force
`[I ⊔ R : ℚ] = 4`. The dimension criterion proves both `I.LinearDisjoint R`
and `(I ⊔ R).LinearDisjoint B`. Mathlib's invariance under rational algebra
equivalence transports the latter to the original supplied `K`, with its
canonical embedding into `C`. Thus the conclusion concerns the actual common
ambient algebraic closure and the supplied copy of `K`.

For each of `I` and `R`, local squareness gives two distinct rational algebra
embeddings into `Padic p` by `rationalRootField_two_embeddings`. The second
arithmetic prerequisite then supplies the unchanged
`HasSplitQuadraticPrime p` predicate: exactly two distinct actual height-one
primes of the ring of integers containing `p`, exhaustion of all such primes,
and ring equivalences from their actual adic completions to `Padic p` that are
continuous in both directions. This module uses that full prerequisite rather
than proving the local comparison. There is no restriction excluding `p = 2`,
and the universe parameter is retained.

The construction does not use total reality of `K` beyond accepting the
existing target's input; the stronger generic signed supply permits the same
degree argument for any number field. The root fields' own signatures are
proved from the strict signs.

The source motivation is Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Inventiones Mathematicae 139 (2000),
Section 3.3, printed p.449, second paragraph (PDF page 11), registered as
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
That paragraph chooses split imaginary and real quadratic fields whose
compositum is linearly disjoint from the previously constructed totally real
field. The image definition, compositum lemmas, and conditional assembly here
are an internal derived implementation of that choice, not statements quoted
literally from Henniart. Proving the two generic arithmetic inputs and then
applying this conditional theorem remains necessary to prove the unconditional
Library target.
