# Statement: uniqueness of compact real semisimple forms

`Langlands.GroupScheme.RealCompactFormUniquenessStatement : Prop` says
that two semisimple group schemes over ℝ with compact full real point sets
are isomorphic over ℝ whenever their base changes to ℂ are isomorphic over
ℂ. This module states the assertion and supplies no proof. It has no
universe parameters.

Both hypotheses `HasCompactRealPoints` use the actual real coefficient
points in the canonical regular-evaluation topology from
`Rational.RealCompactPoints`. Both isomorphisms in the statement are group
scheme isomorphisms. The conclusion does not require compatibility with
the supplied isomorphism after complexification.

Source: Armand Borel, *Lie Groups and Linear Algebraic Groups, I. Complex
and Real Groups*, retained Hong Kong lecture notes (2000–2001), source ID
`borel-lie-groups-linear-algebraic-groups-2000`, Section 5.6, printed p.40
(one-based PDF p.40). Borel states that any two compact real forms of a
connected complex reductive group are conjugate by an inner automorphism.
Section 5.7 on the same page discusses the algebraic structure on the
complexification of a compact form.

Provenance: derived. Use the given complexification isomorphism to regard
the two compact forms as forms of a common connected complex semisimple
group. Inner conjugacy gives an isomorphism of the real forms; the
statement retains only the existence of that isomorphism, which is weaker
than specifying an inner conjugator. The source's usual topology on real
points is encoded by regular-function evaluations. Passing from point
conjugacy to an actual real group scheme isomorphism remains part of the
future proof; an abstract or continuous isomorphism of point groups alone
does not prove this statement.

This statement does not assume compact real-form existence.
