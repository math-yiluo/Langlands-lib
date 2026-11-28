# The Steinberg presentation and its torus-defect quotient

Robert Steinberg, *Lectures on Chevalley Groups*, AMS 2016, is registered
as `steinberg-2016-lectures-chevalley-groups`. The PDF SHA-256 is
`e3f9ab93111dd88ff3d944a951f4d39b7e08539f6a9b57f22fba0d9bbc19eb89`.
Chapter 3, Lemma 15 and its corollary (printed pp. 19–20, PDF pp. 32–33)
give the commutator convention and the ordered product. Chapter 6,
Theorem 8 and the construction preceding Lemma 36 (printed p. 43,
PDF p. 56), give the relations for \(G'\). The proof of Theorem 8(b)
and the definition before Lemma 39 (printed p. 45, PDF p. 58)
give the presentation \(G''\) and the torus defect, respectively.

## Input and words

All declarations are in `Langlands.Covering.BrylinskiDeligne`. For a type
of root indices, `SteinbergPresentationData` supplies an involution
\(\alpha\mapsto-\alpha\), a choice of rank branch and a list
`commutatorTerms` for each pair \((\alpha,\beta)\) with \(\beta\ne-\alpha\).
For data from a root system, the index \(\gamma\) of each `SteinbergCommTerm`
labels the root \(i\alpha+j\beta\), and the coefficient \(c\) is the integer
for that term in the chosen order from Lemma 15. The index, the two positive
exponents and the integer coefficient are available as fields of the term.
`SteinbergCommTerm.parameter` gives \((c:F)t^iu^j\), and
`commutatorProduct` evaluates the factors in list order.

Over any field \(F\), the free generator `freeRootGenerator` is indexed by
\((\alpha,t)\) for \(t\in F\). Given any group and a family \(x_\alpha(t)\) in it,
`weylWord`, `torusWord` and `torusDefectWord` evaluate the following
words for \(a,b\in F^\times\).

\[
\begin{aligned}
w_\alpha(a)&=x_\alpha(a)x_{-\alpha}(-a^{-1})x_\alpha(a),\\
h_\alpha(a)&=w_\alpha(a)w_\alpha(-1),\\
d_\alpha(a,b)&=h_\alpha(a)h_\alpha(b)h_\alpha(ab)^{-1}.
\end{aligned}
\]

## Relations and evaluation

Each equation \(L=R\) contributes the free-group relator \(LR^{-1}\).
In both rank branches `additiveRelations` imposes (A),
\(x_\alpha(s)x_\alpha(t)=x_\alpha(s+t)\).
The other family in `steinbergRelations` is selected by `SteinbergRank`.

- In rank one, `rankOneRelations` imposes (B′),
  \(w_\alpha(a)x_\alpha(u)w_\alpha(-a)=x_{-\alpha}(-a^{-2}u)\)
  for \(a\in F^\times\), \(u\in F\).
- In rank at least two, `commutatorRelations` imposes (B) for
  \(\beta\ne-\alpha\) and \(t,u\in F\).
  Here \([A,B]=ABA^{-1}B^{-1}\), and
  \([x_\alpha(t),x_\beta(u)]=\prod x_\gamma((c:F)t^iu^j)\)
  uses the supplied ordered list. An empty list gives the identity.

`SteinbergGroup` is Mathlib's `PresentedGroup` for `steinbergRelations`.
It realizes \(G'\) of Chapter 6 for the root data in Steinberg's
orthogonally indecomposable case.
`torusRelations` is the set of all free words \(d_\alpha(a,b)\).
`TorusDefectQuotient` presents \(G''\) by adjoining that set to
`steinbergRelations`, which imposes (C),
\(h_\alpha(a)h_\alpha(b)=h_\alpha(ab)\).
Both constructions take the abstract presentation data over \(F\).
Identification with a group of rational points, centrality and
universality of the projection are separate mathematical assertions.

Each group exposes `rootGenerator`, `weylWord` and `torusWord`.
`SteinbergGroup.torusDefect` is \(d_\alpha(a,b)\) evaluated at the
Steinberg group generators. `SteinbergGroup.toTorusDefectQuotient`
is induced by the identity on the free group, so it is surjective and
sends each root generator to its counterpart. Its kernel is the normal
closure of the Steinberg group torus defects. The kernel proof takes
the image of the normal closure of the enlarged relation set in the
first presentation. The first presentation kills the original relators,
and the image of the added relators is the set of torus defects.

`SatisfiesSteinbergRelations` and `SatisfiesTorusRelations` express the
generator equations in a target group. The free lift sends each relator
to the corresponding left side times the inverse of the right side.
The lemmas `lift_eq_one_iff_steinberg` and `lift_eq_one_iff_torus` use
this calculation to descend evaluation by `PresentedGroup.toGroup`.
For each presentation, `evaluate_rootGenerator` identifies its value on
the generators, and `hom_ext` gives uniqueness. Evaluation of the
torus-defect quotient composed with the projection agrees with Steinberg
evaluation.
