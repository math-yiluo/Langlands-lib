# Identity evaluation determines a complex Whittaker intertwiner

`ComplexLocalIntertwinerEvaluationStatement` compares two complex-linear maps
`B` and `B'` on the same `U(r+1)`-finite complex standard module for a list
`ds` of character data. Each is a Library `IsComplexWhittakerIntertwiner`
for the same character parameter `a : ℂˣ`. If `B f 1 = B' f 1` for every
standard vector `f`, then `B = B'`. The pointwise formulation
`complexWhittakerIntertwiner_eq_of_eval_one` proves the implication, and
`complexLocalIntertwinerEvaluation` packages it for every `r`, `ds`, and `a`.

## Provenance and scope

This is an internal uniqueness step for comparing two ways of producing
coefficients in the compact averaging argument of H. Jacquet, *Archimedean
Rankin–Selberg Integrals* (2009), §4.7 and Proposition 4.4, printed/PDF
pp. 30–31 in the [registered author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
There Jacquet computes with coefficients of continuous linear forms on the
smooth induced representation. The Library intertwiners are maps on its
compact-finite standard module; that module need not be invariant under a
noncompact one-parameter subgroup. The lemma uses the infinitesimal action and
real analyticity instead of assuming an action of the full group on its source.
It does not establish proportionality of the identity evaluations or supply
a compact averaging identity, and does not prove a functional equation.

## Lean proof

First work with two families of smooth functions on `GL_n(ℂ)`, indexed by the
same type. Assume their extensions are real analytic on the open invertible
matrix locus and that right differentiation in a real matrix direction `X`
acts on both families by the same map `D X` on indices.

* The matrix exponential is always invertible. Along the real curve
  `t ↦ exp (t • X)`, its derivative is `exp (t • X) * X`.
  The chart formula for the right derivative and the chain rule thus identify
  the derivative of a coefficient on this curve with the coefficient indexed
  by `D X`, evaluated on the same curve. The restricted coefficient is real
  analytic there by composition with the matrix exponential.
* Induction on derivative order moves each derivative onto the shared
  indexing action. Since the curves start at the identity, the assumed
  equality of evaluations yields equality of all derivatives there.
  On a common neighborhood the real Taylor series sum to the two functions
  and have the same terms. The real analytic identity theorem on `ℝ`
  then gives equality along the entire curve. Varying `X` gives equality on
  the image of the matrix exponential.
* The exponential has strict derivative the identity at zero. The inverse
  function theorem sends the neighborhood filter there to the neighborhood
  filter of the identity matrix, so the extensions agree near the identity.
  Apply the analytic identity theorem again, this time on the preconnected
  invertible matrix locus, and restrict the extensions back to group elements.

For the Whittaker specialization, `D X` is the standard enveloping algebra
action of the real generator `realGenerator (r + 1) X`. It yields another
standard vector and computes its right derivative by `realGenerator_action`.
The intertwining hypotheses transport it to both images, and
`analyticOnNhd_unitsExtension_complexWhittaker` supplies their analyticity.
Thus the general family comparison applies, and linear map extensionality
identifies `B` and `B'`.
