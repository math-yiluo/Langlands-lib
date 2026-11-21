# Evaluation of joint multiplicity spaces

This is an internal linear-algebra construction for the admissibility argument in adelic block induction. It uses the Library's `jointMultiplicitySpace` and `IsJointlyAdmissible`; it is not a separate source statement.

Let `(ρ, κ)` act on a complex vector space `V` and `(ρ', κ')` on a coefficient space `W`. Fix a level `L` of the first finite group, a finite-dimensional compact test representation `σ`, and a homomorphism `j` from the coefficient compact group to the original compact group. For each index `i`, assume a linear evaluation `e i : V →ₗ[ℂ] W` that takes `L`-fixed vectors to vectors fixed by an open coefficient level `L' i` and intertwines the compact actions along `j`.

`jointMultiplicityEvaluation` maps an intertwiner `φ` to the family `e i ∘ₗ φ`. The finite-level hypothesis gives the required fixed-vector property, and compact equivariance follows by evaluating the intertwining law for `φ` at `j k`. Thus the target is the product of the coefficient multiplicity spaces with tests `σ.comp j` at the levels `L' i`.

In `jointMultiplicitySpace_finite_of_evaluations`, joint admissibility of the coefficient pair makes each target factor finite-dimensional. A finite index type makes their product finite-dimensional. The assumed zero-detection property makes the evaluation map injective by the kernel criterion, giving finiteness of the source. No Iwasawa factorization or separation by actual compact evaluations is asserted in this module; those are inputs to its use for induced sections.
