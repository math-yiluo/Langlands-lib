# Continuous Galois representations and the two polynomial conventions

Author: Worker 41. This pair supplies definitions and their intrinsic construction
proofs for compatible families. The automorphic existence theorems remain
separate obligations.

`Langlands.GaloisRepresentation.Objects K L` consists of actual finite-dimensional
representations of Mathlib's `Field.absoluteGaloisGroup K` over the specified
topological coefficient field `L`. The absolute Galois group has its Krull topology.
The published `Langlands.FiniteRepresentation` supplies the actual vector space
and action; continuity is the continuity of the group-variable map into its
endomorphisms, given `moduleTopology L`. In the lambda-adic specialization,
`L` is the actual finite-place completion of a coefficient number field, with
its completion topology. No discrete or complex coefficient topology and no
open-kernel condition replaces that topology. Semisimplicity, purity and
geometric origin are separate conditions.

`Classes` reuses the published genuine quotient by invertible linear
intertwiners. There is no new surrogate equivalence relation.
Coefficient, base-field and carrier universes are independent.

For an element `g` of the actual Galois group, `characteristicPolynomial` is
the monic characteristic polynomial of its action. `eulerPolynomial` is its
reverse. The intrinsic proofs establish monicity, rank as both polynomial
degrees, constant Euler coefficient one, and, in every finite basis `b`,

`eulerPolynomial A g = det(1 - T * matrix_b(A(g)))`.

The last identity uses Mathlib's proved characteristic-polynomial
basis independence and matrix reversal identity. It is the normalization
bridge between eigenvalues as roots of the monic polynomial and reciprocal
roots of the Euler polynomial. The action of `g` is a unit, with inverse the
action of `g` inverse. Its negative has nonzero determinant; evaluating the
characteristic polynomial at zero therefore gives a nonzero constant
coefficient. The reversal degree formula now proves degree preservation.
Applying polynomial reflection twice proves `reverse_eulerPolynomial`:
reversing the Euler polynomial gives the original characteristic polynomial,
including in rank zero. An actual representation equivalence
conjugates the action operators, so their characteristic and Euler polynomials
agree. This proves that `classEulerPolynomial` is well-defined on the quotient.

`pullback` composes with Mathlib's continuous map on actual absolute Galois
groups associated to an embedding of fields. This map uses a choice of
embedding of their algebraic closures; no strict functoriality or independence
of that choice is asserted here. `atFinitePlace` applies it to the actual
number-field completion embedding. The two pullback polynomial formulas hold
by construction, and continuity follows by composition.

These definitions give polynomials for any actual Galois element. The paired
`CompatibleFamily` module defines inertia and the geometric-lift condition,
and proves lift independence under unramifiedness. Existence of these lifts
is an arithmetic proof obligation.
Compatibility across coefficient places, finite exceptional sets, purity,
weak automorphic association and ramified local compatibility remain distinct
propositions. No compatible-family existence conclusion is assumed here.

## Source and dependency boundary

Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*
(1998), Section 1, printed pp.183–184, uses genuine finite-dimensional
lambda-adic Galois representations and the convention
`det(1 - rho(Frob_v) T)` for geometric Frobenius. The source also allows a
finite excluded set of coefficient places; this pair does not yet construct
or constrain a collection of representations.
The original pages were reread for this implementation.
Literature ID: `harris-1998-local-langlands`; SHA256:
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

The reusable representation and adelic names were read in the current Library
at commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`:
`Langlands.Weil.Representation.Basic` and `Langlands.Global.Adelic`.
The complex-only predicates in `Langlands.Weil.Representation.Predicates`
are not used for lambda-adic continuity. This pair adds the coefficient-field
specialization without changing those published declarations.

Intrinsic constructions use pinned Mathlib's `AbsoluteGaloisGroup`,
`NumberField.Completion.FinitePlace`, `ModuleTopology`,
`Charpoly.ToMatrix` and `Matrix.Charpoly.Coeff`.
Environment: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Native compilation and the exact Lake check of the paired compatible-family
module succeeded with no diagnostics. These author checks do not constitute
independent semantic review or publication.

The exported construction names, all in `Langlands.GaloisRepresentation`, are:

| Declarations | Mathematical role |
| --- | --- |
| `IsContinuous`, `Objects`, `Classes`, `LambdaAdic` | Actual continuous finite representations, their isomorphism quotient and coefficient-completion specialization |
| `characteristicPolynomial`, `eulerPolynomial`, `classEulerPolynomial` | Monic and Euler conventions, including descent through representation isomorphism |
| `characteristicPolynomial_monic`, `characteristicPolynomial_natDegree`, `characteristicPolynomial_coeff_zero_ne` | Monicity, dimension and invertibility consequences |
| `eulerPolynomial_coeff_zero`, `eulerPolynomial_natDegree`, `reverse_eulerPolynomial`, `eulerPolynomial_eq_det` | Exact determinant normalization and reversal laws |
| `characteristicPolynomial_eq_of_equiv`, `eulerPolynomial_eq_of_equiv` | Polynomial invariance under linear intertwiners |
| `pullback`, `atFinitePlace`, `characteristicPolynomial_pullback`, `eulerPolynomial_pullback` | Continuous restriction through actual field embeddings and its polynomial formulas |
