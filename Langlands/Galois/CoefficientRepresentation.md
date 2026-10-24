# Continuous Galois representations and the two polynomial conventions

Author: Worker 41. Documentation correction (Frobenius-lift status): Worker 282.
This pair supplies definitions and their intrinsic construction
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

These definitions give polynomials for any actual Galois element. This
module itself defines no Frobenius element and proves no lift existence. The
paired `CompatibleFamily` module defines the actual inertia kernel and the
condition `IsGeometricFrobeniusLift v g`: the inverse of `g` acts on the
residue closure by the residue-cardinality power. That is the geometric,
not the arithmetic, Frobenius direction. It proves lift independence under
unramifiedness: if `IsUnramifiedAt A v`, then
`eulerPolynomial (atFinitePlace v A)` takes the same value at any two such
lifts.

Existence of these lifts is proved in the separately published module
`Langlands.Galois.FrobeniusLift`. That module imports `CompatibleFamily`, and
through it this module; this module does not import it, so using its results
requires importing `Langlands.Galois.FrobeniusLift`. For every number
field `K` and every `v : Global.FinitePlace K`, its theorem
`Langlands.GaloisRepresentation.exists_geometricFrobeniusLift v` proves
`∃ g : LocalGroup v, IsGeometricFrobeniusLift v g`. Here `LocalGroup v` is
`Field.absoluteGaloisGroup (Global.FiniteCompletion K v)`, the group acting
in `atFinitePlace v A`. The same module defines
`Langlands.GaloisRepresentation.geometricFrobeniusLift v` by classical choice
from this existence proof. It is an arbitrary lift, not a canonical Galois
element. `frobeniusEulerPolynomial A v` is
`eulerPolynomial (atFinitePlace v A) (geometricFrobeniusLift v)`. It is
defined for every representation, but independence of the chosen lift is
proved only under `IsUnramifiedAt A v`. No lift independence is claimed for
ramified representations.

The global-to-local algebraic-closure choice enters only through
restriction. `atFinitePlace` uses `pullback`, hence
`Field.absoluteGaloisGroup.map`, which selects Mathlib's closure embedding
`IsAlgClosed.lift`. The lift `geometricFrobeniusLift v` does not use that
embedding. It is chosen in `LocalGroup v` using the action of that group on
the residue field of the algebraic closure of the completion itself. The
global embedding enters `frobeniusEulerPolynomial A v` only through
`atFinitePlace v A`.

This module proves no independence of the closure embedding. The separately
published module `Langlands.Galois.ClosureRestriction`, which imports
`CompatibleFamily` and is not imported here, proves it for representations.
Let `ι` be any closure embedding of type
`ClosureEmbedding (NumberField.FinitePlace.embedding v)`, that is, compatible
with the completion embedding. Then `atFinitePlaceAlongClosureEquiv`
constructs an actual intertwining equivalence from
`atFinitePlaceAlongClosure v ι A` to `atFinitePlace v A`.
`eulerPolynomial_atFinitePlaceAlongClosure_eq` gives equal Euler polynomials
at every element of `LocalGroup v`. `isUnramifiedAt_iff_alongClosure` and
`hasEulerPolynomialAt_iff_alongClosure` show that unramifiedness and
existential Euler matching do not depend on `ι`. These results keep the same
algebraic closure of the completion and the same residue-action model. The
restriction homomorphisms for different embeddings are not asserted equal,
and no canonical restriction homomorphism is constructed. Comparison between
different residue-closure models is not claimed.

Compatibility across coefficient places, finite exceptional sets, purity,
weak automorphic association and ramified local compatibility remain distinct
propositions. No compatible-family or automorphic existence conclusion is
assumed here, and none follows from lift existence.

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

For the Frobenius-lift status correction, Harris Section 1, printed
pp.183–184 (PDF pp.7–8), was reread in this original. These pages use
geometric Frobenius `Frob_v` without addressing existence of lifts. The
inverse-power form of the geometric convention is Tate, *Number theoretic background*,
Corvallis Part II (1979), Section 1.4.1, printed p.6 (retained `Part II.pdf`,
PDF p.15). There inertia fixes the residue closure, and uniformizers
correspond to the inverse of the cardinality-power Frobenius. This page was
reread in the registered original `tate-1979-number-theoretic-background`,
SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Neither source is the origin of the lift-existence proof. `FrobeniusLift`
derives it from the Library's proved surjectivity of the spectral residue
action and finite-field Frobenius. The cited names were read in Library
commit `0c88a81463e8a4e1a52fe535b3aa7490adc9ab76`; `FrobeniusLift` was
published at `e7e1cf75d8341a5fe60f25d4e6bb64d251921cbf` as accepted artifact
`88845882-20e5-49d4-96ca-d282e661b114`. `ClosureRestriction` was published
at `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` as accepted artifact
`efa168c5-76b0-4d89-b7c3-bc21e1b9e077`; its own source attribution is in
its paired Markdown.

For the original submission, the reusable representation and adelic names
were read in the Library at commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`:
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
independent semantic review or publication. The Frobenius-lift status
correction changes only this Markdown; the Lean module, its imports and its
declarations are byte-identical.

The exported construction names, all in `Langlands.GaloisRepresentation`, are:

| Declarations | Mathematical role |
| --- | --- |
| `IsContinuous`, `Objects`, `Classes`, `LambdaAdic` | Actual continuous finite representations, their isomorphism quotient and coefficient-completion specialization |
| `characteristicPolynomial`, `eulerPolynomial`, `classEulerPolynomial` | Monic and Euler conventions, including descent through representation isomorphism |
| `characteristicPolynomial_monic`, `characteristicPolynomial_natDegree`, `characteristicPolynomial_coeff_zero_ne` | Monicity, dimension and invertibility consequences |
| `eulerPolynomial_coeff_zero`, `eulerPolynomial_natDegree`, `reverse_eulerPolynomial`, `eulerPolynomial_eq_det` | Exact determinant normalization and reversal laws |
| `characteristicPolynomial_eq_of_equiv`, `eulerPolynomial_eq_of_equiv` | Polynomial invariance under linear intertwiners |
| `pullback`, `atFinitePlace`, `characteristicPolynomial_pullback`, `eulerPolynomial_pullback` | Continuous restriction through actual field embeddings and its polynomial formulas |
