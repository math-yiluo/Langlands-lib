# Formal degrees on discrete-series classes and unitary twist orbits

This is an internal descent of the actual Schur formal degree from
`FormalDegreeComparisons` to the existing canonical `DiscreteSeriesClass` and
`DiscreteSeriesOrbitClass`. It keeps the central subgroup, quotient and measure
fixed throughout:

\[
d([\pi])=d(\pi)>0,\qquad d(\chi\cdot\omega)=d(\omega),\qquad
d(O)=d(\omega)\quad(\omega\in O).
\]

The source is Waldspurger (2003),
`waldspurger-2003-plancherel`, III.1 (3), printed p.265 / PDF p.31,
III.7, printed p.273 / PDF p.39, and the degree comparison in the proof of
III.7.1, printed p.275 / PDF p.41.

The inputs are a topological group, a normal subgroup `A` contained in its
center, a Borel measurable quotient `G/A`, an inversion-invariant Haar measure
on that quotient, and cofinality of compact open subgroups among open
subgroups. Group and representation-carrier universes remain independent.
There is no finite-dimensional-carrier, characteristic, splitness or
quasisplitness restriction. The class lies in the canonical smooth dual of actual
irreducible admissible smooth representations. Its square-integrability predicate
also includes the existing admissibility and unitary full-central-character
witness.

`discreteSeriesFormalDegree` chooses a representative of the canonical
isomorphism class, recovers its actual square-integrability from the class
predicate, and applies `representationFormalDegree`. Its computation lemma
`discreteSeriesFormalDegree_mk` identifies the result with the actual
representation's degree for every representative. The proof turns the
representative isomorphism into a representation equivalence and applies the
degree comparison. `discreteSeriesFormalDegree_pos` follows from the existing
positivity. `discreteSeriesFormalDegree_eq_formalDegree` identifies it with the
original Schur degree for every scalar-action witness on `A`. In particular,
the class degree has the crossed-pairing normalization

\[
\int_{G/A}\ell_1(\pi(g)v_1)\ell_2(\pi(g^{-1})v_2)\,d\mu(g)
  =d([\pi])^{-1}\ell_2(v_1)\ell_1(v_2)
\]

for every two vectors and two actual smooth dual functionals. The displayed
integrand is the existing well-defined quotient lift for a scalar-action
witness, and the inverse uses the complex coercion of the real degree.
The chosen representative and character do not add normalization parameters;
the computation law, existing arbitrary-witness comparison and proof
irrelevance remove these choices.

`discreteSeriesFormalDegree_unitaryTwist` proves invariance under every
open-kernel, pointwise norm-one complex character. Quotient induction reduces it
to the comparison of actual representations. The character twist is the
existing canonical twist, with its proved square-integrability preservation.

For an indexed family of positive norm characters in an independent index
universe and `NonarchimedeanGroup G`,
`discreteSeriesFormalDegree_smul` gives invariance under the existing unitary
unramified twist action. `discreteSeriesOrbitFormalDegree` descends the class
degree using `Quotient.lift` on the existing actual orbit relation.
Two related classes have the form \(\omega=\chi\cdot\eta\); the preceding
invariance gives exactly the equality required by this lift. No replacement
class quotient, twist action, or orbit equivalence relation is introduced.
`discreteSeriesOrbitFormalDegree_mk` computes it on each class,
`discreteSeriesOrbitFormalDegree_pos` proves positivity, and
`discreteSeriesOrbitFormalDegree_eq_of_mem` identifies it with the degree of
every member of a representative's orbit.

These constructions use the existing Schur integral, existence, positivity and
uniqueness proofs. No degree is chosen as a free normalization parameter. The
source application still requires the actual split-center and rational-character
specializations. Finiteness or unitarity of the full stabilizer, orbit topology
and measure, Haar-scale comparisons, the Fourier and polynomial calculations of
III.7 and the Plancherel theorem are separate obligations.
