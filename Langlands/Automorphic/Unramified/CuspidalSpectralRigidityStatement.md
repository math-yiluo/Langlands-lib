# Jacquet–Shalika rigidity for supplied cuspidal spectral systems

This module gives proposition targets for Jacquet–Shalika's mixed-rank
cuspidal trace independence and the numerical constituent-recovery argument
in their Theorem 4.4. It contains no proofs of these targets. The aggregate
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement` is their
conjunction.

## Actual objects and supplied spectra

Every target quantifies over a number field `F : Type uF`, with complex
coefficients and the explicit compactness assumption
`CompactSpace (AdeleQuotient F)` inherited from the automorphic framework.
The cuspidal entries are `PositiveRankCuspidalClass F`: the disjoint union,
over `r : ℕ`, of the full operator equivalence classes of actual irreducible
cuspidal realizations on `GL_(r+1)`. Equality retains the positive rank and
the full finite, compact and differential operator equivalence. It is not
equality of chosen embeddings or only of finite restrictions.

For each class `c i`, a numerical system of rank `(c i).rank` is supplied,
and `PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)` is
required. This existing relation witnesses a genuine spectral presentation
inside an actual representative: a nonzero finite adelic invariant slice,
an equivariant restricted tensor presentation with actual smooth local
factors, and spectra satisfying the normalized spherical Hecke equations
on the whole fixed space. The local factors are admissible and irreducible
outside the spectral exceptional set. The factor universe `uV` is
independent of the number-field universe `uF`; finite sums and the spectral
comparisons use the existing published numerical constructions.

No arbitrary numerical system is identified with an automorphic object.
The attachment conditions are premises of each target. There is no assertion
that all classes admit such presentations, and no selection of a canonical
presentation or spectrum.

## Trace independence

`CuspidalPowerTraceIndependenceStatement` takes a finite indexed family of
pairwise distinct full cuspidal classes, expressed by `Function.Injective c`.
Their positive ranks may differ, and no unitarity condition is imposed.
For a finite set `S` containing every supplied spectral exceptional set
and coefficients `a i : ℂ`, its premise is

\[
  \sum_i a_i \operatorname{tr}(A_{i,v}^{\,k})=0
  \qquad(v\notin S,\ k\geq 1).
\]

The Lean trace is `SpectralSystem.powerTrace`, the sum of the `k`th powers
of the supplied nonzero eigenvalues. The membership proof is obtained from
`hS` and `v ∉ S`. The conclusion is `∀ i, a i = 0`.
One set `S` works for all positive powers; the target does not merely test
the first power. Only finite places are indexed, so the infinite places
included in the source's exceptional set are already omitted.
The finite family is indexed by `Fin p`, including the harmless empty case.

This is the supplied-presentation formulation of JS81 Theorem 4.2
(printed pp.806–807). The source first identifies the disjoint union of
cuspidal equivalence classes in all positive ranks and explains the passage
from unitary representations to arbitrary cuspidal representations by
positive quasi-character twists. The normalization is inherited from
the attached spherical spectra; this module introduces no additional
twist or choice of uniformizer.

## Constituent recovery with multiplicities

`CuspidalPowerTraceConstituentRecoveryStatement` takes two finite lists of
full cuspidal classes, with attached systems. Repetitions are allowed:
there is no injectivity hypothesis on either list. Its premise is
`SamePowerTraces` for their numerical `SpectralSystem.finiteSum`s.
That construction concatenates the eigenvalue multisets and retains all
multiplicities, even when ranks vary. The premise says that outside one
finite set the sums of traces agree at every positive power.
The cofinite quantifier precedes the quantifier over positive powers.
The finite union of the individual exceptional sets can be added to that
same set, so all tested eigenvalues are defined simultaneously.

The conclusion supplies a bijection `e : Fin p ≃ Fin q` such that
`c i = d (e i)` for every index. This recovers the two constituent lists,
including repetitions and ranks. In particular, their lengths and total
ranks agree, without assuming either equality. Empty lists are allowed.
The singleton specialization recovers equality of full cuspidal classes
from equality of their attached spectra almost everywhere.

`CuspidalEulerConstituentRecoveryStatement` has the same inputs and
conclusion, replacing the trace premise by `SameEulerPolynomials` for the
two numerical sums. By the existing `finiteSum_eulerPolynomial` formula,
this compares the products of normalized denominator polynomials

\[
  \prod_i\prod_{\alpha\in s_{i,v}}(1-\alpha X)
  =
  \prod_j\prod_{\beta\in t_{j,v}}(1-\beta X)
\]

outside a finite set. Nonzero complex eigenvalues and their multiplicities
are retained. This is a polynomial equality, not just equality of polynomial
degrees or of their values at one point.

These are the numerical recovery step of the argument in JS81 Theorem 4.4
(printed p.809), together with its Euler-polynomial reformulation. There
the authors pass from equality of the unramified components of induced
representations to equality of block sums of Satake classes, then to
positive-power trace sums, and finally collect multiplicities and apply
Theorem 4.2. Our targets start at the numerical comparison with genuine
attachments. They do not state the preceding comparison of local induced
representations, nor construct an actual global isobaric representation.
They permit differing total ranks in the inputs: the numerical comparison
and the bijective conclusion enforce equality rather than assume it.

No implication between these three targets is proved here. A later proof
that collects repeated classes must justify equality of the numerical
spectra supplied by different presentations of the same class. The existing
transport theorem preserves a single supplied factor family; it does not
establish that additional uniqueness result by itself. Existence of
presentations, uniqueness across different presentations, analytic
Jacquet–Shalika arguments, local induced-component compatibility, and
realized-isobaric equivalence remain separate proof or construction
obligations. No such result is inserted as a field or a hidden axiom.

## Original source and provenance

H. Jacquet and J. A. Shalika, *On Euler Products and the Classification of
Automorphic Forms II*, American Journal of Mathematics **103** (1981),
777–815. Registered literature ID: `jacquet-shalika-1981-euler-ii`.
Source file:
`/home/taskhub/central-library/Jacquet-Shalika--On Euler products and the classification of automorphic forms II--1981.pdf`.
SHA256: `4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.

Printed pp.805–809, one-based PDF pp.30–34, were read from the original:
§4.1 supplies the unitary analytic background; Theorem 4.2 and its proof
on pp.806–807 give mixed-rank independence; §4.3 on pp.807–808 describes
the inducing data and associate pairs; Theorem 4.4 and its proof on p.809
give the multiplicity recovery argument. The first target follows Theorem
4.2 on the project's actual supplied-presentation domain. The recovery
targets isolate the numerical step of Theorem 4.4 and its elementary
polynomial reformulation, rather than claiming to formalize all of §4.3–4.4.
