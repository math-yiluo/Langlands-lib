# Compact Sobolev estimates on actual automorphic operator spaces

This proposition is a prerequisite for the actual cuspidal operator
multiplicity-one argument.

`Langlands.Automorphic.OperatorCompactSobolevStatement.{u}` concerns the actual
space `S.Space` of an operator realization of `GL_(r+1)` over a number field
`F : Type u`. The number-field universe stays free, and `r = 0` is included.
The realization has one prescribed unitary Hecke central character `χ`.
Every vector is assumed square integrable on the Library's open determinant
band `1 < |det| < 2` in the rational quotient, for its actual quotient Haar
measure. These are assumptions about the original realized functions.

Fix a compact open subgroup `J` of the finite adelic group and a compact set
`Q` of the adelic matrix group. The conclusion supplies a finite set `D` of
elements of the existing archimedean enveloping algebra and a nonnegative
real constant `C` such that

`|f_x(g)| ≤ C ∑_{d ∈ D} ‖d x‖₂`

for every `J`-fixed vector `x` and every `g ∈ Q`. Here
`f_x(g) = evaluate F (r+1) (S.toContinuous x) g`, `d x` is the actual
`S.envelopingAction d x`, and `‖·‖₂` is the norm of
`OperatorDeterminantSlice.toL2` for the determinant-band Haar measure.
The supplied `hL2` certifies that this map is defined for every original
vector; the differential action stays in `S.Space`. No arbitrary positive
Hermitian form or unrelated Hilbert completion is substituted for this norm.
The quantifier order allows `D` and `C` to depend on `F`, `r`, `S`, `χ`,
`J` and `Q`, but they are independent of `x` and `g`.

The statement does not require cuspidality, irreducibility, compactness of
the additive adele quotient, or finite total volume of the rational quotient.
Its band-square-integrability assumption is retained explicitly. For the
cuspidal consumer with unitary central character, the published argument in
`CuspidalUnitaryForm` obtains a measurable covering set from
`OperatorRealization.exists_band_cover` and applies
`OperatorDeterminantSlice.memLp_band_of_cover` to obtain this integrability.
That argument also assumes `CompactSpace (AdeleQuotient F)`, as required by
the existing cusp interface. `OperatorDeterminantSlice.unitaryForm` then
constructs the positive form from the same band integral. These consumer
assumptions are not added to this Sobolev proposition.

## Source and changes of presentation

The original is J. A. Shalika, *The multiplicity one theorem for GL_n*,
Annals of Mathematics 100 (1974), 171–193, Lemma 5.6 and its reduction to
Lemma 5.7, printed pp.187–188 (PDF pp.18–19). The retained source is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
registered as `shalika-1974-multiplicity-one`, SHA-256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
No source-specific errata note was found in the Library or project notes.

Shalika fixes a unitary central character and a compact open finite subgroup
before choosing the differential operators. Conditions (5.1)–(5.3) impose
rational left invariance, transformation by that central character, and
square integrability modulo the full adelic center. Lemma 5.6 does not require
the cuspidal condition (5.4). Its estimate uses the quotient
`Z(𝔸) GL_n(F) \ GL_n(𝔸)` norm. This proposition instead uses the Library's norm
on the determinant band in `GL_n(F) \ GL_n(𝔸)`. Establishing the required
comparison, or proving the estimate directly for that band, is an explicit
obligation of a subsequent proof. The central character is unitary, so the
pointwise squared norm descends through the center. Haar normalizations and
the volume of the remaining norm-one central quotient may contribute a
positive factor, which the existential constant `C` can absorb. This
explanation is not a proof of the measure comparison.

On printed p.188, Shalika first chooses a smaller compact open finite
subgroup whose conjugates by the given compact set lie in the original
subgroup. He reduces to evaluation at the identity and uses finiteness of
the class number of `PGL_n` to pass to the archimedean group. Lemma 5.7
then states a point-evaluation estimate on an oriented smooth manifold,
with a Lie algebra of independent vector fields spanning each tangent
space and the `L²` norm associated to a nonsingular top-degree form. Its
test functions are compactly supported smooth functions, and its operators
lie in the enveloping algebra of those vector fields. The paper reduces
this manifold estimate to the Euclidean case. Transferring that local
argument to the actual quotient, controlling cutoffs and invariant
derivatives, and using the prescribed determinant-band measure are
obligations of the subsequent proof.

The source absorbs constants into its operators. The proposition instead retains
a separate common `C`, which also avoids dependence on Haar normalization.
It states the estimate for the published stable automorphic operator spaces,
rather than every smooth function on the quotient satisfying the source's
conditions (5.1)–(5.3). Their actual enveloping action records the genuine
archimedean derivatives. Finite sets in place of a list do not affect the
existential estimate: repetitions can be absorbed into the common constant.
The precise band-norm comparison remains unproved here.

## Scope and remaining work

This file defines the proposition and proves no Sobolev estimate. The
Library proves it as `operatorCompactSobolev` (module
`Langlands.Automorphic.OperatorCompactSobolevProof`).
The published Euclidean estimates in
`Langlands.Analysis.LocalSobolevPointwise` concern derivatives and Haar
measure on real vector spaces. They do not already supply the quotient
charts, invariant-vector-field comparison, finite-level quotient analysis,
or band-norm comparison required here.

Fixing `J` is essential. The statement makes no bound uniform over arbitrary
finite levels using archimedean derivatives alone. It supplies no smooth
Hilbert globalization, recovery of smooth vectors, extension of an operator
equivalence, continuous Whittaker uniqueness, or all-place tensor comparison.
For the intended application, an additional argument must apply this estimate
to the compact unipotent quotient defining a Whittaker coefficient and then
identify the actual enveloping derivatives with the derivatives of a
compatible smooth Hilbert representation.
