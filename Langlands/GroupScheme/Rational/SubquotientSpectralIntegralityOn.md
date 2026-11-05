# Pointwise integral characteristic coefficients of actual subquotients

This derived companion to `SubquotientSpectralIntegrality` isolates its
inheritance argument at a single actual rational point. It supplies the
composition-factor step of Kaletha–Prasad, Lemma 2.2.11, when the coefficient
bounds are known on a subset of extended-field points.

For an actual representation subquotient `σ.IsSubquotientOf ρ` and an actual
point `g`, `IsSubquotientOf.charpoly_coeff_vle_one` assumes integral
characteristic coefficients of `ρ.rationalMatrix g` only at that point and
proves the same inequalities for `σ.rationalMatrix g`. It unpacks the
published subquotient predicate into an intermediate representation, an
injective intertwiner and a surjective intertwiner. The existing
`Intertwines.rationalMatrix` comparison specializes both all-affine-test
identities to the actual matrices at `g`. The existing injective and
surjective matrix coefficient-inheritance theorems then transfer the bounds
through the intermediate representation.

`IsSubquotientOf.charpoly_coeff_vle_one_on` applies this argument separately
at each point of an arbitrary subset `S`. In particular, `S` can be the
actual image of ground-field points in a scalar-extended group. No
integrality assumption on points outside `S` is needed.

The primary construction `integralCharpolyOfSubquotientAt` returns a
polynomial over the original valuation ring, certified to be monic, to map
exactly to the actual characteristic polynomial of `σ.rationalMatrix g`,
and to have natural degree equal to the dimension of `σ`. The proof first
uses pointwise inheritance to lift each characteristic coefficient to the
valuation ring. It then applies the existing monic-polynomial lift theorem,
which preserves natural degree, and chooses one such certified lift.

The base field has arbitrary universe and characteristic, its valuative
relation has arbitrary rank, and both representation dimensions may be
zero. There are no reductivity, faithfulness, local-field, topology,
algebraic-closedness, density or simplicity hypotheses. The subset theorem
also permits the empty set. This unit supplies spectral-integrality
inheritance only; it does not prove boundedness or the host
`ReductiveSpectralBoundednessStatement`.

The original composition-factor proof in Kaletha–Prasad passes to an
algebraic closure, takes invariant subspaces, and deduces integral traces on
the irreducible quotients from the original spectral bounds. The present
pointwise form is a derived interface for that passage, retaining the
published actual representation and rational-matrix data. Its proof is the
same elementary injection/quotient transfer as in the preceding module,
with the quantification restricted to the points where bounds are supplied.

Sources: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Lemma 2.2.11 and its composition-factor argument, printed pp.72–73 /
PDF pp.103–104; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The November 2024 corrections, Section 2.2, PDF p.24, impose Henselianity
throughout the section and amend the extension-topology assertion of
Lemma 2.2.5. The pointwise algebraic argument invokes no extension topology
or Henselianity. Registered corrections source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
