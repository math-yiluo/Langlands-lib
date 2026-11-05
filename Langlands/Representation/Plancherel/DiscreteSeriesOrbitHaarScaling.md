# Haar rescaling of the actual discrete-series twist orbits

This internal normalization construction extends the identity transport of
canonical discrete-series classes to the existing unitary unramified twist
action and its actual orbit quotient. For a positive finite scalar `c`, it
constructs

\[
\overline E_c:\mathcal E_2(G,A,\mu)/\operatorname{Im}X_\nu(G)
 \simeq \mathcal E_2(G,A,c\mu)/\operatorname{Im}X_\nu(G),
\qquad
 d_{c\mu}(\overline E_c O)=c^{-1}d_\mu(O).
\]

The notation `Im X_ν(G)` denotes the existing group
`unitaryUnramifiedCharacters ν`. The central subgroup and the norm-character
family remain explicit.

The provenance is Waldspurger (2003), `waldspurger-2003-plancherel`, III.1 (3),
printed p.265 / PDF p.31, and III.7, printed p.273 / PDF p.39. The first passage
characterizes the positive real formal degree by the crossed-pairing Schur
integral. The second defines `E₂(G)`, the unitary unramified twist action, its
orbits and their stabilizer parameterization. Haar-scale transport of those
objects is an internal deduction here, rather than a separately stated result
of the source. The construction uses the already defined actual classes,
twists, orbits, stabilizers and degrees from `DiscreteSeriesOrbits`,
`DiscreteSeriesFormalDegree` and `FormalDegreeHaarScaling`.

The common setting is an actual topological group `G` with
`NonarchimedeanGroup G`, a normal central subgroup `A`, a measurable Borel
quotient `G/A` and a Haar measure `μ` on that quotient. There is an arbitrary
index type `I` and family `ν : I → (G →* ℝ≥0ˣ)`. The existing unramified
characters are the continuous complex characters trivial on the common kernel
of this family, and the unitary subgroup consists of those of pointwise norm
one. The nonarchimedean hypothesis supplies the smoothness needed for their
action on the canonical smooth representation classes. The group, index and
representation-carrier universes are independent. No restriction on field
characteristic, splitness, quasisplitness or finite-dimensionality of a
representation carrier is introduced. The scalar is `c : ℝ≥0` with `[NeZero c]`,
so it is strictly positive and finite.

Write `E_c` for `discreteSeriesClassHaarScalingEquiv A hA μ c`. Its two directions
retain the underlying canonical smooth isomorphism class and change its
square-integrability proof using the actual positive measure-scaling
comparison. The theorems `discreteSeriesClassHaarScalingEquiv_smul` and
`discreteSeriesClassHaarScalingEquiv_symm_smul` prove

\[
 E_c(\chi\cdot\omega)=\chi\cdot E_c(\omega),\qquad
 E_c^{-1}(\chi\cdot\eta)=\chi\cdot E_c^{-1}(\eta).
\]

Both statements use the same actual character `χ` on either side. On underlying
classes the maps are the identity and the twist operations agree; subtype
extensionality gives the equalities. No integral, inversion-invariance or
compact-open-cofinality hypothesis is needed for these statements.

`mem_discreteSeriesOrbit_haarScaling_iff` preserves and reflects the actual
orbit membership relation: `E_c η` belongs to the twist orbit of `E_c ω` for
`c • μ` if and only if `η` belongs to the twist orbit of `ω` for `μ`. The proof
uses the existing existential character description of orbit membership,
equivariance and injectivity of `E_c`. Similarly,
`discreteSeriesStabilizer_haarScaling` proves equality of the two actual
stabilizer subgroups in the same group `unitaryUnramifiedCharacters ν`, by
unfolding the fixed-point condition and applying equivariance and injectivity.
This equality has no finiteness hypothesis or conclusion and does not compare
the unitary stabilizer with a stabilizer in a larger character group.

The definition `discreteSeriesOrbitHaarScalingEquiv` uses `Quotient.map` in
both directions on the existing `MulAction.orbitRel` quotient. A witness of
that relation is the same actual twisting character after applying `E_c` or
its inverse; the two equivariance laws prove well-definedness. Quotient
induction reduces the inverse laws to the corresponding inverse laws for
`E_c`. The computation theorem `discreteSeriesOrbitHaarScalingEquiv_mk` states
that the orbit of every class `ω` is sent to the orbit of `E_c ω`, by the
defining quotient-map equation. No alternative orbit quotient is introduced.

The degree comparison additionally assumes that `μ` is invariant under
inversion and that compact open subgroups are cofinal among open subgroups of
`G`. These are the explicit hypotheses of the existing actual Schur-degree
construction. Local instances construct Haar measure and inversion invariance
for `c • μ`: nonzero nonnegative scaling preserves Haar measure, and mapping a
scaled measure by inversion commutes with that scaling. The caller supplies no
additional scaled-measure hypotheses, and the module installs no global
instances.

`discreteSeriesOrbitFormalDegree_smul_measure` proves the displayed
inverse-scaling formula for every actual orbit class. Quotient induction
exposes a discrete-series class; the orbit-transport computation and the two
existing orbit-degree computation laws reduce the assertion to
`discreteSeriesFormalDegree_smul_measure`. That theorem already identifies the
actual class degrees by the Schur characterization and uniqueness on the
unchanged central quotient. Thus the orbit law concerns those constructed
degrees, rather than assigned normalization parameters.

This unit supplies orbit-level Haar normalization comparisons toward the
Plancherel program. The underlying group, central quotient, representations and
character family stay fixed while the Haar scale changes explicitly. It
constructs no topology or measure on character orbits. Identification of `A`
with the source's split center, rational-point and rational-character
realizations, other compatible quotient measures, stabilizer finiteness and
comparison, the polynomial and Fourier arguments of III.7, and the Plancherel
transform and inversion remain separate obligations.
