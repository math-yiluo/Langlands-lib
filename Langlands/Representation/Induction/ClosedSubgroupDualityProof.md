# Smooth induction and the smooth dual of compact induction

The module `Langlands.Representation.Induction.ClosedSubgroupDualityProof`
proves `Langlands.Induction.closedInductionSmoothDuality`, whose type is exactly
the published proposition
`Langlands.Induction.ClosedInductionSmoothDualityStatement`.
Worker 268 supplied this proof for Task 5787.

The group and coefficient universes remain independent. The theorem applies to
every closed subgroup of a Hausdorff, locally compact, totally disconnected
group and every smooth complex representation of that subgroup. Its invariant
functional is arbitrary subject to the target's invariance and nonzero
hypotheses.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
of 9 July 2026, III.2.7, Theorem, printed p.78 / PDF p.84; registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original theorem gives the duality by integrating the pointwise evaluation
pairing over the homogeneous space. Its proof refers to the fixed-vector
descriptions in III.2.2 and the compact-open duality lemma I.4.1.

The implementation follows that route, using the published compact-induction
fixed-vector model and compact-open duality. For nonvanishing of the
double-coset integrals it additionally uses the published theorem II.3.9,
`HarmonicAnalysis.HomogeneousFunctions.Renard.invariantFunctional`.
This theorem supplies strict positivity for a generator and scalar uniqueness
in the full algebraic space of right-invariant functionals. Thus the proof does
not assume positivity of the functional in the target.

All helpers in the namespace `Langlands.Induction.ClosedSubgroupDuality` are
internal constructions or deductions for this proof, rather than additional
source statements.

## The integrand and invariant pairing

`integrand` constructs the actual function
`g ↦ smoothDualPairing ρ (h(g)) (f(g))` in `renardSpace H hH`.
Local constancy follows by composing the two locally constant evaluation
functions with the coefficient pairing. Covariance follows from invariance of
the contragredient pairing: the scalar twist contributes exactly
`relativeModular H hH`. For support, a compact lift of the quotient support of
`f` also covers the integrand's support modulo `H`, since the integrand
vanishes wherever `f` vanishes.

`pairing` applies the specified functional `ν` to `integrand` and bundles the
result as a bilinear map. `pairing_invariant` follows from right invariance of
`ν`, because right translation of both arguments right translates their
pointwise pairing.

## Compact stabilizers and basic functions

For a compact open subgroup `K` and `x : G`, put
`Jₓ = H ∩ x K x⁻¹`, represented by `conjOpenSubgroup H K x`.
Closedness of `H` makes `Jₓ` compact. `relative_eq_one` uses triviality of the
two modular characters on compact subgroups to show that the relative modular
character is trivial on `Jₓ`. Hence the given complex character is also
trivial there (`character_eq_one`), and `fixedTwistEquiv` identifies the fixed
spaces of `twist χ ρ` and `ρ` by the identity on underlying vectors.

`basic K hK x` is the scalar compact double-coset section, viewed in
`renardSpace`: it is zero off `H x K` and has value `χ(a)` at `a x k`.
It is nonnegative, and its value at `x` is one. To prove `basic_ne_zero`,
write the given invariant functional as `ν = c • ν₀` using II.3.9.
The hypothesis `ν ≠ 0` implies `c ≠ 0`, and strict positivity gives
`ν₀(basic K hK x) ≠ 0`. Consequently
`ν(basic K hK x) ≠ 0`.

For `K`-fixed `h` and a compact section with coefficient `v` at `x`,
`integrand_section` proves that the integrand equals
`h(x)(v) • basic K hK x`. On `H x K` this follows from covariance,
right `K` invariance and invariance of the coefficient pairing; off that
double coset the compact section vanishes. Applying `ν` gives
`pairing_section`:

```text
pairing(h, sectionₓ(v)) = h(x)(v) · ν(basicₓ).
```

## Nondegeneracy and surjectivity

`compact_cofinal` supplies compact open subgroups inside arbitrary open
subgroups, using the published compact-open test-function invariance theorem
with the empty family of tests.

For `pairing_left`, choose a compact open `K` fixing `h`. At every `x`,
`h(x)` is a `Jₓ`-fixed smooth functional. If `h` pairs to zero with every
compact section, the displayed formula and `ν(basicₓ) ≠ 0` show that
`h(x)` vanishes on `W^{Jₓ}`. Injectivity of
`smoothDualFixedRestriction` at the compact open subgroup `Jₓ` then gives
`h(x) = 0`. Pointwise equality yields `h = 0`.

For `pairing_fixed_surjective`, start with an arbitrary linear functional
`φ` on the `K`-fixed compact induction. At each representative `q.out` of
`H \ G / K`, compose `φ` with the one-coordinate section map, transport
through `fixedTwistEquiv`, and divide by `ν(basic₍q.out₎)`.
The inverse of `smoothDualCompactFixedEquiv` extends this coefficient
functional to a `J₍q.out₎`-fixed smooth functional on `W`.

`assemble` combines these arbitrary coefficients into a single `K`-fixed
smooth induced function: at `x`, use the compact double-coset section
belonging to the double coset of `x`. Covariance and right `K` invariance
follow because the selected double coset is unchanged by the corresponding
multiplications. There is no finiteness requirement on this coefficient
family. The section formula verifies the desired pairing on every
one-coordinate compact section. `DFinsupp.lhom_ext` and
`compactFixedEvaluationEquiv` extend this equality to the entire fixed space.

Finally, `exists_smoothDualEquiv_of_fixedSurjective` combines the invariant
pairing, left nondegeneracy, smoothness of both induced representations and
surjectivity at every compact open level. The resulting representation
equivalence has the pairing required by the target; its integrand witness is
the constructed `integrand`.
