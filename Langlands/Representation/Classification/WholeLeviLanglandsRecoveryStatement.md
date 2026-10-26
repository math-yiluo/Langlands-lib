# Standard Langlands recovery for whole-Levi inputs

`Langlands.GLWholeLeviLanglandsRecoveryStatement.{uF,uV,uW,uJ,uK}`
states recovery of regular positive standard Langlands data from equivalent
irreducible quotients. It is a proposition definition, with no proof in this
file. Its five universe parameters are independent.

The field is an arbitrary `PadicField.{uF} p` with supplied topological data
`T`; the rank `n` is positive. The input shapes `B` and `C` are arbitrary
ordered positive block shapes of rank `n`. The representations `σ` and `τ`
are arbitrary representations of the actual full product Levi groups,
with carriers in `Type uV` and `Type uW`. Each is irreducible and satisfies
the existing `RelativeRegularComparison.IsLeviTempered` predicate. This is
analytic temperedness on the whole Levi, quantified over all Borel Haar
measures on its actual quotient by its center. It is not a replacement
condition defined in terms of classification data.

The real vectors `t` and `u` on the respective blocks are strictly decreasing.
The representations `J` and `K` of the ambient `GL_n` have carriers in the
independent universes `uJ` and `uK` and are irreducible. The hypotheses provide
surjective actual intertwiners from the normalized parabolic inductions of
`T.leviRealPowerTwist B t σ.ρ` and `T.leviRealPowerTwist C u τ.ρ` onto `J.ρ`
and `K.ρ`, respectively, and a nonempty type of representation equivalences
between `J.ρ` and `K.ρ`.

The conclusion is an equality `h : B = C`, equality of the transported real
vector with `u`, and an equivalence of the transported untwisted representation
with `τ.ρ`. The dependent transports have the mathematical form

```text
tC : Fin C.length → ℝ := h ▸ t
σC : Rep.{uV} ℂ (C.Levi F.Carrier) := h ▸ σ
tC = u ∧ Nonempty (σC.ρ.Equiv τ.ρ).
```

Lean implements both transports with `Eq.rec` and an explicit motive. The
representation equivalence explicitly uses the carrier, additive group and
complex module instances stored in each `Rep`. This avoids typeclass
inference through the transported bundle; it adds no assumption or data.

Thus it recovers the whole ordered shape, not only the number of blocks or
an association of Levi subgroups. The representation conclusion is for the
untwisted input. No tensor decomposition, support witness, common literal
quotient, prescribed parameter equality, or universe domination is assumed.
A single block is allowed; strict decrease is then vacuous.

This is a derived interface for the standard-data part of the semistandard
conjugacy project, corresponding to task
`707cfa4e-a9aa-4748-8f7a-0074d8ee5a3d`. The existing
`GLRegularLanglandsParameterUniquenessStatement` and
`GLRegularLanglandsTensorRecoveryStatement` express related recovery goals
for supplied tempered block factors in a common enlarged universe. This
statement expresses the additional whole-Levi and universe adapter needed
by the parent, without assuming that adapter as a premise. The closed
`CuspidalSupport.padicLeviAdmissibleFactorization` supplies an algebraic
factorization tool in the original carrier universe, but does not by itself
establish analytic temperedness of each factor or this recovery theorem.
A proof must discharge those analytic, induction-transport and universe
obligations using closed results, rather than assume the related Prop-valued
targets. No completed proof of this statement is claimed here.

The only direct import is `RelativeRegularComparisonStatement`, providing
the actual analytic predicate and induction definitions. Neither this file
nor its import closure depends on `SemistandardLanglandsStatement`, so this
standard-data interface does not create a circular dependency on the parent
conjugacy target. Its provenance is the explicit whole-Levi formulation and
adapter rationale above, not a claim that this precise dependent-type and
universe formulation occurs verbatim in external literature.
