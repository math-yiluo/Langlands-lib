# Full Whittaker type of canonical rank-one quasicharacters

`Langlands.RankinSelberg.rankOneWhittakerType` proves exactly the published
`Langlands.RankinSelberg.RankOneWhittakerTypeStatement.{uF}`, with arbitrary
field universe `uF`. The theorem has no additional parameters or hypotheses.
It concerns every prime, every canonical p-adic field, every bundled continuous
nontrivial unitary additive character, and every continuous complex
quasicharacter. The representation is the existing `rankOneCharacter` on the
complex scalars.

The first helper, `scalar_isOfWhittakerType_rankOne`, treats any smooth GL(1)
representation on the complex scalars. It proves all three clauses of
`IsOfWhittakerType`. Smoothness is supplied to this helper; finite-dimensionality
of each fixed subspace supplies the remaining admissibility condition.
`Module.Finite.of_restrictScalars_finite` gives finite generation of
`π.asModule` over the actual complex group algebra from finite generation over
the complex scalars. Finally, `glFunctionals_rankOne` identifies the whole
standard Whittaker-functional submodule with the full algebraic dual.
`Submodule.topEquiv` followed by `LinearMap.ringLmapEquivSelf ℂ ℂ ℂ` gives
its linear equivalence with the complex scalars, equivalently evaluation at one.
The argument identifies the entire functional space, rather than selecting
only a nonzero functional.

The second helper, `rankOneCharacter_isOfWhittakerType`, proves the required
smoothness for every continuous quasicharacter. It installs the canonical field
topology and the canonical nonarchimedean instance for GL(1). Composing the
quasicharacter with the continuous determinant gives a continuous complex
character of GL(1). The existing
`isOpen_ker_of_continuous_complex_character` proves that its kernel is open.
The existing `isSmooth_twist_iff` then reduces smoothness of its scalar
character representation to smoothness of the trivial representation. Every
vector of the trivial representation is fixed by the whole group, represented
in the proof by the top open subgroup. Applying the first helper proves full
Whittaker type. The final theorem is this helper at the closed published target.

Continuity and nontriviality of the additive character remain bundled
assumptions. The rank-one unipotent subgroup, and therefore
`standardCharacter ψ 0`, is trivial; this explains why the functional-space
argument works for every additive character in that bundle. The multiplicative
character needs only its bundled continuity. Smoothness is proved, and no
finite-order, unitarity, conductor, Haar-measure, irreducibility, supplied
functional, or representation-equivalence hypothesis is added.

This is an internal derivation from existing Library definitions and lemmas,
not a transcription of a separately numbered literature result. Worker 53
authored the proof in revision 2 of the shared draft for task
`379b5e0f-b1f2-4767-9385-f7dfdecbd407`. Worker 504 reused that Lean source
unchanged, checked it against the published target, and prepared this companion
Markdown and contribution. Both workers are actual coauthors. The module imports
the published statement and its supporting results by Lean name; it does not
include the draft statement pair.

The carrier here is exactly the complex scalars. This result supplies a scalar
rank-one certificate; it makes no assertion about a universe-lifted carrier,
Rankin–Selberg analytic comparison, L-factor multiplicativity, or tail
L-polynomial divisibility.
