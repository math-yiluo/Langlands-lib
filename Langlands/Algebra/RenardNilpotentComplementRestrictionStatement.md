# Renard C.I: restriction to a complement and the resulting dimension bound

Worker 709 formulates the closed Prop-valued declaration
`Langlands.Renard.NilpotentComplementRestrictionStatement.{u}` for two
consecutive assertions in David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix C.I,
printed p.275 / one-based PDF281. These are the determination of each
element of `R` by its restriction to `W` and the resulting inequality
`dim R ≤ s k`, where `s = dim W` and `k = dim V`. This pair contains no
proof implementation.

The governing registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF281–282 were reread and PDF281 was visually inspected for the exact
restriction and dimension assertions. The registered supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF18–19. Its C.I corrections concern older inequalities and
exponents; the 2026 original governs the assertions formulated here.

## Quantifiers and actual objects

For every complex vector space `V : Type u`, with explicit `AddCommGroup V`,
`Module ℂ V` and `FiniteDimensional ℂ V` instances, every natural `l` and
every tuple `a : Fin l → Module.End ℂ V`, assume that all entries commute
pairwise and that every entry is nilpotent. The tuple uses zero-based `Fin l`
indices for the source's listed generators.

The published import `Langlands.Algebra.RenardNilpotentIdealFiltration`
provides the actual unital algebra
`R = Algebra.adjoin ℂ (Set.range a)`, its original tuple-generated ideal `I`,
and the original-action complex subspace `V_1 = I V`. Under tuple commutation
this actual algebra is commutative and the imported left ideal is the
source's two-sided ideal.

The assertion quantifies over every `W : Submodule ℂ V` such that
`IsCompl (NilpotentFiltration.idealPowerSubspace a 1) W`.
Thus `W ∩ I V = 0` and `W + I V = V`. The complement need not be invariant
under the generators or under `R`.

## Restriction injectivity and dimension

The first conclusion is injectivity of the actual function

`r ↦ (r : Module.End ℂ V).domRestrict W`.

Its domain is the original subalgebra `R`, and its codomain is the space of
complex-linear maps from `W` to `V`. It restricts the domain of each original
endomorphism. It does not claim that the image lies in `W`, and no
endomorphism of `W` is substituted. Injectivity says exactly that two elements
of `R` agreeing on `W` are equal in the original endomorphism algebra.

The second conclusion is the natural-number inequality

`Module.finrank ℂ R ≤ Module.finrank ℂ W * Module.finrank ℂ V`.

All three vector spaces are finite-dimensional: `R` is a complex subspace
of the endomorphisms of finite-dimensional `V`, and `W` is a subspace of `V`.
Consequently this is the source's ordinary complex-dimension inequality,
with `s = finrank ℂ W` and `k = finrank ℂ V`; it does not use the
convention of zero finrank for an infinite-dimensional space. The
restriction map is complex-linear and its ambient target has dimension
`s k`. These observations explain the source route to the inequality;
the Lean file only states its conclusion.

The carrier universe is arbitrary. Zero spaces, empty tuples, and zero,
repeated or redundant entries are included. For a zero space the domain
algebra and restriction target are trivial and both sides of the inequality
are zero. For an empty tuple on a nonzero space, `I = 0`, so its complement
is all of `V`; restriction is then faithful on the scalar algebra. These
are explicit boundary extensions of the source notation. The identity and
scalars are contained in the unital adjoin without adding a counted generator.
There is no positivity, nontriviality, maximality, chosen-basis, supplied
generation, supplied vanishing or sharp-dimension-bound premise.

## Proof and remaining scope

Renard first obtains `R · W = V` from the power filtration. Commutativity
then implies that an element killing `W` kills every vector in `V`, which
gives restriction injectivity and the dimension inequality. This describes
the intended source proof route; neither generation nor injectivity is
proved in this statement pair, and generation is not an added premise.

The subsequent source inequality `φ_l(k) ≤ s k` requires applying this
result to a tuple that actually attains the maximum. No maximum assertion
is made here for an arbitrary tuple or complement. Attainment, the actual
filtration endpoint and generation proofs, algebra splitting, restriction
to `V_1`, monotonicity, the floor recurrence and the final estimates retain
their separate obligations, as does the remainder of the whole-book program.

Worker 709 authored the reused statement draft. Worker 1194 checked the
2026 source passage and supplementary corrections, verified the imported
objects and complete declaration, and prepared this contribution.
