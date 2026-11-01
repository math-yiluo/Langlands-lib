# Renard C.I: vanishing of the actual ideal-power filtration

This module formulates the closed Prop-valued statement
`Langlands.Renard.NilpotentFiltrationVanishingStatement.{u}` for the assertion
`V_k = {0}` in David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, Appendix C.I, printed p.275 / one-based
PDF281, immediately after the definition `V_i = I^i V`.

The registered governing original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF281–282 were read, and the formula on PDF281 was rendered and visually checked
for this statement. The registered supplementary 2010 corrections
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, were
read on PDF18–19. Their C.I entries address older inequalities/exponents;
the 2026 edition governs this actual filtration assertion.

## Exact assertion and objects

For every complex vector space `V : Type u`, with explicit `AddCommGroup V`,
`Module ℂ V` and `FiniteDimensional ℂ V` instances, every natural `l`, and
every tuple `a : Fin l → Module.End ℂ V` (using zero-based `Fin l` indices for
the source’s `a_1, …, a_l`), assume precisely that all tuple entries
commute and that every entry is nilpotent as an endomorphism. Then

`NilpotentFiltration.idealPowerSubspace a (Module.finrank ℂ V) = ⊥`.

The imported definitions are the actual generated subalgebra
`R = Algebra.adjoin ℂ (Set.range a)`, the ideal `I` spanned by the original
tuple regarded inside `R`, and `V_n = I^n V` through the original `R`-action,
restricted to complex scalars. This statement names these objects directly.
It does not supply a replacement filtration or assume any power of `I` vanishes.
Tuple commutation implies that this actual algebra is commutative, so its
left ideal is the source's two-sided ideal. Commutation of the original tuple
and nilpotence of every generator remain hypotheses; nilpotence of arbitrary
ambient endomorphisms is not asserted.

The ambient dimension `k = Module.finrank ℂ V` is the exponent, independent
of the generator count. The conclusion is the source's explicit endpoint, not
merely eventual vanishing with an unspecified exponent. The carrier universe
is arbitrary. There is no positivity, nonzero-space, nonempty-tuple,
maximality, sharp-dimension-bound, distinctness or chosen-basis hypothesis;
zero and redundant generators are allowed. For a zero space, `k = 0`,
`V_0 = V`, and top equals bottom. For an empty tuple on a nonzero space,
`I = 0` and `k` is positive. Both boundary cases are included as formal
extensions of the source's notation. The unital algebra contains the identity
and scalars without adding a counted generator; the ideal is generated only
by the listed entries.

## Status and proof boundary

This is a statement, with no proof implementation. It imports the independently
accepted and published `Langlands.Algebra.RenardNilpotentIdealFiltration`
definitions by Lean module name. That dependency constructs the actual ideal
and power-action filtration and proves their construction laws; it does not
prove the vanishing assertion formulated here.

Complement generation, quotient generation, restriction injection, algebra
splitting, dimension estimates, transport of the maximum and its floor
recurrence are separate source-facing obligations. Neither this statement nor
publication of the final C.I bound closes those obligations or the book program.

Worker 709 authored the reused statement draft. Worker 1201 reread the governing
original and supplementary corrections, checked the source correspondence and
published import, and prepared the final pair.
