# Integral cocharacters detecting a rational character subspace

Author: Worker 355.

This internal linear algebra construction supplies a finite zero-set choice on
the actual character and cocharacter lattices of a split torus over an
arbitrary field in universe `u`. It uses the published positive denominator
clearing theorem `IsSplitTorus.exists_positive_multiple_pairing` and Mathlib's
finite hyperplane avoidance theorem
`Module.exists_dual_forall_apply_ne_zero`. It introduces no external source
hypothesis.

`IsSplitTorus.exists_cocharacter_zero_iff_mem_subspace` takes a rational
subspace `W` of the full rational character space and a finite set `R` of
actual characters. It constructs an actual integral cocharacter `ν` that
annihilates every character whose rationalization is in `W`. For every
character in `R`, its pairing with `ν` is zero if and only if its
rationalization belongs to `W`. There is no assertion about the converse for
characters outside `R`.

The proof passes to the quotient by `W`. The images of the members of `R`
outside `W` are a finite family of nonzero vectors. Hyperplane avoidance
chooses a rational linear functional nonzero on every member of this family.
Compose it with the quotient map, and clear denominators by a positive
integer to obtain an actual integral cocharacter. The pairing is zero on
`W` and nonzero on every specified character outside `W`. The finite family
may be empty and the subspace may be the entire character space.

`IsSplitTorus.exists_cocharacter_zero_iff_mem_ratSpan` specializes `W` to
`ratSpan J` for any chosen set `J` of actual characters. Its chosen
cocharacter annihilates `J` and has zero pairing on a member of `R` exactly
when that character belongs to the rational span of `J`. Finiteness is
required only for `R`, not for `J`.

The Prop-valued `SpanAnnihilatingCocharacterStatement` packages the latter
assertion, and `spanAnnihilatingCocharacter` proves it. When `R` is a finite
relative root set, the result supplies the cocharacter needed to detect the
roots in a chosen rational span. It does not construct a common-kernel
torus, prove the convex symmetric-part span criterion, identify Weyl
stabilizers, or prove an intersection theorem.
