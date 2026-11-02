# Renard B.III: simple left quotients separating a shifted element

`Langlands.Renard.leftShiftSimpleQuotient` proves the exact published
`Langlands.Renard.LeftShiftSimpleQuotientStatement` from
`Langlands.Algebra.SeparationStatements`:

```lean
theorem leftShiftSimpleQuotient (A : Type u) [Ring A] [Algebra ℂ A] :
    LeftShiftSimpleQuotientStatement A
```

For `a : A` and `z : ℂ` with `z ≠ 0`, assume that no `b : A` satisfies
`b * (a - algebraMap ℂ A z) = 1`. The theorem constructs an actual left ideal
`I : Submodule A A` such that `IsCoatom I`, the principal left ideal generated
by the shift lies in `I`, the actual quotient left module `A ⧸ I` is simple,
and `a • I.mkQ 1 ≠ 0`. The universe `u` is arbitrary. No countability,
nontriviality or commutativity assumption is used.

The implementation first applies `principalLeftIdealProper` to show that
`Submodule.span A {a - algebraMap ℂ A z}` is proper. Then
`Ideal.exists_le_maximal` places this left ideal inside a maximal left ideal
`I`. Mathlib's `Ideal A` is definitionally the submodule of the regular left
module, so this theorem gives precisely an `I : Submodule A A`. It holds for
arbitrary semirings and requires no commutativity. `Ideal.IsMaximal.out`
gives the required coatom property; `isSimpleModule_iff_isCoatom` then gives
`IsSimpleModule A (A ⧸ I)`.

To show `a ∉ I`, suppose otherwise. The shift belongs to `I` by containment
of its principal left ideal. Subtracting the shift from `a` gives
`algebraMap ℂ A z ∈ I`. Closure under left scalar multiplication in the
regular module allows multiplication on the left by
`algebraMap ℂ A z⁻¹`. This yields `1 ∈ I`, because the product is
`algebraMap ℂ A (z⁻¹ * z) = 1`. Thus `I = ⊤` by `Ideal.eq_top_iff_one`,
contradicting maximality. This computation uses only multiplication on the
left, the nonzero scalar premise and the algebra homomorphism laws.

Finally, linearity of the quotient map gives
`a • I.mkQ 1 = I.mkQ (a * 1) = I.mkQ a`.
`Submodule.Quotient.mk_eq_zero` identifies vanishing of the latter with
`a ∈ I`, proving the nonzero action on the specified class of `1`. The
quotient is a left module. Its inherited complex module and scalar tower
are exactly the structures checked in the published statement module.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, B.III, printed page
273 / one-based PDF page 279. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The source passes from the nonzero cyclic module
`N = A / A(a - λ1)` to a simple quotient using A.VI.3, Proposition (i),
printed page 264 / PDF270. That proposition obtains a maximal proper
subobject by Zorn's lemma. The Lean proof obtains its inverse-image maximal
left ideal directly through `Ideal.exists_le_maximal`. This is the same
quotient construction expressed in `A`, with the source's inverse-image
ideal identified with `I` and its simple module realized by `A ⧸ I`.
It does not depend on the general categorical simple-quotient theorem.

The final argument also sharpens the source's wording in the way required
by the published statement. The source supposes that `a` annihilates the
simple quotient and deduces `a ∈ I` using `a * 1 = a`. The Lean proof rules
out `a ∈ I` directly, so the separating vector is explicitly the class of
`1` rather than an unspecified vector.

Worker 1210 read B.III PDF279 as text and a rendered page, A.VI.3 PDF269–270
as text, and the older-edition errata PDF18–19. The registered older errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF19,
remove the old right-zero-divisor claim while retaining the absence of a
left inverse. Both source hashes were verified, and the 2026 text already
incorporates the correction. No separate Renard errata note was present in
the current Library.

Worker 1210 wrote the proof and explanation. The published statement and
its matching informal proof outline are due to Worker 221 and Worker 6.
The nonnilpotent resolvent assertion and the final unital separation
statement are separate proof units. The source's reduction from a
nonunital algebra remains a separate obligation.

Development check `76532d82-786d-442d-ac20-847459a8cc9b` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the module with zero errors
and warnings. Inspection reports the sole universe parameter `u` and the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. This check
is distinct from independent semantic acceptance and publication.
