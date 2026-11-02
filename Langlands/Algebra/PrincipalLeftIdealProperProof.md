# Proper principal left ideals

`Langlands.Renard.principalLeftIdealProper` proves the unchanged published
`Langlands.Renard.PrincipalLeftIdealProperStatement` from
`Langlands.Algebra.SeparationStatements`:

```lean
theorem principalLeftIdealProper (A : Type u) [Ring A] :
    PrincipalLeftIdealProperStatement A
```

For every `x : A`, the actual left ideal `Submodule.span A {x}` is proper if
and only if every `b : A` satisfies `b * x ≠ 1`. The carrier universe `u` is
arbitrary. The only structure required is `Ring A`; the proof imposes no
commutativity or nontriviality premise.

The implementation rewrites equality with the top left ideal using
`Ideal.eq_top_iff_one`: a left ideal is the whole regular module exactly when
it contains `1`. By `Submodule.mem_span_singleton`, membership of `1` in
`Submodule.span A {x}` means `∃ b : A, b • x = 1`. In the regular left module,
`b • x = b * x`. Negating the existence of such a `b` gives the target. This
uses only left multiplication, including in a noncommutative ring. In the
zero ring both sides of the displayed equivalence are false, so the same
proof covers that case.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, B.III, printed page 273 /
one-based PDF page 279. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The source observes that `b ↦ b * (a - λ1)` fails to be surjective because it
does not reach `1`. This general ring-theoretic equivalence is an internal
auxiliary formalizing that observation; Renard does not state it separately.

Worker 1210 read B.III as extracted text and as a rendered page, and checked
the source hash. The older-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF18–19,
were read and their hash checked. The PDF19 correction keeps the condition
that the shift has no left inverse and removes the right-zero-divisor claim.
That corrected condition is already present in the 2026 source. No separate
Renard errata note was present in the current Library.

Worker 1210 wrote this proof and explanation. The published statement and its
informal proof outline are due to Worker 221 and Worker 6. The proof uses
Mathlib's actual `Submodule A A` left ideals. Its role is the properness step;
the simple-quotient and unital-separation conclusions have separate proofs.

Development check `ecdf093c-3fe0-4dc9-a91a-d95bfb6ec7e8` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the module with zero errors
and warnings. Declaration inspection reports the sole level parameter `u`
and axioms `propext` and `Quot.sound`. Independent acceptance and publication
remain separate from this development check.
