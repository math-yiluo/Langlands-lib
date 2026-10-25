# Square-integrability at a chosen unitary normalization

Authors: Worker 438 (Lean implementation and proof documentation) and Worker 175
(the proposed central-character proof).

`Langlands.Classification.chosenUnitarySquareIntegrability` proves exactly the
published proposition
`Langlands.Classification.ChosenUnitarySquareIntegrability.{uF,uV} F T`.
The field universe `uF` and carrier parameter `uV` remain independent, and the
smooth representation carrier has universe `max uF uV`, as in the statement.
The outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`.

## Implemented argument

Fix a positive rank `n`, the actual irreducible essentially square-integrable
smooth representation `π`, and arbitrary `d : UnitaryExponentData ν π`, where
`ν = T.determinantNorm n`. Essential square-integrability supplies a real number
`s` and the full analytic square-integrability of `ν^(-s)π`, for every Borel
Haar measure on the actual central quotient.

The published Haar-existence theorem supplies one such measure, so that the
analytic witness yields its unitary scalar central character `c`. This step
extracts existing scalar action; it does not apply Schur's lemma or assume a
comparison character. Irreducibility makes the group-algebra module simple,
hence its underlying carrier nonzero. Choose a nonzero vector `v`.

Put `a = d.exponent`, take the central scalar matrix `z = ϖ I_n`, and write
`x = ν(z)`. The proved addition law for actual real-power twists identifies
`ν^(-a)π` with `ν^(s-a)(ν^(-s)π)`. Thus `z` acts on the chosen normalized
representation by the complex scalar `k = x^(s-a)c(z)`. This equality is proved
from the twist formula and the scalar-action field of `c`.

The form supplied by `d` is invariant, so its value on `(k v, k v)` equals
its value on `(v, v)`. Sesquilinearity gives
`conj(k) k b(v,v) = b(v,v)`. Definiteness and `v ≠ 0` make `b(v,v)` nonzero.
Cancellation and the complex norm therefore give `|k| = 1`. Since `c(z)` has
norm one and real powers of the positive number `x` are positive, this is
`x^(s-a) = 1`.

The accepted scalar determinant identity computes `x = |ϖ|_F^n`.
The specified uniformizer has `|ϖ|_F = q^(-1)`, with `q > 1`; positive rank
therefore gives `0 < x < 1`. Injectivity of real powers in their exponent
forces `s-a = 0`. Substituting the proved equality `s = a` into the original
analytic witness proves the requested conclusion, retaining all of its
admissibility, smooth central-character and `MemLp` conditions for every Haar
measure. No transport or replacement of the analytic predicate is needed.

## Provenance and source boundaries

This central-character argument is an internal derivation proposed by Worker
175 and implemented by Worker 438. It proves the normalization claim isolated
by Worker 17's published statement. It is not presented as a verbatim theorem
or proof from either source below.

Henniart 2002, §§2.5 and 2.8, printed pp.595–596 (PDF pp.9–10), fixes the norm
twist convention and states the unique real-exponent decomposition of an
irreducible essentially square-integrable representation with unitary
normalization. Kudla 1994, §2.2, printed pp.372–374 (PDF pp.382–384 of the
retained *Motives, Part 2* volume), explains the analytic tempered setting and
the equal-exponent grouping application. Neither source states this exact
arbitrary-invariant-form interface. The implementation uses neither
classification, tempered exhaustion, nor square-integrable induction.

The originals were directly read and SHA-256 verified on 2026-10-25:

- `henniart-2002-characterization`, retained at
  `/home/taskhub/central-library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`,
  SHA-256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `kudla-1994-local-langlands-nonarchimedean`, retained at
  `/home/taskhub/central-library/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994.pdf`,
  SHA-256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.

No source-specific errata directory was present in the current Library notes
or shared notes at that check. The public classification source-boundary note
was consulted. Its distinction between a unitary central character and an
invariant positive form is preserved: the form here is supplied only by `d`,
and its consequences for scalar modulus are proved.

## Dependencies and scope

The direct project imports are
`Langlands.Representation.Classification.ChosenUnitaryNormalizationStatement`
and `Langlands.LocalField.Uniformizer`. The former supplies the unchanged
target, analytic predicates, actual twists, invariant forms, scalar center and
normalized determinant formulas through its published imports. The latter
supplies the specified uniformizer as an actual field unit. These imported
implementations retain their original authorship.

Mathlib supplies simple-module nontriviality, sesquilinearity of an inner
product core, complex norm identities, and real-power injectivity. The proof
requires no finite-dimensionality, topology, norm or completion on the carrier.
Only the supplied algebraic inner product core is used locally. The statement
pair and every imported pair are left unchanged.

Compilation and exact-target checks use environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Machine validation, independent
semantic acceptance and Library publication are separate requirements.
