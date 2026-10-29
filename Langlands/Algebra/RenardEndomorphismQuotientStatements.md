# Injectivity on the power-kernel quotient and its localization comparison

Authors: Worker 911.

This statement module states three remaining claims of Renard's lemma (ii)
about the actual power-kernel quotient: the induced operator a' is
injective; the canonical map ι' of the quotient into its own localization
is injective; and the localization of the quotient at a' is canonically
equivalent to the localization of the original module at a. It imports
the published definition module `Langlands.Algebra.RenardEndomorphismQuotient`
(and through it `Langlands.Algebra.RenardEndomorphismLocalization`). Every
declaration is a Prop-valued `def` in namespace
`Langlands.Renard.EndomorphismLocalization`; nothing is proved here.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, A.III.1, unnumbered lemma (ii) after example 5,
printed253/PDF259; example 5 (the localization of a vector space with an
endomorphism) is on printed252/PDF258. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary author errata `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, contain no entry for this lemma.

Over a field k, with L a k-vector space, a an endomorphism, K the union of
the kernels of the powers of a, L' = L/K and a' the induced endomorphism,
lemma (ii) states:

1. the localization (L'_{a'}, ã') of L' at a' is isomorphic to the
   localization of L at a;
2. a' is injective, and so is the canonical morphism ι' from (L', a') to
   (L'_{a'}, ã');
3. hence L'_{a'} is an extension of L' on which ã' agrees with a', and
   L'_{a'} is the union over n in ℕ of (ã')^{-n}(L').

The two injectivity claims of item 2 are original source content. Item 1
says only "isomorphe"; the proof obtains the isomorphism from the two
universal properties after factoring ι through L'. The comparison stated
here is a derived, more precise form of item 1: it names the equivalence by
its compatibilities with the canonical maps and the localized operators,
and asserts that exactly one such equivalence exists. The extension from
fields to arbitrary commutative unital rings is internal; the field case is
also stated separately.

## Hypotheses and universes

Each statement quantifies over a ring `R : Type u` with `[CommRing R]`, a
carrier `V : Type v` with `[AddCommGroup V] [Module R V]`, and
`a : Module.End R V`; the field statement uses `k : Type u` with `[Field k]`
instead of R. The universes u and v are independent. No finite dimension,
finite generation, Noetherianity, nontriviality, injectivity of a, nonzero
a or stabilization of the power kernels is assumed. Zero rings, zero
modules and nilpotent a are permitted; for nilpotent a the quotient is the
zero module.

The actual objects are the published ones:

| Source object | Lean term |
| --- | --- |
| K, L' = L/K, projection L → L' | `powerKernel a`, `PowerKernelQuotient a`, `quotientProjection a` |
| a' | `quotientEnd a` |
| (L_a, ã) and ι | `Localized a`, `localizedEnd a`, `iota a` |
| (L'_{a'}, ã') and ι' | `Localized (quotientEnd a)`, `localizedEnd (quotientEnd a)`, `iota (quotientEnd a)` |

Both localizations live in `Type (max u v)`, so the equivalence below is
between types in the same universe.

## Statements

- `QuotientEndInjectiveStatement`: for all R, V and a,
  `Function.Injective (quotientEnd a)`. This is the source's "a' est
  injectif".
- `QuotientIotaInjectiveStatement`: for all R, V and a,
  `Function.Injective (iota (quotientEnd a))`. This is the source's
  injectivity of ι'. It is stated unconditionally; the source derives it
  from the injectivity of a' and part (i).
- `QuotientLocalizationComparisonStatement`: for all R, V and a there is a
  unique `e : Localized (quotientEnd a) ≃ₗ[R] Localized a` such that

  ```lean
  e.toLinearMap.comp ((iota (quotientEnd a)).comp (quotientProjection a)) = iota a ∧
    ∀ z : Localized (quotientEnd a),
      e (localizedEnd (quotientEnd a) z) = localizedEnd a (e z)
  ```

  The first conjunct says e ∘ ι' ∘ π = ι, where π is the quotient
  projection; the second says e intertwines ã' and ã. Uniqueness is taken
  among R-linear equivalences satisfying both conditions.
- `QuotientLocalizationStatement`: the conjunction of the three ring
  statements, at universes u and v.
- `FieldQuotientLocalizationStatement`: for every field `k : Type u`, every
  k-vector space `V : Type v` and every `a : Module.End k V`, the
  conjunction of the same three conclusions with k in place of R. This is
  the source's own setting at arbitrary dimension.
- `QuotientLocalizationStatements`: the closed aggregate
  `QuotientLocalizationStatement.{u, v} ∧ FieldQuotientLocalizationStatement.{u, v}`,
  the intended single proof target.

The field statement is a specialization of the ring statement; it is
included so that the source's exact case is a named target.

## Not stated here

None of the following is stated, assumed or restated by this module.

- The agreement of ã' with a' on the image of L' is the published theorem
  `iota_intertwines` applied to `quotientEnd a`.
- The kernel theorem for `iota a` (its kernel is K:
  `KernelCriterionStatement`, `KernelUnionStatement`) and the inverse-power
  exhaustion (`PowerExhaustionStatement`) belong to the aggregate
  `KernelExhaustionStatements` in
  `Langlands.Algebra.RenardEndomorphismLocalizationStatements`, owned by
  task `4d1cd271-3226-4c21-9ca0-5a22d89c6fa3`. The source's
  L'_{a'} = ⋃ (ã')^{-n}(L') is the instance of `PowerExhaustionStatement`
  at `quotientEnd a`.
- The converse universal characterization of inverse-power extensions is
  stated in `Langlands.Algebra.RenardLocalizationExtensionStatements`.
- The corollary for surjective ι, the general possibly noncommutative and
  nonunital B-action extension, categorical packaging, localization
  exactness and the final C.II finite-localization proposition remain
  separate obligations of the Renard parent task.
