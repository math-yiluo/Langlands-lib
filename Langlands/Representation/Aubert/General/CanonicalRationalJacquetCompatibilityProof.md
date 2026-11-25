# Proof of canonical Jacquet compatibility

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalJacquetCompatibilityStatement`
(module `CanonicalRationalTheorem17Targets`) at universes `u`, `v`:

`theorem canonicalRationalJacquetCompatibility :
  CanonicalRationalJacquetCompatibilityStatement.{u, v}`.

The target is the second equation of Aubert (1995), Théorème 1.7 (2),
`r_J ∘ D_G = Ad(n) ∘ D_(M_J') ∘ r_J'`, stated for the canonical actual operator
of every connected reductive group over every nonarchimedean local field, with
the canonical Coxeter system and every normalizer lift `n` of the longest
element of `D(J, ∅)`. The statement module's Markdown describes the statement,
its meaning and its provenance. This file describes only the Lean proof.

The theorem proves the whole proposition. Like every target of that module,
the proposition is itself an implication from its two global dynamic
finite-length binders `hiFl : DynamicInductionFiniteLengthStatement` and
`hrFl : DynamicJacquetFiniteLengthStatement`. The proof keeps them as binders
of the proposition. It does not discharge them and adds no other hypothesis.

## Proof

The proof is a single term:

```
canonicalRationalJacquetCompatibility_of_rational.{u, v}
  rationalJacquetCompatibility.{u, v}
```

1. `rationalJacquetCompatibility : RationalJacquetCompatibilityStatement.{u, v}`
   (module `RationalJacquetCompatibilityProof`) is the published
   proof of the existing rational-point target. That target quantifies every
   Coxeter system and all structural premises.
2. `canonicalRationalJacquetCompatibility_of_rational`
   (module `CanonicalRationalTargetBridgesProof`, the published proof of
   `CanonicalRationalTargetBridgesStatement`) proves
   `RationalJacquetCompatibilityStatement.{u, v} →
   CanonicalRationalJacquetCompatibilityStatement.{u, v}`. It specializes the
   rational target to the canonical topology, torus, cocharacter and relative
   root system, the standard Levi data, the canonical Coxeter system and the
   published normalizer, centralizer, root-length, simple-reflection,
   minimality and associated-subset comparisons. It passes the target's own
   `hiFl` and `hrFl` to the finite-length premises.

The universe arguments are passed explicitly, so both declarations are used
at exactly the universes of the conclusion.

All modules named are in `Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commit
`2016a0d994180c702214a75514a08546aa930f07`). Against that Library, the module compiles with
zero errors and zero warnings. The theorem has level parameters `u`, `v` and
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
