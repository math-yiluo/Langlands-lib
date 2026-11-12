# Complex scalars on the actual corner-induction quotient

Worker 133, Task 5342 (`115b38ac-7e1e-4790-b21b-ce3c753617f9`).

The theorem
`Langlands.Algebra.NonUnitalModuleCornerInduction.complexScalarsStatement`
proves exactly the published proposition
`Langlands.Algebra.NonUnitalModuleCornerInduction.ComplexScalarsStatement`.
It retains the independent universes `uA` and `uZ`, all published objects,
and the statement's hypotheses.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
I.3.2, remark after Lemma (I.3.2.1), printed p.20 / PDF p.26.
Worker 133 read the surrounding text on PDF pp.25–26. The source asserts
that the two complex vector-space structures coincide without giving a
proof of that assertion. The argument below is an internal algebraic
proof using the published corner and balanced quotient. The statement
unit explains why the assertion holds without local units or
nondegeneracy, and these assumptions are not added here.

## Implemented proof

For a scalar `c`, both left and right multiplication by the idempotent
`e` fix `c • e`; hence it belongs to `Idempotent.Corner e`. The map
`c ↦ c • e` is a unital ring homomorphism: additivity follows from
`add_smul`, preservation of the unit from `one_smul`, and preservation of
multiplication from the two compatibility hypotheses for the complex
algebra and the identity `e * e = e`. Restricting the given unital corner
module structure on `Z` along this homomorphism with `Module.compHom`
proves the first clause, with precisely the action of the corner element
`c • e`.

On the published quotient `Tensor e Z`, fix `c` and consider the
biadditive map `(a, z) ↦ tmul e (c • a) z`. Compatibility of scalars with
multiplication on `A`, followed by `tmul_balanced`, proves that this map
is balanced for the published right corner action on `A` and left
corner action on `Z`. `NonUnitalModuleTensor.lift` therefore descends it
to an additive endomorphism of the actual quotient.

These endomorphisms form a unital ring homomorphism from `ℂ` to
`AddMonoid.End (Tensor e Z)`. Each law is checked on pure tensors using
`NonUnitalModuleTensor.hom_ext`; zero and addition also use
`zero_tmul` and `add_tmul`. Restrict the canonical endomorphism module
structure along this homomorphism with `Module.compHom`. Its action on
a pure tensor is definitionally `tmul e (c • a) z`, proving the first
formula of the second clause.

Finally, for every corner element `s` whose ambient value is `c • e`,
unitality of `Z`, balancing by the corner unit, compatibility of complex
scalars with multiplication, and balancing by `s` give

```text
(c • a) ⊗ z
  = ((c • a) * e) ⊗ z
  = (a * (c • e)) ⊗ z
  = a ⊗ (s • z).
```

This proves the second formula for every such `s`, as the published
statement requires. All scalar structures are built on the specified
additive groups; the proof uses no replacement tensor carrier.

## Scope and dependencies

The only direct import is the published statement module
`Langlands.Algebra.NonUnitalModuleCornerInductionComplexScalarsStatement`.
Its Lean/Markdown pair and complete import closure are unchanged.
The proof is checked in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
