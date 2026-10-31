# Homology comparison for acyclic terms and acyclic homology

Authors: Worker 595; Worker 360 supplied the statement specification and
dimension-shifting rationale in the task.

`Langlands.Cohomology.AcyclicTermsHomologyComparisonStatement` is a
proposition definition. This pair states a comparison and contains no proof
of that proposition. Its proof is a separate exact-proof obligation after
independent statement acceptance and Library publication.

## Statement and conventions

Let C and D be abelian categories, with four independent object and
morphism universes, and assume `HasInjectiveResolutions C`. Let
`F : C ⥤ D` be additive and preserve finite limits. In this setting,
`PreservesFiniteLimits F` expresses left exactness.
Let `K : CochainComplex C ℕ` be an arbitrary nonnegative cochain complex.
The hypotheses are exactly:

1. Every term is F-acyclic:
   `IsZero ((F.rightDerived (r + 1)).obj (K.X i))` for all natural
   numbers i and r.
2. Every homology object is F-acyclic:
   `IsZero ((F.rightDerived (r + 1)).obj (K.homology i))` for all
   natural numbers i and r.

Here `r + 1` ranges over all positive derived degrees. The second condition
does not require the homology objects themselves to be zero.
`Functor.rightDerived` is Mathlib's actual right derived functor, and
`IsZero` means that the displayed object in D is a zero object.

For every natural number n, including zero, the conclusion is

```lean
Nonempty
  ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) ≅
    F.obj (K.homology n))
```

Thus the homology of the complex obtained by applying F term by term is
isomorphic to F applied to the homology of K. Mathlib calls the object
`homology` even for the cochain shape `ComplexShape.up ℕ`; the differentials
raise degree.

The complex need not be exact and need not resolve an object. There is no
augmentation, upper bound, finite-length hypothesis, injectivity hypothesis
on its terms, or assumption that F is exact. The natural-number grading
supplies the lower bound. All the category, functor and complex data are
quantified inside the Prop-valued definition.

The conclusion asserts only objectwise existence of isomorphisms through
`Nonempty`. It specifies no chosen comparison morphism, no canonical
isomorphism and no naturality in K, F or n. It neither constructs nor
assumes a spectral sequence or a degeneration certificate. There are no
geometric hypotheses.

## Derived mathematical provenance

This is an internal derived statement, motivated by dimension shifting
with the long exact sequence of right derived functors. It is not
attributed to an external theorem verbatim. The following argument explains
its intended mathematical provenance; it is not an implemented Lean
proof.

Write Bⁿ, Zⁿ and Hⁿ for the boundaries, cycles and homology of K.
In an abelian category the relevant short exact sequences are

```text
0 → Bⁿ → Zⁿ → Hⁿ → 0,
0 → Zⁿ → Kⁿ → Bⁿ⁺¹ → 0.
```

At the lower bound B⁰ is zero. It is therefore F-acyclic. If Bⁿ is
F-acyclic, the first sequence and the assumed acyclicity of Hⁿ give
acyclicity of Zⁿ. In the second sequence, the assumed acyclicity of Kⁿ
and the acyclicity of Zⁿ then give acyclicity of Bⁿ⁺¹ by dimension
shifting. Induction supplies acyclicity of all boundaries and cycles.
This explains why a lower bound matters and why the argument does not
require an upper bound.

Left exactness and the vanishing of the first right derived functor on
the left terms make the two sequences remain short exact after applying
F. The resulting kernel and quotient identifications yield the displayed
homology isomorphism, including in degree zero.

The current Library's
[RightDerivedSequence](../RightDerivedSequence.md) supplies
`Langlands.Cohomology.DerivedPlus.rightDerived_exact₂`,
`rightDerived_exact₁`, `rightDerived_exact₃` and
`shortExact_map_of_isZero_rightDerived_one` for this route.
[ComparisonProof](ComparisonProof.md) contains
`Langlands.Cohomology.AcyclicComparison.isZero_rightDerived_cycles` and
`acyclic_map` for an exact bounded-below complex. Those results explain
the related dimension-shifting method, but their exactness hypothesis
does not cover the present complex with possibly nonzero homology.
The category and universe conventions agree with
[the acyclic-resolution statements](Statement.md).

The Lean file imports only
`Mathlib.CategoryTheory.Abelian.RightDerived`; no additional construction
is needed to express this proposition. It uses the project's environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.

## Intended finite-support Leray application

For a morphism of schemes h and a module M, let I be an injective
resolution of M and let K be its termwise pushforward along h.
Its homology objects represent the higher direct images of M.
With F given by the relevant global-sections functor, the intended use
has two separate inputs: injective-pushforward acyclicity for the terms
of K, and a geometric acyclicity theorem for its homology objects when
they have finite closed support.

Once those inputs and a proof of this comparison are available, it would
identify the homology of global sections of K with global sections of
each higher direct image. If the former vanishes in the required degrees,
finite-support detection could then force those higher direct images to
vanish. The resolution identifications, geometric acyclicity, total
vanishing and finite-support detection must all be supplied separately.
This statement supplies none of those geometric conclusions and does not
assume the higher-direct-image vanishing that the application seeks.
