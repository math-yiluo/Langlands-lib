# Descent of ample existence along finite field extensions

`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentStatement.{u}`
is a universe-polymorphic `Prop`-valued definition. This module states the
descent result and supplies no proof.

Worker 712 implemented this pair. Worker 404 supplied the specification,
the source selection and the reuse boundaries in the task contract.

## Exact statement

The proposition quantifies over:

- fields `K L : Type u` with `[Algebra K L]` and `[FiniteDimensional K L]`;
- an actual scheme `X : Scheme.{u}`;
- a morphism `p : X ⟶ Spec (CommRingCat.of K)`.

It asserts

```text
(∃ M : LineBundle
    (CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))),
  M.IsAmple) →
  ∃ N : LineBundle X, N.IsAmple
```

Here `pullback` is Mathlib's categorical pullback in `Scheme.{u}`. Its second
leg is the spectrum of the actual structure map `algebraMap K L`, so the
pullback is the base change `X_L = X ×_{Spec K} Spec L` of the `K`-scheme
`(X, p)`. `FiniteDimensional K L` uses the module structure induced by the
algebra structure, so `L` is a finite field extension of `K`.

`LineBundle` is the published `Langlands.AlgebraicGeometry.Picard.LineBundle`:
the full subcategory of actual `X.Modules` that are locally isomorphic to the
structure sheaf. Both the hypothesis and the conclusion use the published
`LineBundle.IsAmple` unchanged. For a line bundle `M` on a scheme `Y`,
`M.IsAmple` is

```text
CompactSpace Y ∧ ∀ y : Y, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : M.powSections n,
  y ∈ M.sectionOpen s ∧ IsAffineOpen (M.sectionOpen s).
```

`M.powSections n` consists of global sections of the actual sheafified tensor
power `Langlands.Scheme.Modules.tensorPow M.obj n`, and `M.sectionOpen s` is
the largest open on which the map from the structure sheaf induced by `s` is
an isomorphism. The **whole** generation open must be affine; an affine
neighbourhood inside it does not suffice. See
`Langlands/AlgebraicGeometry/Picard/Ample.md` for these definitions and their
comparison with Stacks Definition 28.27.1.

Both existence statements are plain existentials. No compatibility between
the ample bundle on `X_L` and the bundle on `X` is asserted or assumed, and
the hypothesis bundle is not required to be a pullback from `X`.

## Scope

All universes `u`, all characteristics, separable, inseparable and mixed
finite extensions, imperfect `K`, and the trivial extension `L = K` are
included. `X` and `p` are arbitrary: there is no properness, finite type,
separatedness, projectivity, reducedness, nonemptiness or dimension
hypothesis, so dimension zero and the empty scheme are covered. There is no
algebraic closure, separability, perfectness, norm-certificate or supplied
descent-data premise. The norm bundle needed by the source proof is a future
proof obligation, not an input.

An intermediate field `E : IntermediateField K Ω` carries Mathlib's
`Field ↥E` and `Algebra K ↥E` instances. Hence the proposition applies with
`L := ↥E` whenever `FiniteDimensional K ↥E` is available, as in the
arbitrary-field route described below.

## Derived provenance

This is a derived specialization, not a literal quotation of one source
statement.

Stacks [Proposition 31.18.9, tag 0BCX](https://stacks.math.columbia.edu/tag/0BCX),
case (1), states: if `π : X → Y` is a finite surjective morphism, `X` has an
ample invertible module and `π` is finite locally free, then `Y` has an ample
invertible module. Its proof combines Lemma 31.18.6 (a finite locally free
morphism of degree `d ≥ 1` has a canonical norm of degree `d`) with Lemma
31.18.4 (if `X` has an ample invertible sheaf and `π` is finite with a norm of
degree `d`, then `Y` has an ample invertible sheaf).

The present proposition takes `π` to be the base-change projection
`X_L → X`, the first projection of the displayed pullback. It is the base
change of `Spec L → Spec K` along `p`, so it is finite locally free of
constant degree `[L : K] ≥ 1` and surjective. This is exactly the final step
of the proof of Stacks
[Lemma 33.15.1, tag 0BDB](https://stacks.math.columbia.edu/tag/0BDB): after
obtaining an ample invertible sheaf on `X_{k'}` for a finite extension
`k'/k`, it concludes "Since `X_{k'} → X` is finite locally free we conclude
that `X` has an ample invertible sheaf by Divisors, Proposition 31.18.9."
Source `k` and `k'` are renamed `K` and `L`; source invertible
`𝒪`-modules are the published actual `LineBundle`s; source ampleness is the
published `IsAmple`.

The specialization drops nothing from the conclusion and adds no hypothesis.
The finite-locally-free, surjectivity and positive-degree properties of the
projection are consequences of the field-extension setting, not premises.

## Original source and reading record

Registered source `stacks-norms-field-ample-descent-2026-10-26`, directory
SHA256 `af3256169e1d1a032cecd20fa228482bad8e1b478ccfc55a4a73c7ec187d9f5a`,
retained at
`literature/Stacks Project - Norms and field-extension ampleness descent (HTML snapshot 2026-10-26)`.
Worker 712 read on October 26, 2026 the complete retained Section 31.18
(`0BCX.html`: the definition of a norm of degree `d`, Lemmas 31.18.1–31.18.8,
Proposition 31.18.9, Lemma 31.18.10, all proofs, and its two comments) and
the complete retained Section 33.15 (`0BDB.html`: Lemmas 33.15.1–33.15.5 and
their proofs; no comments). Comment 7175 on 0BCX (2022) asks whether `V`
was defined in item (2) at the beginning of the section; the reply records
the fix for the missing declaration of `V`. The working Library base has
no erratum file for this source.

One typo in the retained proof of Lemma 31.18.4 does not affect the statement:
it says the norm section "does not vanish at `x`"; the argument requires the
point `y` of `Y` chosen there.

## Proof obligations for the future exact-target proof

Following the source, a proof of this whole proposition must, with no extra
outer hypothesis:

1. Show that the actual first projection `X_L → X` is finite, locally free of
   constant rank `[L : K] ≥ 1`, and surjective.
2. Construct the degree-`[L : K]` norm on the actual pushed-forward structure
   sheaf (determinant of multiplication, Lemma 31.18.6), with
   `Norm(g) = g^d` on pulled-back functions and the vanishing property (2).
3. Construct the norm of an actual line bundle as an actual `LineBundle X`
   (Lemmas 31.18.1–31.18.2) and the norm of sections of its tensor powers
   (Lemma 31.18.3). Compare the norm of a published `tensorPow` with the
   published `tensorPow` of the norm, so that norm sections are elements of
   the published `powSections`.
4. Prove the ampleness argument of Lemma 31.18.4: quasi-compactness of `X`
   from surjectivity; for each point a section on `X_L` whose generation
   locus contains its fibre and lies in the preimage of an affine open
   (Stacks Properties, Lemma 28.30.6, cited there); and affineness of the
   **whole** generation open of the norm section (Properties, Lemma 28.27.4,
   cited there).

The source works with nonvanishing loci. The published comparison
`LineBundle.isAmple_iff_nonvanishingLocus` is conditional on
`Langlands.SchemeModule.LineBundleResidueOpenComparison` and local rank one of
the tensor powers. Any use of it must establish or import those premises; it
cannot be used as an unconditional theorem. The Stacks Properties lemmas
cited by 0BCX are not part of the retained source and must be registered and
read by the proof's author before use.

Substantial norm constructions and generation-open lemmas belong in separate
focused definition, statement and proof tasks. They must not become outer
assumptions of the exact theorem. This module adds no axiom and discharges
none of these obligations.
