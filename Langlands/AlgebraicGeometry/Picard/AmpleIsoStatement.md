# Ampleness under an actual module-sheaf isomorphism

`Langlands.AlgebraicGeometry.Picard.AmpleIsoStatement` is the proposition

```lean
∀ (X : AlgebraicGeometry.Scheme.{u}) (L M : LineBundle X),
  Nonempty (L.obj ≅ M.obj) → L.IsAmple → M.IsAmple
```

The universe `u` is arbitrary. The scheme `X` is arbitrary, and `L` and `M`
are actual line bundles in the published full subcategory of locally free
rank-one objects of `X.Modules`. The isomorphism is an isomorphism of their
underlying module sheaves on this same scheme. `Nonempty` asserts the
existence of such an isomorphism without fixing one as part of the target.
Every isomorphism is allowed. Ampleness of `L` is the only other premise.

The file imports [Ample](Ample.lean) and preserves its definitions and the
imported [LineBundle](LineBundle.lean) definitions. It adds no separatedness,
projectivity, noetherianity, coherence, residue-comparison or tensor-power
rank-one hypothesis. Quasi-compactness is already part of `L.IsAmple`:

```lean
CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
  x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s)
```

The conclusion uses exactly that same published predicate for `M`.

## Actual tensor powers and the required open equality

The published [Tensor](../Modules/Tensor.lean) construction defines
`tensorPow P 0 = structureSheaf X` and
`tensorPow P (n + 1) = tensorObj P (tensorPow P n)`. These are actual
sheafified tensor products, associated to the right and ending in a
structure-sheaf factor. In particular the first power is
`tensorObj P (structureSheaf X)`; identifying it with `P` uses the right
unitor rather than definitional equality.

For an actual isomorphism `e : L.obj ≅ M.obj`, the published
[TensorPowerIsomorphisms](../Modules/TensorPowerIsomorphisms.lean) module
supplies `Langlands.Scheme.Modules.tensorPowIso e n` for every natural `n`.
Its endpoints are exactly the tensor powers used by `powSections`, including
their trailing units. Its hom is the existing `tensorPowMap e.hom n`.
A section `s` of the source power has an image section obtained by evaluating
this hom at the top open.

For arbitrary module sheaves `P Q : X.Modules`, an isomorphism `e : P ≅ Q`,
and `s : Langlands.SchemeModule.GlobalSections P`, the open equality needed
in the future proof is

```lean
Langlands.SchemeModule.trivializationOpen Q (e.hom.app ⊤ s) =
  Langlands.SchemeModule.trivializationOpen P s
```

This is equality of the whole opens. The published
[SectionLocus](../Modules/SectionLocus.lean) defines `trivializationOpen P s`
as the supremum of all opens where the restricted `sectionHom P s` is an
isomorphism. The published
[TensorSections](../Modules/TensorSections.lean) already proves
`Langlands.SchemeModule.sectionHom_naturality`: for every module map
`f : P ⟶ Q`, the section morphism of `f.app ⊤ s` equals
`sectionHom P s ≫ f`.

The intended derived argument applies this naturality equality on each
open and uses the restricted isomorphism and its inverse to compare the
two `TrivializesOn` predicates. Equality of the corresponding suprema
would give the displayed whole-open equality for arbitrary module sheaves,
without a rank-one or residue-field premise. Applying that equality to
`tensorPowIso e n` would transport both membership and affineness of every
whole `L.sectionOpen s`. It would retain the same positive exponent and the
same `CompactSpace X` witness. Affineness of a chosen smaller neighborhood
would not suffice for the published definition.

## Provenance and proof boundary

This is an internal derived invariance statement of the existing
`LineBundle.IsAmple` definition. Its provenance is the published
`Picard.LineBundle`, `Picard.Ample`, `Modules.SectionLocus`,
`Modules.Tensor`, `Modules.TensorSections` and
`Modules.TensorPowerIsomorphisms` constructions cited above, together with
their Markdown companions. It does not translate an additional external
literature theorem or rely on a new external source.

This module defines a proposition returning `Prop`; it does not prove that
proposition, the displayed whole-open equality, or an ampleness transport
theorem. Those are separate proof obligations. The intended proof will reuse
the published section naturality and tensor-power isomorphisms and expose
the generic whole-open isomorphism lemma for other consumers.
Workers 410 and 477 contributed the shared transport route and the reuse
observation for the published naturality lemma.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
