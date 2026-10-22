# Finite unramified stages under a specified closure embedding

The theorem
`Langlands.ClassFieldTheory.Local.unramifiedBaseChangeStageExistence.{u}`
proves exactly the published proposition
`Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeStageExistence.{u}`.
The input includes the actual algebra structure `Fbar → Ebar` and its
compatibility with `F`. The output is an actual
`FiniteIntermediateExtension E.Carrier`, with Galois and canonical
unramifiedness certificates and containment of the specified image of every
element of the source stage `L`.

Here `Fbar` and `Ebar` abbreviate the existing `AlgebraicClosure` types.
The proof applies in every common universe `u`, includes degree-one cases,
and does not require `E/F` to be Galois or the output stage to be normal over
`F`. It introduces no additional premise and changes no published statement
or construction.

## Implemented proof

Write `f : F →ₐ[Q_p] E` for the homomorphism given by the supplied scalar
tower. Let `j = extensionGaloisMap F E f : G_E → G_F` be the published
continuous absolute Galois homomorphism and let
`e = extensionClosureEquiv F E f : Fbar ≃+* Ebar` be its chosen closure
isomorphism. The specified closure map, denoted by `b` below, need not equal
`e`.

The subgroup

```text
N = j⁻¹(L.field.fixingSubgroup)
```

is open because the fixing subgroup of a finite extension is open and `j`
is continuous. It is normal because `L/F` is Galois and inverse images
preserve normality. The proof bundles it as an `OpenNormalSubgroup`, then
defines `M.field` to be `finiteStageFixedField E.Carrier N`. The published
fixed-field stage instances provide the finite-dimensional and Galois
certificates. The infinite Galois correspondence identifies
`M.field.fixingSubgroup` with `N.toSubgroup`; openness ensures that `N` is
closed, as required for this correspondence.

To prove unramifiedness, the proof first applies
`Langlands.PadicField.canonicalUnramifiedCriterion` to the hypothesis on
`L`. This says that the canonical inertia subgroup `I_F` fixes `L`.
For `σ ∈ I_E`, the published residue compatibility
`localResidueMap_extensionGaloisMap` gives

```text
localResidueMap F (j σ)
  = extensionResidueGaloisMap F E f (localResidueMap E σ)
  = 1.
```

The kernel identities `absoluteResidueHom_ker` identify this assertion with
`j σ ∈ I_F`. Hence `j σ` fixes `L`, so `σ ∈ N`. Applying the canonical
criterion to `M` now gives exactly the equality of the canonical absolute
ramification indices of `E` and `M.asPadicField` used in the target. No new
valuation structure or comparison with a separately normalized index is
introduced.

For the specified-image containment, form the `F`-algebra endomorphism

```text
c = e⁻¹ ∘ b : Fbar →ₐ[F] Fbar.
```

Its scalar compatibility follows from
`extensionClosureLift_algebraMap` and the supplied scalar tower through
`Fbar`, together with the ordinary tower through `E`. Restricting `c` to
`L` gives `g : L →ₐ[F] Fbar`. Since `L/F` is normal,
`AlgHom.fieldRange_of_normal g` gives `g.fieldRange = L.field`. Thus
`g a ∈ L.field` for every `a : L.field`.

If `σ ∈ N`, then `j σ` fixes `g a`. The defining compatibility
`extensionClosureLift_galoisMap` implies

```text
σ (e (g a)) = e ((j σ) (g a)) = e (g a).
```

Since `e (g a) = b a`, every element of the prescribed image is fixed by
`N`, and therefore lies in `M.field`. This proves the required containment
for the original specified map, even though the intermediate subgroup
construction used the published chosen closure isomorphism. No claim that
`M` is the smallest overfield or any degree formula is needed or proved.

## Dependencies and provenance

The statement's source is Jean-Pierre Serre, *Local Fields*, translated by
Marvin Jay Greenberg, Springer, 1979, Chapter III, section 5, Theorems 2 and
3 and their corollaries, printed pages 54–55, PDF pages 61–62. These pages
classify finite unramified extensions by separable residue extensions and
identify embeddings by their residue maps. The exact specified-closure
containment statement is a derived consequence, rather than a verbatim
statement in Serre. The retained original is registered as
`serre-1979-local-fields`, at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The implemented route instead uses the already proved canonical inertia
criterion and residue compatibility from the Library, plus Mathlib's
infinite Galois correspondence and normality API. Its direct imports are
`UnramifiedBaseChangeStatement`, `FixedFieldStages`, and
`Langlands.Galois.Local.UnramifiedCriterionProof`; the last supplies the
necessary local Weil extension interfaces through its imports. The
fixed-field and comparison constructions above are internal to this proof.
The theorem-local transparency option only assists elaboration of existing
absolute Galois group presentations; it adds no mathematical assumption.

Authored by Worker 107. Worker 154 confirmed that the published target
matches the downstream assembly interface; no unpublished peer proof was
used.
