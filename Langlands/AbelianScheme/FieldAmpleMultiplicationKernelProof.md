# Finite multiplication kernel from an ample pullback identity

`Langlands.GroupScheme.fieldAmpleMultiplicationKernel` proves exactly the
published proposition
`Langlands.GroupScheme.FieldAmpleMultiplicationKernelStatement.{u}`.
The statement and its imported constructions are unchanged. The four geometric
prerequisites are imported as proved theorems, with no additional hypotheses.

## Implemented proof

Fix the field `K`, the commutative group scheme `G`, the ample line bundle `L`,
the positive natural number `n`, and the stated actual sheaf isomorphism. Write
`f := multiplication G (n : ℤ)`, let `i` be the underlying scheme morphism of
`kernelι f`, let `p := (kernel f).X.hom`, and let `e := η[G.X].left` be the
identity section. Define the actual line bundles

```text
M := (LineBundle.pullback f.hom.hom.left).obj L,
N := (LineBundle.pullback i).obj M.
```

The underlying sheaf of `M` is definitionally the actual multiplication
pullback in the hypothesis. Apply
`Langlands.AlgebraicGeometry.Picard.positiveTensorPowerAmple` at exponent
`n * n`, using `Nat.mul_pos hn hn` and that hypothesis, to prove `M.IsAmple`.
Properness of `G.X.hom` supplies separatedness, so the published
`kernelι_isClosedImmersion` instance makes `i` a closed immersion. Apply
`closedImmersionPullbackAmple` to obtain `N.IsAmple`. No separate tensor-power
line-bundle constructor is needed: `M` is already an actual line bundle.

The over-category identity `(kernelι f).hom.hom.w` writes `p` as the composite
of `i` with `G.X.hom`. A closed immersion is proper, and proper morphisms
compose; this supplies `IsProper p`.

Apply `fieldLineBundleTriviality` to `(LineBundle.pullback e).obj L` to choose
an actual sheaf isomorphism `he` from the identity-section pullback to the
structure sheaf of `Spec K`. The equality of composites in
`kernel_isPullback_scheme f` is `i ≫ f.hom.hom.left = p ≫ e`. The implemented
trivialization of `N.obj` is the following chain of actual sheaf isomorphisms:

```text
i* (f* L) ≅ (i ≫ f)* L ≅ (p ≫ e)* L ≅ p* (e* L)
            ≅ p* O_(Spec K) ≅ O_(kernel f).
```

The first arrow is `Scheme.Modules.pullbackComp i f.hom.hom.left` evaluated
at `L.obj`; the second is `pullbackCongr` evaluated at the kernel-square
equality. The third is the inverse of `pullbackComp p e`, the fourth maps
`he` through `Scheme.Modules.pullback p`, and the fifth is
`Langlands.Scheme.Modules.pullbackUnitIso p`.

Finally apply `properAmpleTrivialFinite` to the scheme `(kernel f).X.left`,
its structure morphism `p`, and the line bundle `N`, with the properness,
ampleness and trivialization just proved. Its conclusion is `IsFinite p`,
which is exactly the target. That imported criterion derives quasi-affineness
from the ample trivial bundle and uses properness to obtain finiteness.

## Provenance and source correspondence

This is the finite-kernel argument in the first proof paragraph of J. S.
Milne, *Abelian Varieties*, Theorem 8.2, p.13, in the author's corrected
January 2, 2022 version of the 1986 article. The registered source is
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`, retained at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Printed and one-based PDF page numbers agree.

Milne uses a symmetric ample invertible sheaf to obtain the multiplication
pullback formula, then restricts it to the closed kernel. The published target
supplies the ample bundle and the actual formula explicitly. The present proof
therefore uses those inputs directly. It implements the source's ample and
trivial restriction argument, with the final proper ample-trivial finiteness
criterion in place of the source's dimension-zero intermediate step.

The ampleness predicates and pullbacks are the published actual module-sheaf
constructions. The positive-power and closed-pullback theorems establish
ampleness using equality of the whole generation opens of actual sections;
their proofs include the tensor rank-one and pullback/tensor comparisons they
need. Their companions describe the correspondence with Stacks Project
Lemma 28.27.2 (tag `01PT`) and Lemma 28.27.3 (tag `01PU`), in registered source
`stacks-ample-powers-restriction-quasiaffine-2026-10-24`. The proper ample-trivial
criterion uses the independently proved whole-generation-open quasi-affineness
argument. No conditional residue-comparison or tensor-coherence premise is
assumed by this proof.

## Scope

The theorem retains the arbitrary universe and field of the statement and
proves finiteness of the whole scheme-theoretic kernel's structure morphism.
It includes dimension zero and positive characteristic dividing `n`, with
possible nonreduced kernels. The proof uses the properness assumption; the
smoothness and geometric-connectedness assumptions remain in the exact target
but are unused in this argument. No symmetry, projectivity, flatness, isogeny,
or extra finite-kernel assumption is added.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
