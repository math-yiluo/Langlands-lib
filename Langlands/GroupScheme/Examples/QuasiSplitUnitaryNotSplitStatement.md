# The quasi-split unitary group `U(1,1)` has no split maximal torus: statement

Author: Worker 15, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). The module contains one
`Prop`-valued definition and no proof.

## The statement

`Langlands.GroupScheme.QuasiSplitUnitary.NotSplitStatement` says the following. Let
`F` and `E` be fields in one universe `u`, with `[Algebra F E]` and
`[Algebra.IsQuadraticExtension F E]`. Let `κ` be a finite type in universe `u`, let
`b` be an `F`-basis of `Matrix (Fin 2) (Fin 2) E` indexed by `κ`, and let
`c : E ≃ₐ[F] E` satisfy `c ≠ AlgEquiv.refl`. Then
`¬ HasSplitMaximalTorus (groupScheme b c)`.

Here `groupScheme b c` is the group scheme `U(1,1)` over `Spec (CommRingCat.of F)` of
`Langlands.GroupScheme.Examples.QuasiSplitUnitary`. It is the unitary group of the
hermitian form `h(v, w) = v₁ c(w₂) + v₂ c(w₁)`, with antidiagonal Gram matrix
`J = !![0, 1; 1, 0]`. The full unitary equation is imposed, with no determinant
condition. These are the same data, binders and hypotheses as in the sibling
statements `RankStatement`, `NonCommutativeStatement` and
`IsConnectedReductiveStatement`.

`HasSplitMaximalTorus G` is the Library predicate of
`Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal`. It holds when there are a
commutative group scheme `T` over `Spec F` and a homomorphism `i : T ⟶ G` with
`IsSplitTorus T` and `IsMaximalTorus i`. `IsSplitTorus T` means that `T` is isomorphic
to `𝔾ₘ^I` for a finite index type `I`. `IsMaximalTorus i` means that `T` is a torus,
that `i` is a closed immersion, and that `i` factors through no strictly larger closed
torus of `G`. The statement therefore says that no maximal torus of `U(1,1)` is split
over `F`.

No assumption on the characteristic of `F` is made, so the statement covers
characteristic `2`.

## Source and provenance

Milne, *Algebraic Groups* (2022 corrected reprint), source `milne-2022-algebraic-groups`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`:

- Definition 19.22, printed p.402 (PDF p.413): "A reductive group `G` is splittable if
  it contains a split maximal torus." Milne adds that "we often say that a reductive
  group `G` is split when we mean splittable."
- Definition 19.20 on the same page defines the rank and the `k`-rank as the
  dimensions of a maximal torus and of a maximal split torus. The following paragraph
  notes that maximal tori stay maximal under field extension (17.82) and become
  conjugate after extension (17.87).

`U(1,1)` is connected reductive (`IsConnectedReductiveStatement`), so the predicate
`HasSplitMaximalTorus` has Milne's meaning here. The statement is the assertion that
`U(1,1)` is not split over `F`. It is derived for this program, which asks for a
concrete noncommutative non-split unitary example with proved non-splitting. Milne
does not state this particular result.

`RankStatement` already gives the rank form: every closed split torus of `U(1,1)` over
`F` has rank at most one, while the base change to `E` contains a closed split torus of
rank two. `NotSplitStatement` is the split-group formulation itself. Deducing it
requires the comparison of maximal tori after field extension, which is a proof
obligation and not part of this statement.
