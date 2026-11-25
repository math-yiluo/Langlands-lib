# Statement: central semisimple Lie elements and their centralizers

`Langlands.GroupScheme.Lie.SemisimpleCentralElementStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Lie.ElementCentralizer`](ElementCentralizer.md), for `elementCentralizer` and
  `elementCentralizerLie`.
- [`Lie.SemisimpleElement`](SemisimpleElement.md), for `IsSemisimpleElement`.
- [`Reductive.Basic`](../Reductive/Basic.md), only so that `Smooth` and the other
  group-scheme vocabulary over a field are in scope.

## Lean statement

```lean
def SemisimpleCentralElementStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (X : lieKernel G k), IsSemisimpleElement G X →
      (elementCentralizerLie G X = ⊤ ↔ elementCentralizer G X = ⊤)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X.left`
  is the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `lieKernel G k`: the actual Lie algebra `𝔤 = Lie(G)`, the kernel of `G(k[ε]) → G(k)`
  (written multiplicatively; `Additive (lieKernel G k)` is the `k`-module).
- `IsSemisimpleElement G X` ([`Lie.SemisimpleElement`](SemisimpleElement.md)): for every
  finite-dimensional algebraic representation `ρ : G → GL_n`, the differential `dρ(X)` is
  semisimple after extending scalars to the algebraic closure of `k`.
- `elementCentralizer G X` ([`Lie.ElementCentralizer`](ElementCentralizer.md)): the subgroup
  functor `C_G(X)` of points of `G` that fix `X` under the adjoint action, after every affine
  refinement of the test scheme. `elementCentralizer G X = ⊤` says `C_G(X) = G`.
- `elementCentralizerLie G X` ([`Lie.ElementCentralizer`](ElementCentralizer.md)): the tangent
  submodule `Lie(C_G(X)) ⊆ 𝔤`, the dual-number points of `C_G(X)`. The published theorem
  `mem_elementCentralizerLie_iff_adjointDifferential`
  ([`Lie.AdjointDifferentialCentralizer`](AdjointDifferentialCentralizer.md)) proves that,
  in any finite coordinate system `c : FiniteCoordinates G d`, `Y` lies in it exactly when
  `adjointDifferentialFamily c Y` (the matrix of `ad(Y)`, the differential of the adjoint
  representation at `Y`) kills the coordinates of `X`. Since Milne defines the bracket by
  `[Y, X] = ad(Y)(X)` (10.22), this submodule is `z_𝔤(X) = {Y ∈ 𝔤 | [Y, X] = 0}`, the
  identification `Lie(C_G(X)) = z_𝔤(X)` of Proposition 17.76. So
  `elementCentralizerLie G X = ⊤` says `z_𝔤(X) = 𝔤`, that is, `X` is central in `𝔤`. The
  published `SemisimpleCentralizerSpanningStatement` uses `elementCentralizerLie G X ≠ ⊤`
  for "noncentral" in the same way.

## Statement and quantifiers

For every field `k : Type u`, every smooth, affine, connected group scheme `G` over `Spec k`
and every semisimple element `X` of `Lie(G)`: `X` is central in `Lie(G)` (its tangent
centralizer is all of `Lie(G)`) if and only if its centralizer `C_G(X)` is all of `G`, as a
subgroup functor on all schemes over `Spec k`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16. The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`) has the same
wording and printed pages for 17.76 and 17.77.

- Corollary 17.77, p.377: "A semisimple element X of g is central if and only if
  C_G(X) = G."
- Before Proposition 17.76, p.377: "Let g be a Lie algebra over a field k (not necessarily
  perfect). We say that an element X of g is semisimple if ρ(X) is semisimple for all
  representations ρ of g. ... Let G be a connected group variety over a field k, and let
  X ∈ g. Then G acts on g through the adjoint representation, and we let C_G(X) denote the
  subgroup of G fixing X."
- Proposition 17.76, p.377: "If X is semisimple, then C_G(X) is a smooth algebraic subgroup
  of G, and Lie(C_G(X)) = z_g(X) = {Y ∈ g | [Y, X] = 0}."
- Proof of Corollary 17.77, p.377: "By definition, X is central if and only if z_g(X) = g.
  As C_G(X) is smooth and G is connected, C_G(X) = G if and only if Lie(C_G(X)) = Lie(G)
  (see 10.15), i.e., if and only if z_g(X) = g."
- 10.22, p.193: "On applying the functor Lie to Ad, we get a homomorphism of k-vector spaces
  ad: g → End(g). For x, y ∈ g, define [x, y] = ad(x)(y)."
- Proposition 10.15, p.190 (p.191 in the 2022 reprint): "Let H ⊂ G be algebraic groups such
  that Lie(H) = Lie(G). If H is smooth and G is connected, then H = G."
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are affine over a base
  field k"; remark after 1.26, p.13 (p.14 in the 2022 reprint): "“group variety” = “smooth
  algebraic group”."

The official errata snapshot of 2026-11-02 for the 2017 printing (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for pp.13, 190, 193, 352 or
377. The errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`) has no entry for reprint pp.14, 191, 193,
352 or 377.

## Derivation from the source

- **Connected group variety.** `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`,
  `[ConnectedSpace G.X.left]`: the setting before 17.76 is a connected group variety over an
  arbitrary field, and Chapter 17 assumes algebraic groups are affine.
- **Semisimple elements.** Milne tests `ρ(X)` for all representations `ρ` of the Lie algebra.
  This statement uses the Library's convention `IsSemisimpleElement`, which tests the
  differentials of algebraic representations of `G` and asks for semisimplicity after
  extension to an algebraic closure. This is the convention of the published
  `SemisimpleCentralizerSmoothStatement` (the smoothness part of 17.76). The statement does
  not claim that the two conventions agree.
- **Central.** Milne defines `X` central by `z_𝔤(X) = 𝔤`. As explained above, the Library's
  `elementCentralizerLie G X` is `z_𝔤(X)` by a published theorem, so centrality is
  `elementCentralizerLie G X = ⊤`.
- **`C_G(X) = G`.** Equality of the all-test subgroup functor with `⊤`.

Milne's proof works with this convention, as explanation only. If `C_G(X) = G`, its tangent
submodule is all of `Lie(G)`; this direction holds for every `X`. Conversely, a closed
representative of `C_G(X)` is smooth for semisimple `X` (the published
`SemisimpleCentralizerSmoothStatement`), its Lie algebra is then all of `Lie(G)`, and
Proposition 10.15 gives `C_G(X) = G` because `G` is connected.

## Related Library results

- [`SemisimpleCentralizerSmoothStatement`](SemisimpleCentralizerSmoothStatement.md) states
  smoothness of closed representatives of `C_G(X)` for semisimple `X` (Milne 17.76).
- [`ElementCentralizerRepresentability`](ElementCentralizerRepresentability.md) proves that
  `C_G(X)` has a closed representative for affine, locally finite type `G` over a field
  (`elementCentralizer_isClosedRepresentable`).
- [`SemisimpleCentralizerSpanningStatement`](SemisimpleCentralizerSpanningStatement.md)
  (Milne 17.79) uses `elementCentralizerLie G X ≠ ⊤` for noncentral semisimple elements.

The Library proves the same centralizer equivalence in [Semisimple centrality](SemisimpleCentrality.md), where the affine and smooth instances occur in the opposite order.
