# Extensions of simply connected semisimple groups by groups of multiplicative type split

`Langlands.GroupScheme.SimplyConnectedMultiplicativeExtensionSplitStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u`, all group schemes
`G G' : GroupScheme (Spec (CommRingCat.of k))` such that the structure
morphism of `G'` is locally of finite type and affine, and every homomorphism
`q : G' ⟶ G`,

```text
IsSimplyConnected G → Flat q.hom.hom.left → Surjective q.hom.hom.left →
  IsMultiplicativeType (kernel q) →
    ∃ s : G ⟶ G', s ≫ q = 𝟙 G.
```

In words: let `G` be a simply connected semisimple group over `k`, and let
`e → D → G' → G → e` be an extension of `G` by a group `D` of multiplicative
type, with `G'` an affine algebraic group. Then the extension splits: `q` has a
section that is a homomorphism of group schemes.

Every ingredient is an existing declaration, used without change:

- `IsSimplyConnected G` (from [`SimplyConnected.Basic`](Basic.md)) says that
  `G` is semisimple (`IsSemisimple`, from
  [`Reductive.Semisimple`](../Reductive/Semisimple.md)) and that every central
  isogeny `f : H ⟶ G` from a semisimple group `H` over `k` is an isomorphism.
  `IsSemisimple G` says that `G` is connected reductive and that its
  scheme-theoretic centre is finite. Connected reductive
  (`IsConnectedReductive`) means: smooth, affine, connected, and the unipotent
  radical of the base change to an algebraic closure is trivial.
- `Flat q.hom.hom.left` and `Surjective q.hom.hom.left` say that the
  morphism of schemes underlying `q` is flat and surjective.
- `kernel q` (from [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) is
  the actual group-scheme kernel of `q`: the pullback of `q` along the unit
  section of `G`. Its points with values in any `T` over `Spec k` are the
  elements of the kernel of `G'(T) → G(T)` (`kernelPointsEquiv`).
- `IsMultiplicativeType` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that the
  base change to some field extension `K` of `k` is isomorphic to the
  diagonalizable group of a finitely generated abelian group. It imposes no
  smoothness or connectedness, so finite groups such as `μ_p` in
  characteristic `p` are allowed.
- The conclusion asks for a morphism `s : G ⟶ G'` of group objects, that is, a
  homomorphism of group schemes, with `s ≫ q = 𝟙 G`.

Nothing is assumed about `G'` beyond being affine and locally of finite type
(hence of finite type, since an affine morphism is quasi-compact). In
particular `G'` need not be smooth or connected, and `D` need not be smooth.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Proposition 18.28, printed p. 393 (PDF p. 409), in the case
named by Remark 18.29:

- Proposition 18.28: "An extension of algebraic groups e → D → G′ → G → e
  splits if (a) D is of multiplicative type and (b) G is smooth, connected,
  and perfect, and G_{k^a} is simply connected."
- Remark 18.29, printed p. 394 (PDF p. 410): "The proposition applies to
  extensions of simply connected semisimple algebraic groups by groups of
  multiplicative type (21.50)."

The surrounding conventions are:

- An algebraic group is "a group object in the category of algebraic schemes
  over k", and "an algebraic k-scheme is a scheme of finite type over k"
  (printed p. 6, PDF p. 22). Chapter 18 opens, printed p. 387 (PDF p. 403),
  with "Recall that all algebraic groups are affine over a base field k." The
  Lean statement therefore assumes that `G'` is affine and locally of finite
  type. For `G`, both properties are part of `IsSemisimple`.
- Definition 1.61, printed p. 24 (PDF p. 40): a sequence e → N → G → Q → e
  (maps `i` and `q`) "is exact if i is an isomorphism of N onto the kernel of
  q" and "in addition q is faithfully flat. When (4) is exact, we say that G is
  an extension of Q by N." In the Lean statement the extension is given by `q`
  alone, and `D` is the kernel `kernel q`. Any `D` as in Milne is isomorphic to
  this kernel, so hypothesis (a) says exactly that `kernel q` is of
  multiplicative type.
- Faithfully flat: A.68, printed p. 582 (PDF p. 598): "A flat map φ is said to
  be faithfully flat if it is flat and |φ| is surjective." This is
  `Flat q.hom.hom.left ∧ Surjective q.hom.hom.left`. Milne writes |X| for
  "the underlying topological space of closed points" (printed p. 3, PDF
  p. 19). For a morphism of schemes of finite type over `k`, surjectivity on
  closed points is equivalent to surjectivity on all points: closed points map
  to closed points, and the complement of the image is constructible, so it
  is empty if it contains no closed point.
- Multiplicative type: Definition 12.17, printed p. 236 (PDF p. 252): "An
  algebraic group over k is of multiplicative type if it becomes diagonalizable
  over some field containing k." `Torus/MultiplicativeType.md` records that
  `IsMultiplicativeType` is this definition.
- Split: an extension splits when its quotient map has a section that is a
  homomorphism. Theorem 16.27(a), printed p. 333 (PDF p. 349), speaks of
  "sections of q (as a homomorphism of algebraic groups)", and Proposition 18.6
  (printed p. 388, PDF p. 404), used in the proof of 18.28, concludes that "φ
  admits a section".

The Lean statement is the case of Proposition 18.28 in which `G` is a simply
connected semisimple group. The hypotheses (b) of 18.28 then hold, by the
following identifications taken from Milne and the Library:

1. **Semisimple groups.** Milne, printed p. 400 (PDF p. 416): "Recall (6.46)
   that an algebraic group G over a field k is said to be reductive if it is
   smooth and connected and the unipotent radical of G_{k^a} is trivial."
   Proposition 19.10 on the same page says that for a reductive group, "(a) G
   is semisimple" and "(c) Z(G) is finite" are equivalent. So `IsSemisimple G`
   is Milne's semisimple group. In particular `G` is smooth and connected.
2. **Perfect.** Corollary 21.50, printed p. 440 (PDF p. 456): "Every semisimple
   algebraic group is perfect." Definition 12.45, printed p. 245 (PDF p. 261):
   "An algebraic group G is perfect if it equals its derived group."
3. **Simply connected.** Definition 18.5, printed p. 388 (PDF p. 404): "A
   connected group variety G is simply connected if every multiplicative
   isogeny G′ → G of connected group varieties is an isomorphism." Proposition
   19.15, printed p. 400 (PDF p. 416): "A semisimple group G is simply
   connected if and only if every central isogeny G′ → G from a semisimple
   group G′ to G is an isomorphism." Its proof, printed p. 401 (PDF p. 417):
   "When G is semisimple, to say that an isogeny G′ → G is central with G′
   semisimple is the same as saying that it is multiplicative with G′ a
   connected group variety." So for semisimple groups, Milne's Definition 18.5
   is the Library's `IsSimplyConnected`.
4. **Simply connected over `k^a`.** The Library proves
   `isSimplyConnectedFieldExtension`: `IsSimplyConnected G` implies
   `IsSimplyConnected` of the base change of `G` along any field extension,
   in particular to an algebraic closure `k^a`. By item 3 over `k^a`, this is
   the condition "G_{k^a} is simply connected" of 18.28(b). Conversely, the
   Library proves `simplyConnectedAlgebraicExtensionReflection`, so for a
   semisimple `G` the hypothesis `IsSimplyConnected G` is equivalent to the
   simple connectedness of `G_{k^a}`. The Lean statement assumes no more than
   18.28(b) for semisimple groups.

So every `G` satisfying `IsSimplyConnected G` satisfies 18.28(b), and every `q`
as in the Lean statement is an extension in Milne's sense satisfying 18.28(a).
Proposition 18.28 then gives a section.

The provenance is derived for these reasons:

- Milne states 18.28 for smooth, connected, perfect `G` with `G_{k^a}` simply
  connected. The Lean statement treats the case of simply connected semisimple
  `G`, which Remark 18.29 singles out. The restriction is forced by the
  Library's `IsSimplyConnected`, which includes `IsSemisimple`. Milne's
  Definition 18.5 also covers connected group varieties that are not
  semisimple; that case is not stated here.
- The hypotheses "smooth, connected, perfect" and "G_{k^a} simply connected"
  are derived from `IsSimplyConnected G` by items 1 to 4.
- The extension is given by the quotient map `q` and its actual kernel, rather
  than by a pair of maps `i`, `q`.
- `k`, `G` and `G'` lie in an arbitrary universe `u`. This is a formalization
  convention.

Errata. The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 1, a note that Notation 3.2 should be placed earlier and corrections
only on pp. 18, 20, 21 and 26; for Chapter 12, only
12.41 (p. 244) and 12.57 (p. 249); for Chapter 16, only pp. 324, 330 and 349;
for Chapter 18, only the last sentence of 18.4 and Exercise 18-1 (pp. 388
and 396, "G should be reductive") and the target of α in 18.8 (p. 389); for
Chapter 19, only Definition 19.7 (p. 399); for Chapter 21, on p. 440 only that
"The proof of Theorem 21.51 has been rewritten", and further entries on
pp. 445 and later; for Appendix A, only pp. 570 and 582 (on p. 582: "In A.70,
delete the word 'faithfully'"). None concerns the conventions of pp. 3 and 6,
1.61, 12.17, 12.24, 12.38,
12.45, 12.46, 16.27, 18.5, 18.6, 18.18, 18.24, 18.28, 18.29, 19.10, 19.15,
21.50 or A.68.

## For a proof (not part of this module)

The Library proves the statement as `simplyConnectedMultiplicativeExtensionSplit`
in `MultiplicativeExtensionSplitProof`.

Milne's proof of 18.28, printed p. 394 (PDF p. 410), has two cases.

- **`D` a torus.** Proposition 18.18 (printed p. 391, PDF p. 407) is applied to
  `G′_{k^a} → G_{k^a}`. It gives the exact sequence
  `X*(G) → X*(G′) → X*(D) → Pic(G_{k^a})`. Here `Pic(G_{k^a}) = 0` by
  Corollary 18.24 (printed p. 393), and `X*(G) = 0` because `G` is perfect.
  So restriction `X*(G′) → X*(D)` is an isomorphism. "As D is a central torus
  in G′ and G′/D is perfect, the quotient T = G′/DG′ is a torus (12.46)."
  The maps on character groups `X*(T) → X*(G′) → X*(D)` are isomorphisms, so
  `D → T` is an isomorphism. Its inverse composed with `G′ → T` is a
  homomorphism `G′ → D` restricting to the identity on `D`. Its kernel `DG′`
  meets `D` trivially and maps onto `DG = G` (as `G` is perfect), so it maps
  isomorphically onto `G`; the inverse of this isomorphism is the section.
- **`D` finite.** Milne cites Proposition 18.6 (printed p. 388, PDF p. 404):
  for a simply connected connected group variety `G` and "a surjective
  homomorphism with finite kernel of multiplicative type", "φ admits a section"
  if "(b) G is perfect". Proposition 18.6 assumes that `G` itself is simply
  connected. In the Lean statement this is the hypothesis `IsSimplyConnected G`
  (item 3).
- **General case.** By Corollary 12.24 (printed p. 240, PDF p. 256) there is
  an exact sequence `e → D′ → D → D″ → e` with `D′` a torus and `D″` finite.
  Milne then writes "This gives an exact sequence
  Ext¹(G, D″) → Ext¹(G, D) → Ext¹(G, D′)". **Source defect:** the arrows are
  printed in the wrong order. `Ext¹(G, −)` is covariant, so the sequence is
  `Ext¹(G, D′) → Ext¹(G, D) → Ext¹(G, D″)`. With the correct order, the
  middle group vanishes when the outer two do, which is the reduction Milne
  uses. Concretely, without `Ext¹` groups: first replace `G′` by its identity
  component, as Milne does in the proof of 18.6(b) ("We may suppose that G′ is
  connected"). It still maps onto the connected group `G`, because its image
  has finite index in `G`, and its kernel is a
  subgroup of `D`, hence of multiplicative type ("Subgroups and quotient
  groups (but not necessarily extensions) of groups of multiplicative type
  are of multiplicative type", printed p. 236). A section for the identity
  component is a section of `q`. Now `D` is central in `G′` by rigidity
  (Corollary 12.38, printed p. 244, PDF p. 260: "Every normal multiplicative
  subgroup N of a connected algebraic group G is contained in the centre of
  G"), so `D′` is normal in `G′`. The extension `e → D″ → G′/D′ → G → e`
  splits by the finite case, with a section `s″`. The fibre product of
  `G′ → G′/D′` and `s″` is an extension of `G` by the torus `D′`, which splits
  by the torus case. Composing that section with the projection to `G′` gives
  a section of `q`.
