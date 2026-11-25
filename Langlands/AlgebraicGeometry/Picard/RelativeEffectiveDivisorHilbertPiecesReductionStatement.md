# Reduction of the representability of relative effective divisors to the Hilbert scheme and the relative effective Cartier locus

The statement is one of the prerequisites of the Library's proof of Kleiman's
Theorem 4.8 (`NoetherianIntegralFibrePicardSheafAFSchemeProof`). The
proposition reduces the published
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement`
("(a)", proved as `relativeEffectiveDivisorHilbertPieces` in
`RelativeEffectiveDivisorHilbertPiecesProof`)
to two statements:

- `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement` ("HGP"),
  the Hilbert scheme with its universal closed subscheme and H-projective
  Hilbert-polynomial pieces;
- `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusStatement`
  ("CLO"), the openness of the relative effective Cartier locus.

No proof is asserted here. The module only states the implication.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReductionStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`):

```lean
HilbertSchemeUniversalFamilyStatement.{u} →
  RelativeEffectiveCartierLocusStatement.{u} →
    RelativeEffectiveDivisorHilbertPiecesStatement.{u}
```

All three are Library propositions, imported from their modules and used at
the same universe `u`. In outline:

1. **HGP.** Let `A` be a commutative ring and `f : X ⟶ Spec A` flat and
   locally of finite presentation, with an invertible module `𝓛X` whose global
   sections give a closed immersion into a finite projective space over `A`
   (`ClosedImmersionBySections 𝓛X f`). Then there are a scheme
   `πH : H ⟶ Spec A`, separated and locally of finite presentation, and an
   ideal sheaf `W` on `X ×_A H`. For every scheme `T` and `s : T ⟶ Spec A`,
   pulling `W` back along `X ×_A T ⟶ X ×_A H` gives a bijection from morphisms
   `T ⟶ H` over `Spec A` onto ideal sheaves on `X ×_A T` whose closed
   subscheme is flat and locally of finite presentation over `T`. Moreover `H`
   is a disjoint union of open subschemes `U θ` (`θ ∈ ℚ[t]`), each
   H-projective over `Spec A` (`IsHProjective`). An affine point
   `g : Spec B ⟶ H` lands in `U θ` exactly when the geometric fibres of the
   classified subscheme have Hilbert function `θ(n)` for large `n` (dimension
   of the sections of `𝓛X^{⊗n}`).
2. **CLO.** Let `B` be locally noetherian, `q : Y ⟶ B` proper and flat, and
   `Z` an ideal sheaf on `Y` whose closed subscheme is flat over `B`. Then
   there is an open `U ⊆ B` such that, for every pullback square
   `IsPullback gY qT q g` with arbitrary `T`, `Z.comap gY` is a relative
   effective Cartier ideal for `qT` if and only if `g` lands in `U`.
3. **(a), the conclusion.** Let `A` be a noetherian ring and
   `f : X ⟶ Spec A` flat with `𝓛X` as in HGP. Then there are a separated
   scheme `d : D ⟶ Spec A`, locally of finite presentation, and a relative
   effective divisor `W` on `X ×_A D` over `D`. For every scheme `T` and
   `s : T ⟶ Spec A`, pulling `W` back gives a bijection from morphisms
   `T ⟶ D` over `Spec A` onto relative effective Cartier ideals on `X ×_A T`
   over `T`. And `D` is a disjoint union of H-quasi-projective open pieces
   `U θ` with the same Hilbert-function characterization as in HGP.

The Markdown files of the three statements explain every hypothesis and
conclusion in detail.

## Source and provenance

The provenance is "derived". The implication follows the proof of Theorem 3.7
of S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`, statement p.23, proof
p.24). There `Div_{X/S}` is represented by an open subscheme `U` of
`H = Hilb_{X/S}`: the complement of the image of the non-Cartier locus of the
universal subscheme `W`. The first paragraph of the proof constructs `U` and
shows that `W` is a relative effective divisor over `U`. The second paragraph
uses the universal property of `(H, W)` to classify a relative effective
divisor `D ⊂ X_T` by a unique `g : T ⟶ H`, and then the fibre argument to show
that `g` factors through `U`. In the proof of Theorem 4.8 (p.30) Kleiman
notes that an open subscheme `Z` of `Div_{X/S}` lying in a piece
`Hilb^θ_{X/S}`, which is projective over `S`, is quasi-projective.

Here the existence of `(H, W)` with its pieces is the hypothesis HGP. The
construction of `U` and both directions of the comparison "`Z.comap gY` is
relative effective Cartier iff `g` lands in `U`" are the hypothesis CLO. What
remains is the assembly: the universal property of `(H, W)` restricted to
`U`, and the pieces `U ∩ U θ`. Kleiman does not state this implication
separately. Kleiman's schemes are locally noetherian (p.15). The three Lean
statements allow arbitrary test schemes `T`, and their own Markdown files
derive this extension.

## Intended proof

The Library proves the implication as
`RelativeEffectiveDivisorHilbertPiecesReduction.relativeEffectiveDivisorHilbertPiecesReduction`
(module `RelativeEffectiveDivisorHilbertPiecesReductionProof`); its Markdown
describes the implemented proof.

1. `f` is proper, because `ClosedImmersionBySections 𝓛X f` factors `f`
   through a closed immersion into projective space, which is proper over
   `Spec A`. Hence `f` is locally of finite type. Since `A` is noetherian, `f`
   is locally of finite presentation, so HGP applies and gives `H`, `πH`, `W`
   and the pieces `U θ`.
2. `H` is locally of finite presentation over the noetherian `Spec A`, so it
   is locally noetherian. The projection `q := pullback.snd f πH` is proper
   and flat (base change of `f`), and the closed subscheme of `W` is flat over
   `H`. For flatness, apply HGP's classification to `g = 𝟙 H`. CLO gives the
   open `U ⊆ H`.
3. Put `D := U`, `d := U.ι ≫ πH`, and let `W_D` be the pullback of `W` along
   `X ×_A U ⟶ X ×_A H`. CLO applied to the inclusion square shows that `W_D`
   is a relative effective divisor over `U`. `d` is separated and locally of
   finite presentation, as a composite of an open immersion with `πH`.
4. **Functor of points.** Pullbacks compose (`IdealSheafData.comap_comp`), so
   the pullback of `W_D` along `T ⟶ U` is the pullback of `W` along the
   composite `T ⟶ H`. CLO then says it is relative effective Cartier. A
   relative effective Cartier ideal `I` on `X ×_A T` is invertible, so its
   ideal is finitely generated on affines and its closed subscheme is locally
   of finite presentation over `T`. HGP classifies `I` by a unique
   `g : T ⟶ H`, and CLO shows that `g` lands in `U`. So `g` lifts uniquely
   through the open immersion `U.ι`.
5. **Pieces.** Take `U.ι⁻¹(U θ)`. These are disjoint and cover `U`. Each one
   is an open subscheme of the noetherian scheme `U θ` (H-projective over
   noetherian `A`, so proper and of finite type), hence quasi-compact, and
   its inclusion into `U θ` composed with the closed immersion of `U θ` into
   projective space is an immersion. So each piece is H-quasi-projective. The
   Hilbert-function characterization is HGP's applied to the composite
   `Spec B ⟶ U ⟶ H`.
