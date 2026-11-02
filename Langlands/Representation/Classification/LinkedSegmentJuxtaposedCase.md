# The juxtaposed case of Proposition 4.6, step (2)

Author: Worker 1033.

The published statement `LinkedSegmentSocleReverseProductQuotientHom` (module
`LinkedSegmentSocleReverseProductStepsStatement`) extends step (2) of Zelevinsky
1980, Proposition 4.6 to juxtaposed segments. There it follows from statement 1,
`JuxtaposedSegmentSocleReverseProductStructure`, which is step (1) of the same
proposition (printed pp. 185–186). Step (1) gives a filtration
`0 ⊂ ω₀ ⊂ π` with `π/ω₀ ≅ ⟨Δ ∪ Δ'⟩`, so the quotient map `π → π/ω₀` is
nonzero. This module carries this out, assuming statement 1 as a hypothesis.
Everything lives in the namespace `Langlands.Classification.QuotientHom`.

## Declarations

- `nonempty_induced_iso_of_segments_eq d e hs hd he`: two segment product data
  with the same list of segments, both with segment-socle blocks, have
  isomorphic products `d.induced ≅ e.induced`. The proof destructures both
  data and substitutes the equal lengths and segment families. Each pair of
  blocks is then isomorphic, since each block is isomorphic to the published
  segment socle by `IsSegmentSocle.nonempty_iso_segmentSocle`. The product
  isomorphism is the image of `Pi.isoMk` under
  `normalizedProductInductionFunctor`.
- `replacement_eq_of_inter_empty hfree h₀ h`: suppose `h` is a
  replacement `Δ, Γ ↦ (U, none)` and `h₀` is any replacement
  `Δ, Γ ↦ (U₀, I₀)`. Then integral twist freeness `hfree` gives `U₀ = U` and
  `I₀ = none`. The two unions have the same support, so
  `Segment.eq_of_support_eq` makes them equal. If `I₀ = some J`, the base of `J`
  lies in `J.support` by `Segment.base_mem_support`. That support is
  `Δ.support ∩ Γ.support`, which `h` says is empty, a contradiction.
- `IntertwiningMap.ne_zero_of_surjective`: a surjective intertwiner onto an
  irreducible representation is nonzero, because its range is not `⊥`.
- `IntertwiningMap.comp_ne_zero`: composing a nonzero intertwiner with an
  injective one gives a nonzero intertwiner.
- `toTopStep s`: the identity of `A` as an intertwiner onto the top step of an
  `ObjectRepFiltration A m`. That step is all of `A` by
  `s.subrepresentation_last`. `toTopStep_surjective` says it is surjective.
- `exists_ne_zero_of_juxtaposed h1 d h₂ hd hp U e hs he he'`: this takes
  - statement 1 as the hypothesis `h1`;
  - a two-segment datum `d` with segment-socle blocks, where `Δ' = d.segments 1`
    precedes `Δ = d.segments 0`;
  - a union–intersection replacement `Δ, Δ' ↦ (U, none)`;
  - a socle datum `e` whose segment list is `[U]`.

  It returns a nonzero intertwiner `d.induced → e.induced`.

  Proof. The empty intersection in `hs` together with the linkage in `hp` makes
  the segments juxtaposed. Statement 1 then supplies `U₀`, `I₀`, `e₀`, a
  filtration `s` with simple factors and an equivalence `φ` from graded
  piece `1` to `e₀.induced`. `replacement_eq_of_inter_empty`, applied with the
  proved `cuspidalIntegralTwistFreeness` (module
  `CuspidalIntegralTwistFreenessProof`), gives `U₀ = U` and `I₀ = none`. So `e₀` and
  `e` have the same segment list, and `nonempty_induced_iso_of_segments_eq`
  gives `ι : e₀.induced ≅ e.induced`. The map `g = gradedProjection 1 ∘
  toTopStep s` is surjective onto the simple graded piece `1`, hence nonzero.
  Composing with the injective `ι ∘ φ` keeps it nonzero.
