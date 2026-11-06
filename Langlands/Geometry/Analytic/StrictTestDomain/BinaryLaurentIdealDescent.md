# Closed-ideal effectiveness for the actual strict binary Laurent cover

This is an internal prerequisite for finite-cover closed-ideal descent. It
restates the two-member result of `GeneralizedAffinoid.BinaryLaurentIdealDescent`
for the strict binary Laurent cover of `StrictTestDomain.BinaryLaurentCover`,
whose pieces are rational data over a presented strict affinoid algebra. The
motivating source is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Kiehl's Theorem and Remark 1.2.1(ii), printed p.15 / PDF p.12,
registered as `berkovich-1993-etale-cohomology`. The transport argument below is
internal and transcribes no proof from the source.

## Transport of split squares

`BoundedAlgHom.SplitSquare.congr` transports a split square along bounded
algebra equivalences of its four corners. Let `S` be a split square for
`p₁ : A → A₁`, `p₂ : A → A₂`, `r₁ : A₁ → A₁₂`, `r₂ : A₂ → A₁₂`. Let
`q₁ : B → B₁`, `q₂ : B → B₂`, `s₁ : B₁ → B₁₂`, `s₂ : B₂ → B₁₂` be bounded algebra
maps, and let `e : B ≃ A`, `e₁ : B₁ ≃ A₁`, `e₂ : B₂ ≃ A₂`, `e₁₂ : B₁₂ ≃ A₁₂` be
bounded algebra equivalences with

- `e₁ (q₁ b) = p₁ (e b)` and `e₂ (q₂ b) = p₂ (e b)`;
- `e₁₂ (s₁ b) = r₁ (e₁ b)` and `e₁₂ (s₂ b) = r₂ (e₂ b)`.

Then `q₁, q₂, s₁, s₂` form a split square. The four fields are obtained as
follows.

- Commutation: apply the injective map `e₁₂` and use the four identities and
  the commutation of `S`.
- Gluing: if `s₁ b₁ = s₂ b₂`, then `r₁ (e₁ b₁) = r₂ (e₂ b₂)`. Gluing in `S` gives
  `a ∈ A`, and `e⁻¹ a` glues `b₁` and `b₂` by injectivity of `e₁` and `e₂`.
- Density: `s₂ = e₁₂⁻¹ ∘ r₂ ∘ e₂`. A surjective map has dense range, and a
  composite of dense-range maps with continuous outer factors has dense range.
- Splitting: split `e₁₂ h = r₁ a₁ + r₂ a₂` in `S`, and take `e₁⁻¹ a₁` and
  `e₂⁻¹ a₂`. Let `C₁, C₂` be the chosen bounds of `e₁⁻¹, e₂⁻¹`, `C₁₂` the
  chosen bound of `e₁₂`, and `β` the constant of `S`. Both new pieces have norm
  at most `max C₁ C₂ · β · C₁₂ · ‖h‖`; this product is the new constant.

## The strict binary Laurent square

Let `K` be a complete ultrametric normed field, `P` a presented strict affinoid
`K`-algebra and `f ∈ P`. In `StrictTestDomain.RationalData`, `laurentUpper f`
(`|f| ≤ 1`) and `laurentLower f` (`|f| ≥ 1`) are the Library's rational data.
The square consists of their base maps from `P` and the restrictions from each
piece to the actual intersection `(laurentUpper f).inter (laurentLower f)`:
`interLeft` from the upper piece and `interRight` from the lower piece.

`nonempty_laurentSplitSquare hK f`, with `hK : ∃ c : K, 1 < ‖c‖`, states that
this square has a split-square structure. The published
`binaryLaurentDiagramComparison` gives bounded equivalences from the strict
upper, lower and intersection algebras to the relative `Upper`, `Lower` and
`Overlap` over `ofStrict K P`, compatible with the base maps and both overlap
arrows. Together with the inverse of `strictEquiv K P`, these transport
`BinaryLaurent.splitSquareOfStrict` along `congr`. The base element is
`(strictEquiv K P)⁻¹ f`.

`laurentSplitSquare hK f` is a split-square structure chosen from this
nonemptiness statement with `Classical.choice`. Its splitting constant is not
specified.

## Effectiveness

`laurent_closedIdealMap_inf_comap_eq hK f I₁ I₂ hI`: let `I₁` be an ideal of the
upper algebra and `I₂` an ideal of the lower algebra. Suppose their closed
extensions to the intersection algebra along `interLeft` and `interRight`
coincide. Let `J` be the ideal of `P` of elements whose image under the upper
base map lies in `I₁` and whose image under the lower base map lies in `I₂`.
Then the closed extension of `J` to the upper algebra is `I₁`, and its closed
extension to the lower algebra is `I₂`.

The proof applies `SplitSquare.closedIdealMap_inf_comap_eq` to
`laurentSplitSquare hK f`. All three corner algebras are presented strict
affinoid algebras. They are complete and Noetherian by the Library instances,
and all their ideals are closed by `PresentedStrictAffinoidAlgebra.isClosed_ideal`,
which uses `hK`.

## Scope

The results concern only the two-member strict Laurent cover given by one `f`,
over a nontrivially normed field. The module does not prove the finite-cover
`IdealEffectivenessStatement`. It assumes no reducedness, nonzero algebra or
nonempty spectrum, and `f` is arbitrary.
