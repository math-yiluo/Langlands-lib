# Descent of line bundles along direct limits and to finitely presented quotients

Author: Worker 1407.

Module `Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleQuotientDescent` proves
that a line bundle over a base change to `Spec (D ⧸ I)` already comes from one over
`Spec (D ⧸ J)` for some finitely generated ideal `J ≤ I`. It is a helper module for the proof of
`Langlands.AbelianScheme.RelativeDualSchemeFinitePresentationStatement`. All results are internal
and derived. The only external input is the ported FLT theorem
`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit`,
which is already in the Library. It descends invertible sheaves along an arbitrary directed system
of rings with a direct limit, over a quasi-compact, quasi-separated scheme. This is the standard
limit argument for modules of finite presentation; compare EGA IV §8.5.

## `exists_lineBundle_descent_of_isDirectLimit`

Data:
- a ring `A₀`;
- a nonempty directed preorder `ι` with a directed system `G : ι → Type u` of `A₀`-algebras, with
  transition maps `φ i j h` compatible with the structure maps (`hφ`);
- an `A₀`-algebra `A` and maps `g i : G i →+* A` compatible with the structure maps (`hg`), such
  that `A` is the direct limit (`hA : IsDirectLimit ...`);
- a quasi-compact, quasi-separated `f₀ : X₀ ⟶ Spec A₀`;
- a pullback square `hpb : IsPullback a f f₀ (Spec A → Spec A₀)`, so `X = X₀ ×_{A₀} Spec A`;
- a locally free rank-one module `M` on `X`.

Conclusion: there are an index `j` and a locally free rank-one module `M₀` on the chosen pullback
`pullback f₀ (Spec (G j) → Spec A₀)` with the following property. For every morphism
`c : X ⟶ pullback f₀ (Spec (G j) → Spec A₀)` whose first projection is `a` and whose second
projection is `f ≫ Spec (g j)`, `c^* M₀ ≅ M`.

Proof. Fix an index `i` and put `Y = X₀ ×_{A₀} Spec (G i)`, with second projection to
`Spec (G i)`, which is quasi-compact and quasi-separated by base change. The base change `P` of
`Y` along `Spec A → Spec (G i)` comes with maps `e : P ⟶ X` and `e' : X ⟶ P`, both built from the
universal property of the pullback squares. Their composite `e' ≫ e` is the identity of `X`
(`he`). The FLT theorem, applied to `e^* M` on `P`, gives `j ≥ i` and an invertible `Lj` on
`Y ×_{Spec (G i)} Spec (G j)`. Its pullback along every morphism from `P` that is compatible with
both projections is isomorphic to `e^* M`. Let `u` be the canonical map from
`X₀ ×_{A₀} Spec (G j)` to `Y ×_{Spec (G i)} Spec (G j)`, and put `M₀ = u^* Lj`. It is locally
free of rank one by `isLocallyFreeRankOne_of_isInvertible`. Let `c` be as in the conclusion.
Then `e ≫ c ≫ u` is compatible with both projections, checked componentwise as `h₁` and `h₂`.
Hence `(e ≫ c ≫ u)^* Lj ≅ e^* M`. The published `nonempty_iso_pullback_of_section` uses the
section `e'` of `e` to cancel `e`, giving `(c ≫ u)^* Lj ≅ M`. Composing with the pullback
composition isomorphism gives `c^* M₀ ≅ M`.

## The system of finitely generated quotients

For an ideal `I` of a ring `D`:
- `FGQuotIndex I` is the type of finitely generated ideals `J ≤ I`, ordered by inclusion. It is
  nonempty (it contains `⊥`) and directed (it contains `J ⊔ J'`).
- `FGQuotStage J = D ⧸ J`.
- `quotTransition` is `Ideal.Quotient.factor`.
- `quotToLimit J : D ⧸ J →+* D ⧸ I` is `Ideal.Quotient.factor`.

`quotDirectedSystem` records that these maps form a directed system. `quotIsDirectLimit` states
that `D ⧸ I` is its direct limit:
- Surjectivity: every class comes from `D ⧸ ⊥`.
- Injectivity: if `x, y ∈ D` have the same image in `D ⧸ I`, then they already agree in
  `D ⧸ (S ⊔ T ⊔ (x − y))`, which is again a finitely generated ideal inside `I`.
- Compatibility: holds by definition.

## `exists_lineBundle_quotient_descent`

Let `D` be an `A₀`-algebra and `I` an ideal of `D`. Let `f₀ : X₀ ⟶ Spec A₀` be quasi-compact and
quasi-separated, with a pullback square `X = X₀ ×_{A₀} Spec (D ⧸ I)`, and let `M` be locally free
of rank one on `X`. Then there are a finitely generated ideal `J` with `hJ : J ≤ I` and a locally
free rank-one `M₀` on `pullback f₀ (Spec (D ⧸ J) → Spec A₀)` with the following property. For
every `c : X ⟶ pullback f₀ (Spec (D ⧸ J) → Spec A₀)` whose first projection is `a` and whose
second projection is `f ≫ Spec (Ideal.Quotient.factor hJ)`, `c^* M₀ ≅ M`.

Proof. This is `exists_lineBundle_descent_of_isDirectLimit` applied to the quotient system above;
both compatibility conditions hold by `rfl`.
