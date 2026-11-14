# Canonical coherent Galois comparisons for the algebraic fundamental group

Author: Worker 149 (Task 6302).

## Statement proved

`Langlands.GroupScheme.AlgebraicFundamentalGroup.algebraicFundamentalGroupComparison` proves
`Langlands.GroupScheme.AlgebraicFundamentalGroup.AlgebraicFundamentalGroupComparisonStatement`
(module `Langlands.GroupScheme.AlgebraicFundamentalGroupStatement`) at universe `u`.

Let `k` be a field, `E` a separable closure of `k` (`[IsSepClosure k E]`) and `G` a
connected reductive group over `Spec k`. A `Choice k G` is a maximal torus `T` of `G`
together with a simply connected cover `C → D` of the derived subgroup `D` of `G`. The
quotient `a.atChoice E = X_*(T_E) / image(X_*(T_sc,E))` is the presentation of the
algebraic fundamental group for the choice `a`. The theorem gives the following for all
choices `a`, `b` and `c`:

- there is a unique canonical comparison `a.atChoice E → b.atChoice E`, i.e. a map induced
  on representatives by an actual geometric conjugation `(g, e)` of the maximal tori;
- the epsilon-chosen `a.comparison E b` is that canonical comparison;
- it is bijective and commutes with the Galois actions of `E ≃ₐ[k] E`;
- every conjugator `(g, e)` computes it: `[ν] ↦ [ν ≫ e.hom]`;
- `a.comparison E a = id`, and `b.comparison E c ∘ a.comparison E b = a.comparison E c`.

Both the torus and the representative of the simply connected derived cover may vary
between `a`, `b` and `c`.

## Source

Kaletha–Prasad (2023), Construction 11.3.1 and Definition 11.3.2, printed p. 427
(PDF p. 458). The source defines `π_1(G) = X_*(T)/X_*(T_sc)` over a separable closure.
It observes that two choices of maximal torus are conjugate, and that the resulting
identification does not depend on the conjugating element because the Weyl group acts
trivially on the quotient. The Lean proof follows this route.

## Proof

The proof applies the assembly theorem
`Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice.comparison_of_conjugators`
(module `Langlands.GroupScheme.AlgebraicFundamentalGroupConjugators`) to fixed `k`, `E`
and `G`. That theorem derives every clause of the statement from four inputs about
conjugators. A conjugator `(g, e)` from `a` to `b` consists of `g ∈ G_E(E)` and
`e : (T_a)_E ≅ (T_b)_E` with `(i_a)_E ≫ int(g) = e ≫ (i_b)_E`. The four inputs are proved
in four helper modules, each with its own Markdown:

1. **Existence** (`Choice.exists_isConjugationComparison`, module
   `Langlands.GroupScheme.AlgebraicFundamentalGroupConjugatorExistence`). Over the
   separable closure both base-changed maximal tori are maximal split tori, so
   `smoothMaximalSplitTorusConjugacy` gives a conjugator between any two choices.
2. **Coroot preservation** (`Choice.IsConjugationComparison.corootImage_le`, module
   `Langlands.GroupScheme.AlgebraicFundamentalGroupCorootTransport`). Conjugation by `g`
   lifts to a map between the base-changed simply connected covers
   (`exists_comp_eq_comp_iso`). Hence `ν ↦ ν ≫ e.hom` maps the image of `X_*(T_a,sc)` into
   the image of `X_*(T_b,sc)`. The fibre-product description of the preimage torus turns
   lifts into elements of the coroot image.
3. **Weyl triviality** (`Choice.IsConjugationComparison.sub_mem_corootImage`, module
   `Langlands.GroupScheme.AlgebraicFundamentalGroupWeyl`). A conjugator from `b` to itself
   is a normalizing point of the split maximal torus `(T_b)_E`. By the published Weyl group
   theorem `weylGroup` it acts through an element of the Weyl group of a root datum `P` of
   `(T_b)_E`, and Weyl group elements move cocharacters by elements of the coroot span. The
   coroots of `P` lie in the coroot image. They come from the coroots of the simply
   connected cover through the derived subgroup, by
   `simplyConnectedDerivedCoverSplitTorus`,
   `IsRootDatumOf.map_derived_corootSpan_eq_coweight_zero` and
   `centralIsogenyRootDatumHom`.
4. **Galois transport** (`Choice.IsConjugationComparison.exists_galois`, module
   `Langlands.GroupScheme.AlgebraicFundamentalGroupConjugators`). Galois descent transport
   of a conjugator is again a conjugator, and the transported torus isomorphism intertwines
   the Galois actions on cocharacters.

In the assembly, inputs 2 and 3 make the conjugator formula hold for every conjugator,
using the epsilon law `comparison_spec`. The formula then gives uniqueness, the identity
law (conjugator `(1, id)`) and the composition law (composite conjugator). The inverse
comparison gives bijectivity, and input 4 gives Galois equivariance.

The final theorem body is

```lean
intro k E _ _ _ _ G hG
exact Choice.comparison_of_conjugators E
  (Choice.exists_isConjugationComparison E hG)
  (fun _ _ _ _ h => h.corootImage_le)
  (fun _ _ _ h => h.sub_mem_corootImage hG)
  (fun _ _ _ _ h σ => h.exists_galois σ)
```

The development check reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
