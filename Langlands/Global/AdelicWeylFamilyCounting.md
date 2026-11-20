# Composition and inversion in the Weyl sets `Ω(P, P')`

Module `Langlands.Global.AdelicWeylFamilyCounting` proves elementary facts
about the Weyl conjugations `IsWeylConjugation` of module
`Langlands.Global.AdelicIntertwiningOperator`. It also proves the counting
identity behind Arthur's weights `n_P`. Everything is proved; nothing is
assumed. All declarations are in the namespace
`Langlands.Global.AdelicGroupPoints`.

## Conventions

`IsWeylConjugation p l q l' w c` (for parabolics `p : P → G`, `q : Q → G` with
Levis `l : M → P`, `l' : M' → Q`, a point `w` of `G` over the base and
`c : M' → M`) says that `c` is an isomorphism and
`c ≫ l ≫ p = l' ≫ q ≫ (G.innerIso w).inv`, i.e. `l(c(m')) = w⁻¹ l'(m') w`.
The pair presents an element of `Ω(P, Q)`. For a projection `π' : Q → M'`,
`weylParameter l c π'` is the induced map `λ ↦ wλ` from `X^*(P) ⊗ ℂ` to
`X^*(Q) ⊗ ℂ`, given on characters by `χ ↦ χ ∘ l ∘ c ∘ π'`.
`weylParameterSet p l q l' π'` is the set of these maps over all Weyl
conjugations; it is the realization of `Ω(P, Q)` used in the Library (module
`Langlands.Global.AdelicInducedInnerProduct`).

## Results for single conjugations

- `innerIso_mul_inv`, `innerIso_one_inv`, `innerIso_inv_point_inv`: the inverses of
  the inner automorphisms satisfy
  `(G.innerIso (w * w₀)).inv = (G.innerIso w).inv ≫ (G.innerIso w₀).inv`,
  `(G.innerIso 1).inv = 𝟙 G` and `(G.innerIso w⁻¹).inv = (G.innerIso w).hom`.
  They follow from `innerIso_mul_hom`, `innerIso_one_hom` and
  `innerIso_inv_hom` (module `Langlands.GroupScheme.InnerAutomorphismHom`).
- `IsWeylConjugation.trans`: if `(w, c)` is a Weyl conjugation from `P` to
  `P''` and `(w₀, c₀)` one from `P'` to `P`, then `(w * w₀, c ≫ c₀)` is one
  from `P'` to `P''`. This is the composition `Ω(P, P'') × Ω(P', P) → Ω(P', P'')`.
- `IsWeylConjugation.symm`: if `(w, c)` is a Weyl conjugation from `P` to
  `P'`, there is an inverse `c'` of `c` such that `(w⁻¹, c')` is a Weyl
  conjugation from `P'` to `P`.
- `weylParameter_comp_of_retraction`: if `l ≫ π = 𝟙 M`, then
  `weylParameter l c π'' ∘ₗ weylParameter l' c₀ π = weylParameter l' (c ≫ c₀) π''`.
  The parameter maps compose like the conjugations. The proof restricts
  characters along `π'' ≫ c ≫ l ≫ π ≫ c₀ ≫ l'` and cancels `l ≫ π`.

## Results for families

Section `Families` fixes a family of parabolics `p i : P i → G` with Levis
`l i` and projections `π i` (`l i ≫ π i = 𝟙`). It also fixes finite types
`T i i'` with maps `(w i i' t, cw i i' t)` that are Weyl conjugations from
`P i` to `P i'` (`hW`). These are exactly the data and hypotheses `hW`, `hinj`,
`hsurj` of `Langlands.Global.SpectralTransformStatement`: `t ↦
weylParameter (l i) (cw i i' t) (π i')` is injective (`hinj`) with image
`weylParameterSet (p i) (l i) (p i') (l i') (π i')` (`hsurj`), so `T i i'`
enumerates `Ω(P i, P i')` without repetition.

- `card_le_card_of_weylConjugation`, `card_eq_card_of_weylConjugation`: if
  `T i' i` is nonempty, then `|T i i''| = |T i' i''|` for every `i''`.
  Composing with a fixed `t₀ : T i' i` maps `Ω(P i, P i'')` injectively into
  `Ω(P i', P i'')`, and composing with its inverse maps back. Injectivity
  uses `weylParameter_comp_of_retraction` to cancel the parameter map of `t₀`.
- `card_le_card_swap`, `card_swap`: `|T i i'| = |T i' i|`, by inversion.
- `nonempty_self`: `T i i` is nonempty, since `(1, 𝟙)` is a Weyl conjugation
  from `P i` to itself.
- `sum_card_div_card_eq_one`: with `n_P(i') = ∑ i'', |T i' i''|`,
  `∑ i', |T i' i| / n_P(i') = 1` for every `i` (in `ℂ`). The denominators of
  the nonzero terms all equal `n_P(i)` by the first result, and
  `∑ i', |T i' i| = ∑ i', |T i i'| = n_P(i)` by `card_swap`.

## Sources and provenance

The weights are Arthur's: J. Arthur, *An introduction to the trace formula*,
Clay Math. Proc. 4 (2005), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Theorem 7.2 (b),
printed p.35 (PDF page 47), with `n_P = ∑_{P' ∈ 𝒫} |W(𝔞_P, 𝔞_{P'})|`;
likewise J. Getz and H. Hahn, *An introduction to automorphic
representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, (10.23). The identity
`∑_{P'} n_{P'}⁻¹ |W(𝔞_{P'}, 𝔞_P)| = 1` within an association class is
standard and is quoted in the Markdown of
`Langlands.Global.SpectralTransformStatement`. The formulation and the proofs
here are internal. They use only the definitions of `IsWeylConjugation` and
`weylParameter`. Since the family `(P i)` is arbitrary and need not be one
association class, the counting is done with the sets `T i i'`; `T i' i` is
empty when `P i'` and `P i` are not associate, and such terms contribute
zero. The module is used by the bridge
`Langlands.Global.SymmetricFamilyGramBridgeStatement`.
