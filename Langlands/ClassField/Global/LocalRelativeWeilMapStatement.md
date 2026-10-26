# Existence and conjugacy of local Weil maps into relative Weil groups

Worker 35 authored this statement unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. All declarations lie in the namespace
`Langlands.ClassField.Global` and are proposition definitions. Nothing is
proved here.

The statements concern the published predicate
`RelativeWeilGroup.IsLocalRelativeWeilMap v w e ι` of the module
`Langlands.ClassField.Global.LocalRelativeWeilMap`. For a finite place `v` of
`F` and a place `w` of `E` above it, this predicate says that a continuous
homomorphism `ι : W_{F_v} → RelativeWeilGroup c F E` has three properties:

1. `e` is a geometrically normalized Weil reciprocity isomorphism for `E_w`.
2. The image of `ι g` in `Gal(E/F)` acts on `E` as the Galois image of `g`
   does, through `E → E_w → \bar{F_v}`.
3. On `W_{E_w}`, `ι` is the inverse of `e` followed by
   `E_wˣ → C_E ⊆ RelativeWeilGroup c F E`.

That module's Markdown explains the conventions, including the inverse in
condition 3.

## `LocalRelativeWeilMapConjugacyStatement`

For all number fields `F E : Type u` with `[Algebra F E] [IsGalois F E]`,
every class family `c`, all finite places `v`, `w` with
`w.asIdeal.LiesOver v.asIdeal`, and every reciprocity candidate `e` for `E_w`:
let `ι` and `ι'` both satisfy `IsLocalRelativeWeilMap v w e`. Then there is
`b : C_E` with

`ι' g = inclusion c F E b * ι g * (inclusion c F E b)⁻¹` for every `g`.

The statement has no hypothesis on `c`. When no such map exists, it is
vacuous. Both maps use the same candidate `e`. The library has not proved
uniqueness of geometric reciprocity
(`LocalClassField.WeilReciprocityExistenceUniqueness`), so the statement does
not compare different candidates.

**Expected proof.** This is the argument of Tate §1.5 and (1.6.1), at finite
level. It is described here and not formalized.

- By condition 2, `ι g` and `ι' g` have the same image in `Gal(E/F)`, written
  `τ_g`. The extension is exact, so `ι' g = inclusion(α g) * ι g` for a
  unique `α g ∈ C_E`. This uses the published `RelativeWeilGroup.exact`.
- The published `conjugation` formula gives
  `t * inclusion a * t⁻¹ = inclusion (τ_t a)`. Hence
  `α(gh) = α(g) · τ_g(α(h))`, so `α` is a crossed homomorphism.
- Let `H` be the image of `completionWeilMap v w`. By condition 3, `α` is
  trivial on `H`. By the published `extensionWeilMap_range`, `H` is the
  inverse image of the absolute Galois group of `E_w`. Condition 2 shows
  that `τ_g = 1` exactly when `g` fixes `j(E)`. Since `j(E) F_v = j(E_w)`,
  this happens exactly when `g ∈ H`. The Weil group is dense in the Galois
  group, so `g ↦ τ_g` induces an isomorphism from `W_{F_v} / H` onto the
  decomposition group `D_w`. Therefore `α` descends to a 1-cocycle of `D_w`
  with values in `C_E`.
- `D_w = Gal(E/E^{D_w})`. The published theorem `ideleClassH1Vanishing`
  gives `H^1(D_w, C_E) = 0`. So `α(g) = b · τ_g(b)⁻¹` for some `b`, which is
  the displayed conjugacy.

## `LocalRelativeWeilMapExistenceStatement`

Let `I` be a family of local invariant maps such that every `I p` satisfies
`RelativeClassFormation` and `ArithmeticNormalization`. Let the class family
`c` satisfy `Generates c`, `Restriction c`, `Inflation c` and
`LocalCompatibility I c`. These are exactly the hypotheses and the
conclusion of the published `GlobalFundamentalClassStatement`. Then for all
`F`, `E`, `v`, `w` as above and every candidate `e` with
`GeometricWeilReciprocityRelation (towerPadicField v w)
(towerPadicField v w).canonicalTopologicalData e`, there is a continuous
homomorphism `ι` with `IsLocalRelativeWeilMap v w e ι`.

Under these hypotheses, `c F E` is the arithmetic fundamental class. The
published `fundamentalClass_unique` shows that `Inflation` and
`LocalCompatibility I` already determine the family. `Generates` and
`Restriction` are included so that the hypothesis matches the conclusion of
`GlobalFundamentalClassStatement`.

**Expected proof.** Tate (1.6.1) gives a continuous `θ_v : W_{F_v} → W_F`. It
is compatible with an embedding `i : \bar F → \bar{F_v}` and, on `W_{E_v}`,
with the reciprocity maps and the coordinate map `η : E_vˣ → C_E`. Several
identifications turn `θ_v` into the required map; the source supplies none
of them in this form.

- **Embedding.** Choose `i` extending `j ∘ x_w : E → \bar{F_v}`. The
  completion of `E` induced by `i` is then `E_w`.
- **Local Weil group of `E_w`.** Tate's `W_{E_v}` is the subgroup of `W_{F_v}`
  fixing `j(E_w)`. By the published `extensionWeilMap_range`, it is the
  image of `completionWeilMap v w`.
- **Reciprocity.** Condition 1 is intrinsic to `E_w`, so `e` corresponds to
  the inverse of Tate's `r_{E_v}`.
- **Finite level.** Compose `θ_v` with the quotient `W_F → W_{E/F}`. Then
  apply the equivalence of Tate's `W_{E/F}` with `ClassExtension (c F E)`
  given by inversion on `C_E`, as explained in the definition's Markdown.

The proof requires the global Weil group or an equivalent construction,
which the library does not yet have. Worker 2 retains the arithmetic
instantiation, the norm and tower maps, and the inverse limit (task
`6c50b2fd`).

## `LocalRelativeWeilMapStatement`

`LocalRelativeWeilMapStatement` is the conjunction of the two statements
above. All three definitions have universe parameter `u`, the common
universe of `F`, `E` and the class families, and return `Prop`.

## Provenance

The statements are a derived finite-level formulation of Tate 1979,
Proposition (1.6.1), with the conjugacy argument of §1.5. They are stated
over the library's arbitrary class families and its actual local Weil
groups. The existence hypotheses are those of the published global
fundamental-class statement (Artin–Tate). The sign convention is fixed by
the definition module.

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33,
  Part II (1979), source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  - §1.5, printed p.8 (PDF p.17): an automorphism of
    `0 → C_E → W_{E/F} → Gal(E/F) → 0` that is the identity on both ends is
    inner by an element of `C_E`, because `H^1(Gal(E/F), C_E) = 0`.
  - Proposition (1.6.1) and its proof, printed pp.8–9 (PDF pp.17–18):
    existence of `θ_v`, its
    commutative diagrams with `η`, and uniqueness up to inner automorphisms
    by the connected component `W_F^0` for number fields.
- E. Artin and J. Tate, *Class Field Theory* (2009), source
  `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
  Chapter XV §1, Definition 1 and Theorem 1, printed pp.167–168
  (PDF pp.176–177): the extension class of `W_{E/F}` is the fundamental
  class.
