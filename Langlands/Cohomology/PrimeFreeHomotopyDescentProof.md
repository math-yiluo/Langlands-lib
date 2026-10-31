# Proof of descent of a finite free homotopy model from a prime localization

Author: Worker 1103.

This module proves the published proposition
`Langlands.Cohomology.ModuleComplex.PrimeFreeHomotopyDescentStatement.{u}`
as the theorem

```lean
theorem primeFreeHomotopyDescent : PrimeFreeHomotopyDescentStatement.{u}
```

with the universe `u` arbitrary. It imports the statement module, the helper
module `Langlands.Cohomology.ExtendScalarsLocalizationDescent` (its paired
Markdown lists the lemmas used below) and `Mathlib.Data.Int.Interval`. The
theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Nothing in the proof assumes a descended complex or the output homotopy
equivalence: the differentials of the given model, both chain maps, both
homotopies and all their equations are descended explicitly, following the
finite-presentation mechanism explained in the statement Markdown. No derived
category is used.

Throughout, `ext` denotes `ModuleCat.extendScalars φ` for a ring homomorphism
`φ : R →+* A`, and the scalar extension of a complex is the Library's
`baseChange φ`, whose terms and differentials are `ext` of those of `K`.

## Assembly over a ring in which `S` is inverted

Section `Assembly` builds a complex and a homotopy equivalence over `A` from
data over `R` that satisfy the required identities only up to powers of an
element `S : R`, given `σ : A` with `σ * φ S = 1`.

- `scaledExtendScalarsComplex φ D σ hD` is the complex with terms
  `ext (F i)` whose differential from degree `i` to `i + 1` is
  `σ • ext (D i (i + 1))` (and zero for other index pairs). The hypothesis `hD`
  is `ext (D i (i + 1) ≫ D (i + 1) (i + 1 + 1)) = 0`.
- `scaledExtendScalarsHomotopyEquiv` takes morphisms `Φ i : F i ⟶ K.X i`,
  `Ψ i : K.X i ⟶ F i`, `H i j : F i ⟶ F j`, `G i j : K.X i ⟶ K.X j` and the
  identities, after applying `ext`,

  - `ext (S • (Φ i ≫ K.d i (i + 1))) = ext (D i (i + 1) ≫ Φ (i + 1))`,
  - `ext (Ψ i ≫ D i (i + 1)) = ext (S • (K.d i (i + 1) ≫ Ψ (i + 1)))`,
  - `ext (Φ i ≫ Ψ i) = ext (D i (i + 1) ≫ H (i + 1) i + H i (i - 1) ≫ D (i - 1) i + (S * S) • 𝟙)`,
  - `ext (Ψ i ≫ Φ i) = ext (S • (K.d i (i + 1) ≫ G (i + 1) i + G i (i - 1) ≫ K.d (i - 1) i) + (S * S) • 𝟙)`.

  Its chain maps are `σ • ext (Φ i)` and `σ • ext (Ψ i)`, and its homotopies
  have components `σ • ext (H i j)` and `σ • ext (G i j)` for `j + 1 = i`
  (zero otherwise). Each required equation is the corresponding identity
  above multiplied by a power of `σ`, using `extendScalars_map_smul` and the
  scalar identities `σ * σ * φ (S * S) = 1` and `σ * σ * φ S = σ`
  (`smul_smul_extendScalars_map_eq_one`, `smul_smul_extendScalars_map_eq_self`).
  The homotopy equations are checked in degree `i` through Mathlib's
  `dNext_eq` and `prevD_eq`.

## The core descent lemma

`exists_away_homotopyEquiv_of_extendScalars` takes a localization map
`φ : R →+* A` at a submonoid `T`, a complex `K` over `R` with finitely
presented terms, finitely presented modules `F i`, a finite set `s` of degrees
outside which both `F i` and `K.X i` are zero, and morphisms over `A`

- `dL i j : ext (F i) ⟶ ext (F j)` with `dL i (i + 1) ≫ dL (i + 1) (i + 1 + 1) = 0`,
- `fL i : ext (F i) ⟶ ext (K.X i)` and `gL i : ext (K.X i) ⟶ ext (F i)`
  commuting with `dL` and `ext (K.d)`,
- `hL i j : ext (F i) ⟶ ext (F j)` and `kL i j : ext (K.X i) ⟶ ext (K.X j)`
  satisfying the two homotopy identities
  `fL i ≫ gL i = dL i (i + 1) ≫ hL (i + 1) i + hL i (i - 1) ≫ dL (i - 1) i + 𝟙` and
  `gL i ≫ fL i = ext (K.d i (i + 1)) ≫ kL (i + 1) i + kL i (i - 1) ≫ ext (K.d (i - 1) i) + 𝟙`.

It concludes that for some `r ∈ T` there is a complex `P` over
`Localization.Away r` with `P.X i ≅ ext' (F i)` in every degree and a
homotopy equivalence from `P` to `(baseChange (algebraMap R (Localization.Away r))).obj K`,
where `ext'` is extension of scalars to `Localization.Away r`. The proof:

1. Lift the morphisms. By `exists_mem_forall₂_extendScalars_map_eq_smul` and
   `exists_mem_forall_extendScalars_map_eq_smul` (finitely many degrees in
   `s`; zero modules elsewhere), there are `t₁, …, t₅ ∈ T` such that
   `φ t₁ • dL`, `φ t₂ • fL`, `φ t₃ • gL`, `φ t₄ • hL`, `φ t₅ • kL` are
   extensions of morphisms over `R` in all degrees. With
   `S = t₁ * t₂ * t₃ * t₄ * t₅ ∈ T`, `exists_extendScalars_map_eq_smul_of_dvd`
   and `choose` give `D`, `Φ`, `Ψ`, `H`, `G` over `R` with
   `ext (D i j) = φ S • dL i j`, `ext (Φ i) = φ S • fL i`, and so on.
2. Compute over `A`. Substituting these into the five identities over `A`
   gives `ext (D i (i + 1) ≫ D (i + 1) (i + 1 + 1)) = ext 0` and the four
   identities listed in the assembly section, with the factors of `S` placed
   as there.
3. Kill the differences over `R`. By
   `exists_mem_forall_smul_eq_of_extendScalars_map_eq` there are
   `u₁, …, u₅ ∈ T` such that the two sides of each of the five identities,
   as morphisms over `R`, agree after multiplication by the corresponding `uₖ`
   in all degrees.
4. Invert one element. Put `r = S * u₁ * u₂ * u₃ * u₄ * u₅ ∈ T`. In
   `Localization.Away r` the images of `r`, hence of its divisors `S` and the
   `uₖ`, are units, so `extendScalars_map_eq_of_smul_eq` turns the equations
   of step 3 into the identities required by the assembly section for
   `φ = algebraMap R (Localization.Away r)`. With `σ` the inverse of the image
   of `S`, `P` is `scaledExtendScalarsComplex`, its terms are literally
   `ext' (F i)` (so the isomorphisms are `Iso.refl`), and the homotopy
   equivalence is `scaledExtendScalarsHomotopyEquiv`.

The equations are transported from `R` directly to `Localization.Away r`; no
comparison map from `Localization.Away r` to `A` is used.

## The main theorem

Let `R`, `K`, `p`, `n`, `L`, the homotopy equivalence `E` from `L` to the
localization of `K` at `p`, and the linear equivalences
`L.X i ≃ₗ (Fin (n i) → R_p)` be given.

- The target complex of `E` is first restated, by definitional unfolding, as
  the complex with terms `ext (K.X i)` and differentials `ext (K.d i j)`, so
  that the components of `E` have these types syntactically.
- `Localization.AtPrime p` is a localization at `p.primeCompl`
  (`isLocalization_iff_isLocalizationMap`).
- From `IsStrictlyPerfect K` take bounds `a, b` and finite projective terms,
  which are finitely presented (`Module.finitePresentation_of_projective`).
  From `IsFiniteFree L` take bounds `a', b'`.
- Outside `[a', b']` the term `L.X i` is zero; since `R_p` is nontrivial,
  `Fin (n i) → R_p` can only be a subsingleton if `n i = 0`. So `n i = 0`
  there.
- Put `F i = Fin (n i) → R` (finitely presented, and zero when `n i = 0`) and
  `s = Finset.Icc (min a a') (max b b')`; outside `s` both `F i` and `K.X i`
  are zero.
- `nonempty_extendScalars_pi_equiv` and the given rank equivalences give
  isomorphisms `e i : L.X i ≅ ext (F i)`.
- Apply the core lemma with `dL i j = (e i).inv ≫ L.d i j ≫ (e j).hom`,
  `fL i = (e i).inv ≫ E.hom.f i`, `gL i = E.inv.f i ≫ (e i).hom`,
  `hL i j = (e i).inv ≫ E.homotopyHomInvId.hom i j ≫ (e j).hom` and
  `kL i j = E.homotopyInvHomId.hom i j`. The five identities follow from
  `L.d_comp_d`, the commutation of the chain maps `E.hom` and `E.inv`, and
  the homotopy equations of `E.homotopyHomInvId` and `E.homotopyInvHomId`
  in degree `i` (via `dNext_eq` and `prevD_eq`).
- The core lemma gives `r ∉ p` (membership in `p.primeCompl`), a complex `P`
  over `R_r = Localization.Away r` and a homotopy equivalence from `P` to the
  localization of `K` at `r`. Composing `P.X i ≅ ext' (F i)` with
  `nonempty_extendScalars_pi_equiv` gives `P.X i ≃ₗ (Fin (n i) → R_r)`. These
  terms are zero where `n i = 0`, in particular outside `[a', b']`, so `P` is
  bounded by `a', b'` (`isStrictlyGE_iff`, `isStrictlyLE_iff`), and its terms
  are finite and free, so `IsFiniteFree P` holds.

The proof uses no noetherian, local or global-freeness hypothesis on `R` or
the terms of `K`. It does not construct or record any relation between `P`
and `L` beyond what the proposition states.
