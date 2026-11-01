# Gauge classification of line bundles glued from unit cocycles

Module `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleGauge`, namespace
`Langlands.AlgebraicGeometry.Picard.CocycleGluing`.

This module classifies morphisms and isomorphisms between the sheaves
`glued g` built in `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof`.
Fix a scheme `X`, an index type `ι : Type u` and a family of opens
`T : ι → X.Opens`. Let `g h : ∀ i j, (Γ(X, T i ⊓ T j))ˣ` be unit families
satisfying the cocycle identity `IsCocycle`. The main theorem is

```
theorem nonempty_iso_glued_iff (hg : IsCocycle g) (hh : IsCocycle h) :
    Nonempty (glued g ≅ glued h) ↔ ∃ a : ∀ i : ι, (Γ(X, T i))ˣ, IsGauge g h a
```

Here `IsGauge g h a` says that `h i j = a i * g i j * (a j)⁻¹` on
`T i ⊓ T j` for all `i j`, with `a i` and `(a j)⁻¹` restricted to the overlap.
So the glued sheaves are isomorphic exactly when the two cocycles differ by a
multiplicative Čech coboundary of units. The theorem has no cover hypothesis:
the family `T` need not cover `X`.

## Conventions

The conventions are those of `CocycleLineBundleProof`. A section of
`glued g` over `U` is a family `(b i)` with `b i ∈ Γ(X, U ⊓ T i)` and
`b i = g i j * b j` on every open inside `U ⊓ T i ⊓ T j`. `comp g m i` is the
`i`-th component of a section `m`. `genSec g hg i hV` is the local generator
over an open `V ≤ T i`. Its `j`-th component is `g j i` restricted, and
`smul_genSec_bijective` says that `glued g` is free on it over `V`.

The gauge acts on components by multiplication. The morphism defined by `a`
multiplies the `i`-th component by `a i`, and it sends `genSec g i` to
`a i • genSec h i`.

## Declarations

### Componentwise multiplication

- `app_presheaf_map`: a morphism `φ : M ⟶ N` of `X.Modules` commutes with
  restriction, `φ (m|_V) = (φ m)|_V`.
- `gaugeFam a b` for `a : ∀ i, Γ(X, T i)` and `b : Fam T U` is the family with
  components `a i|_(U ⊓ T i) * b i`. Lemmas: `gaugeFam_apply`, `gaugeFam_add`,
  `gaugeFam_smul`, and `famRes_gaugeFam` (it commutes with restriction).

### Gauges and the gauge morphism

- `IsGaugeFamily g h a` for `a : ∀ i, Γ(X, T i)` (not necessarily units) is the
  identity `a i * g i j = h i j * a j` on `T i ⊓ T j`, for all `i j`.
- `IsGauge g h a` for units `a : ∀ i, (Γ(X, T i))ˣ` is the identity
  `h i j = a i * g i j * (a j)⁻¹` on `T i ⊓ T j`, for all `i j`.
- `isGauge_iff`: `IsGauge g h a ↔ IsGaugeFamily g h (fun i ↦ (a i : Γ(X, T i)))`.
- `IsGaugeFamily.inv` and `IsGauge.inv`: the pointwise inverse of a unit gauge
  from `g` to `h` is a unit gauge from `h` to `g`.
- `compat_gaugeFam`: if `IsGaugeFamily g h a` and `b` satisfies the relation
  for `g`, then `gaugeFam a b` satisfies the relation for `h`.
- `gaugeHom a ha : glued g ⟶ glued h` for `ha : IsGaugeFamily g h a` is the
  morphism sending `mk g b hb` to `mk h (gaugeFam a b) _`. `IsCocycle` is not
  needed to define it.
- `comp_gaugeHom_app`: the `i`-th component of `gaugeHom a ha` applied to `m`
  is `a i|_(U ⊓ T i) * comp g m i` (by `rfl`).
- `gaugeHom_app_genSec`: for cocycles `g` and `h`,
  `gaugeHom a ha (genSec g i) = a i|_V • genSec h i` over `V ≤ T i`.
- `gaugeHom_comp_gaugeHom`: if `a i * a' i = 1` for all `i`, then
  `gaugeHom a ha ≫ gaugeHom a' ha' = 𝟙`.
- `gaugeIso a ha : glued g ≅ glued h` for a unit gauge `ha : IsGauge g h a`.
  Its `hom` is `gaugeHom` of `a` and its `inv` is `gaugeHom` of `a⁻¹`.
- `comp_gaugeIso_hom_app` (component formula, by `rfl`) and
  `gaugeIso_hom_app_genSec`
  (`(gaugeIso a ha).hom (genSec g i) = a i|_V • genSec h i`).

### Every morphism is a gauge morphism

From here on `g`, `h` and `k` are cocycles (`hg`, `hh`, `hk`).

- `genSec_eq_smul_genSec`: over an open `V` inside `T i` and `T j`,
  `genSec g j = g i j|_V • genSec g i`.
- `comp_eq_of_map_eq`: two sections over `U` have equal `i`-th components if
  their restrictions to `U ⊓ T i` are equal.
- `hom_ext_genSec`: two morphisms `glued g ⟶ glued h` that agree on every local
  generator `genSec g i` over every `V ≤ T i` are equal. Proof: on `U ⊓ T i`
  every section is a multiple of `genSec g i` (`smul_genSec_bijective`), so the
  two morphisms agree on the restriction to `U ⊓ T i` of any section. Hence the
  `i`-th components of the images agree, by `comp_eq_of_map_eq`.
- `coeff hg hh φ i : Γ(X, T i)` for `φ : glued g ⟶ glued h` is the unique `c`
  with `φ (genSec g i) = c • genSec h i` over `T i`. It is defined through
  `smul_genSec_bijective` for `h`. Lemmas: `app_genSec_top`, `coeff_eq_of`
  (uniqueness), and `app_genSec`
  (`φ (genSec g i) = (coeff φ i)|_V • genSec h i` over any `V ≤ T i`, by
  naturality and `map_genSec`).
- `isGaugeFamily_coeff`: `IsGaugeFamily g h (coeff hg hh φ)`. Proof: on
  `T i ⊓ T j`, compute `φ (genSec g j)` in two ways using
  `genSec_eq_smul_genSec` for `g` and for `h`. Then cancel `genSec h i` using
  injectivity in `smul_genSec_bijective`.
- `eq_gaugeHom`: `φ = gaugeHom (coeff hg hh φ) _`, by `hom_ext_genSec`.
- `comp_app_eq`: the component formula
  `comp h (φ m) i = (coeff φ i)|_(U ⊓ T i) * comp g m i` for every morphism `φ`.
- `coeff_gaugeHom`: `coeff hg hh (gaugeHom a ha) = a`.
- `coeff_comp`: `coeff (φ ≫ ψ) i = coeff φ i * coeff ψ i`.
- `coeff_id`: `coeff (𝟙 (glued g)) i = 1`.

### Isomorphisms

- `isoUnits hg hh e i : (Γ(X, T i))ˣ` for `e : glued g ≅ glued h` has value
  `coeff e.hom i` and inverse `coeff e.inv i`. The two products are `1` by
  `coeff_comp`, `coeff_id` and the identities `e.hom ≫ e.inv = 𝟙` and
  `e.inv ≫ e.hom = 𝟙`. Lemma: `isoUnits_val`.
- `isGauge_isoUnits`: `IsGauge g h (isoUnits hg hh e)`.
- `iso_hom_app_genSec`:
  `e.hom (genSec g i) = (isoUnits e i)|_V • genSec h i` over `V ≤ T i`.
- `iso_eq_gaugeIso`: `e = gaugeIso (isoUnits hg hh e) _`.
- `isoUnits_gaugeIso`: `isoUnits hg hh (gaugeIso a ha) = a`.
- `nonempty_iso_glued_iff`: the theorem displayed above. Forward direction:
  `isoUnits` with `isGauge_isoUnits`. Backward direction: `gaugeIso`.

`iso_eq_gaugeIso` and `isoUnits_gaugeIso` together say that `e ↦ isoUnits e`
is a bijection from isomorphisms `glued g ≅ glued h` to unit gauges from `g`
to `h`. The module states the two identities, not a packaged equivalence.

## Sources and provenance

Provenance: derived. This is the line-bundle form of the injectivity of
Čech H¹ in torsor cohomology, specialised to the explicit gluing
`CocycleGluing.glued`. Sources:

- Stacks Project, Cohomology of Sheaves, Lemma `cohomology-lemma-cech-h1`
  (tag 0B8R). Source at Stacks commit a04446e5, file `cohomology.tex`,
  lines 1485-1512 (tag map: `tags.txt` line 14149). The lemma says that
  Čech H¹ of a covering injects into H¹. Its proof attaches to a torsor with
  local sections `s_i` the cocycle `s_{i0 i1}` determined by
  `s_{i0 i1} · s_{i0} = s_{i1}`, and says that its class does not depend on
  the choice of the `s_i`.
- Stacks Project, Cohomology of Sheaves, Lemma `cohomology-lemma-h1-invertible`
  (tag 09NU). Same file, lines 405-474 (tag map: `tags.txt` line 12227). It
  identifies `H¹(X, O_X^*)` with `Pic(X)` by sending an invertible sheaf `L` to
  the `O_X^*`-torsor of its local generators.

Both files are in the registered source folder
`stacks-flasque-affine-vanishing-kunneth-a04446e5`.

Correspondence with the sources. The local generators `genSec g i` play the
role of the sections `s_i`, and `genSec_eq_smul_genSec` is the relation
`s_{ij} · s_i = s_j` with `s_{ij} = g i j`. An isomorphism `e` carries each
`genSec g i` to a unit multiple `a i • genSec h i` (`iso_hom_app_genSec`).
Changing the local generators by the units `a i` changes the cocycle by the
coboundary of `a`, which is the condition `IsGauge`. The Lean proof is direct.
It uses neither torsors nor Čech cohomology groups. Everything is computed on
the components of `glued g`, through the freeness statement
`smul_genSec_bijective`.

Differences from the sources. The sources work with a covering and with
cohomology classes. This module works with an arbitrary family of opens and
states the result for the specific sheaves `glued g`. It also classifies all
morphisms (`eq_gaugeHom`, `coeff`), not only isomorphisms.
