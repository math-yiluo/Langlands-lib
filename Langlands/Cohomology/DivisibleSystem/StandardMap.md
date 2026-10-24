# Maps of standard resolutions along a functor

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.TotalExact`
(`standardRows`, `standardRowsAugmentation`, `standardRowsAugmentationApp`,
the typed row and column differentials `standardRowsD₁`, `standardRowsD₂`
with `ιTotal_standardRows_d`, the maps out of a total complex after a functor
`totalMapDesc`, `map_ιTotal_totalMapDesc`, `totalMap_hom_ext`, and
`StandardContraction.quasiIso_standardRowsAugmentation`), and through it on
`Langlands.Cohomology.DivisibleSystem.TotalComparison` (`columnRestriction`,
`columnSummand`, `columnComparisonF`, `ιTotal_columnComparisonF`, the
isomorphism `columnComparison` with `isIso_columnComparison`, and
`standardTotalSystemToExtend`), `…StandardExact` (`StandardContraction`,
`augmentation_app_f_zero`, `indResBotContraction`), `…Total`
(`upFin N`, `upFinEmbedding N`, `upFin_π`, `upFinTotalFunctor`,
`standardTotalSystem`) and `…StandardResolution` (`standardPow`,
`standardDifferential`, `standardDifferential_succ`, `standardResolution`,
`standardResolution_obj_d`, `indResBot`, `indResBotCounit`). It also uses
`Langlands.Cohomology.DerivedPlus` (`extendXMapIso`, `mapExtendIso`, the
comparison between extending `Φ L` to `ℤ` and `Φ` of `L` extended to `ℤ`).
From Mathlib it uses total complexes of double complexes, Mathlib's
`HomologicalComplex.extend`, quasi-isomorphisms, and the representation
theory of `Representation.IndV`, `Representation.ind`,
`Representation.Coinvariants`, `Rep.indResAdjunction`, `Rep.resFunctor` and
`MonoidHom.card_fiber_eq_of_mem_range`.

Everything is in the namespace `Langlands.Cohomology`; the declarations of
the second to fifth sections are in `Langlands.Cohomology.StandardMap`, those
of the last section in `Langlands.Cohomology.DivisibleSystem`.

Notation: composition `f ≫ g` is `f` followed by `g`. `P^n` is
`standardPow P n` and `d_n : P^(n+1) ⟶ P^n` is `standardDifferential P ε n`,
so `d_0 = ε` and `d_(n+1) = ε P^(n+1) - P d_n` (`standardDifferential_succ`).
The standard resolution of `X` has `P^(r+1) X` in degree `r` with
differential `d_(r+1)`, augmented to `X` by `ε` in degree `0`. For a cochain
complex `L : CochainComplex A ℕ`, `standardRows N P ε L` is the double
complex with term `P^(r+1) L^q` at `(q, r)`, rows `q < N` (shape `upFin N`)
and columns `r : ℕ` (shape `ComplexShape.down ℕ`); its total complex has the
summand `(q, r)` in degree `q - r`, and `ι_(q,r)` is the summand inclusion
`ιTotal`. The total differential is the row differential plus `(-1)^q` times
the column differential (signs of the Total module).

## Extension to `ℤ` after a functor

`map_extendXIso_inv_comp F K h`: for `F` preserving zero morphisms and a term
`j = some i` of the extension of a complex `K` along an embedding of complex
shapes, `F` of Mathlib's identification `(extend.XIso K h).inv :
K.X i ⟶ (K.extend e).X j` followed by the inverse of the Library's
`DerivedPlus.extendXMapIso F K j` is Mathlib's identification for `F K`.
It is used to compare the morphisms to `L` and `Φ L` extended to `ℤ`.

## The structure `StandardMap`

`A` and `B` are categories, `P : A ⥤ A` with `ε : P ⟶ 𝟭 A`,
`Q : B ⥤ B` with `η : Q ⟶ 𝟭 B`, and `Φ : A ⥤ B`.

- `StandardMap Φ P ε Q η` (structure): a natural transformation
  `θ : P ⋙ Φ ⟶ Φ ⋙ Q`, i.e. maps `Φ (P X) ⟶ Q (Φ X)` natural in `X`, with
  `θ_comp_η X : θ.app X ≫ η.app (Φ X) = Φ.map (ε.app X)` (compatibility
  with the augmentations).

For `t : StandardMap Φ P ε Q η`:

- `t.powApp n X : Φ (P^n X) ⟶ Q^n (Φ X)`, by recursion: the identity for
  `n = 0` (`powApp_zero`), and `θ` at `P^n X` followed by `Q` of
  `t.powApp n X` for `n + 1` (`powApp_succ`). `powApp_one_comp`:
  `t.powApp 1 X ≫ η.app (Φ X) = Φ.map (ε.app X)`. `powApp_naturality`:
  `t.powApp n` is natural in `X` (induction on `n`, from the naturality of
  `θ`), packaged as the natural transformation `t.pow n :
  P^n ⋙ Φ ⟶ Φ ⋙ Q^n`.
- `map_differential_comp_powApp n X` (`A`, `B` abelian, `Φ` additive):
  `Φ.map (d_n X) ≫ t.powApp n X = t.powApp (n + 1) X ≫ d'_n (Φ X)`, where
  `d'_n` is the differential for `Q`. Induction on `n`: for `n = 0` this is
  `powApp_one_comp`; for `n + 1` the two terms of `d_(n+1)` are treated
  separately, the `ε` term by `θ_comp_η` and the naturality of `η`, the
  `P d_n` term by the naturality of `θ` and the induction hypothesis.

## Maps of standard resolutions

With `P` and `Q` preserving zero morphisms (so that the standard resolutions
are defined):

- `t.resolution`: the natural transformation from the standard resolution
  along `P` followed by `Φ` (degreewise) to `Φ` followed by the standard
  resolution along `Q`, given in degree `r` by `t.powApp (r + 1) X`. It
  commutes with the differentials by `map_differential_comp_powApp`, and it
  is natural by `powApp_naturality`.
- `resolution_app_f_zero_comp X`: in degree `0`,
  `(t.resolution.app X).f 0 ≫ η.app (Φ X) = Φ.map (ε.app X)`, so the map of
  resolutions is compatible with the augmentations.

## Maps of total complexes

With `P` and `Q` additive, `N : ℕ` and `L : CochainComplex A ℕ`:

- `t.rowθ N L q r`: `t.powApp (r + 1) (L^q)`, typed as a map from `Φ` of the
  term `(q, r)` of `standardRows N P ε L` to the term `(q, r)` of
  `standardRows N Q η (Φ L)`. `rowθ_naturality` (the row differentials),
  `rowθ_d` (the column differentials, from `map_differential_comp_powApp`)
  and `rowθ_comp_augmentation` (in column `0`, followed by the augmentation
  of `Φ L` it is `Φ` of the augmentation of `L`, from `powApp_one_comp`).

With moreover `Φ` preserving finite colimits:

- `t.totalMapF N L n`: the map from `Φ` of the degree `n` term of the total
  complex of `standardRows N P ε L` to the degree `n` term of the total
  complex of `standardRows N Q η (Φ L)` given on the summand `(q, r)` by
  `t.rowθ N L q r` followed by `ι_(q,r)` (`totalMapDesc`);
  `map_ιTotal_totalMapF` is its defining property
  `Φ.map ι_(q,r) ≫ t.totalMapF N L n = t.rowθ N L q r ≫ ι_(q,r)`.
- `totalMapF_comm`: it commutes with the total differentials. On a summand
  the total differential is the row part plus the column part; the row parts
  match by `rowθ_naturality` (both zero when `q + 1 = N`), the column parts,
  both multiplied by the same sign `(-1)^q`, by `rowθ_d` (both zero in
  column `0`).
- `t.totalMap N L`: the resulting morphism of cochain complexes
  `Φ (Tot (standardRows N P ε L)) ⟶ Tot (standardRows N Q η (Φ L))`
  (`totalMap_f`).
- `totalMapF_naturality`, `totalMap_naturality`: `t.totalMap N L` is natural
  in `L`, the latter stated with `upFinTotalFunctor`.
- `totalMapF_comp_columnComparisonF`, `totalMap_comp_toExtend`: for `L`
  vanishing in degrees `q ≥ N` (hypothesis `hL`), `t.totalMap N L` followed
  by the morphism from the total complex of `standardRows N Q η (Φ L)` to
  `Φ L` extended to `ℤ` (the totalized augmentation
  `standardRowsAugmentation`, then the isomorphism `columnComparison` of the
  TotalComparison module) equals `Φ` of the corresponding morphism for `L`,
  followed by the inverse of `DerivedPlus.mapExtendIso Φ L`, i.e. the
  identification of `Φ` of `L` extended to `ℤ` with `Φ L` extended to `ℤ`.
  On the summand `(q, r)`: for `r ≥ 1` both sides vanish (the column part of
  the target is in column `0` only); for `r = 0` it is
  `rowθ_comp_augmentation` followed by `map_extendXIso_inv_comp`.
- `quasiIso_totalMap` (`Φ` also preserving finite limits): if `L` vanishes in
  degrees `q ≥ N` and the totalized augmentations
  `standardRowsAugmentation N P ε L` and
  `standardRowsAugmentation N Q η (Φ L)` are quasi-isomorphisms (hypotheses
  `hP`, `hQ`), then `t.totalMap N L` is a quasi-isomorphism. Proof: the
  composites with the isomorphisms `columnComparison` are
  quasi-isomorphisms; `Φ` is exact, so it preserves homology and maps the
  composite for `L` to a quasi-isomorphism; by `totalMap_comp_toExtend` the
  composite of `t.totalMap N L` with a quasi-isomorphism is a
  quasi-isomorphism, hence so is `t.totalMap N L` (Mathlib's
  `quasiIso_of_comp_right`).

## ℓ-divisible systems

With `P`, `Q` additive and exact and `Φ` exact, for an `ℓ`-divisible system
`K` of `ℕ`-graded cochain complexes in `A`:

- `t.standardTotalSystemMap N K`: the morphism of `ℓ`-divisible systems from
  `K.standardTotalSystem N P ε` mapped by `Φ` (degreewise) to
  `(K.map Φ).standardTotalSystem N Q η` (here `K.map Φ` maps degreewise),
  given at level `m` by `t.totalMap N (K.obj m)`
  (`standardTotalSystemMap_tower_app`). It commutes with the transition maps
  of the systems by `totalMap_naturality`.
- `standardTotalSystemMap_tower_app_comp`: `totalMap_comp_toExtend` at every
  level, with the Library's `standardTotalSystemToExtend` for `K` and for
  `K.map Φ`, for `K` vanishing in degrees `q ≥ N`.
- `quasiIso_standardTotalSystemMap_tower_app`: given contractions
  `c : StandardContraction F P ε` and `c' : StandardContraction F' Q η`
  along faithful exact functors `F`, `F'` (the StandardExact module), each
  level of `t.standardTotalSystemMap N K` is a quasi-isomorphism, for `K`
  vanishing in degrees `q ≥ N`. The hypotheses `hP`, `hQ` of
  `quasiIso_totalMap` are the TotalExact module's
  `quasiIso_standardRowsAugmentation` for `c` and `c'`.

## The normalized fiber sum

`k` is a commutative ring, `Γ` and `Γ'` are groups, `Γ'` is finite
(`Fintype`), `Γ` has decidable equality, and `π : Γ' →* Γ`. For a
representation `V` of `Γ`, `Ind_1^Γ Res_1^Γ V` (the Library's `indResBot`) is
Mathlib's induced representation along `⊥ ⊆ Γ`: the coinvariants for the
trivial group of `k[Γ] ⊗ V`, with elements `⟦γ ⊗ v⟧` and action
`g · ⟦γ ⊗ v⟧ = ⟦γ g⁻¹ ⊗ v⟧` (`Representation.ind_mk`). Write `c` for
`Ring.inverse |ker π|` in `k`, the inverse of `|ker π|` (`Nat.card`) when it
is a unit and `0` otherwise.

- `fiberAverageLinear k π V`: the `k`-linear map
  `Ind_1^Γ Res_1^Γ V ⟶ Ind_1^Γ' Res_1^Γ' (Res_π V)`,
  `⟦γ ⊗ v⟧ ↦ c • ∑_{γ' : π γ' = γ} ⟦γ' ⊗ v⟧` (`fiberAverageLinear_mk`),
  built with `Coinvariants.lift`, `TensorProduct.lift` and `Finsupp.lift`.
- `fiberAverageLinear_comm`: it intertwines the action of `π g` with the
  action of `g`, because `γ' ↦ γ' g⁻¹` maps the fiber of `π` over `γ`
  bijectively onto the fiber over `γ (π g)⁻¹`.
- `indResBotCounit_app_mk`: the counit `Ind_1^Γ Res_1^Γ V ⟶ V` (the
  Library's `indResBotCounit`, from `Rep.indResAdjunction`) sends
  `⟦γ ⊗ v⟧` to `γ⁻¹ v`.
- `fiberAverage k π`: the natural transformation
  `Ind_1^Γ Res_1^Γ ⋙ Res_π ⟶ Res_π ⋙ Ind_1^Γ' Res_1^Γ'` with components
  `fiberAverageLinear k π V` (`fiberAverage_app_mk`).
- `card_filter_eq_nat_card_ker`: for `π` surjective, every fiber of `π` has
  `|ker π|` elements (Mathlib's `MonoidHom.card_fiber_eq_of_mem_range`).
- `groupStandardMap k π hπ hk`: for `π` surjective (`hπ`) and `|ker π|` a
  unit in `k` (`hk`), the `StandardMap (Res_π) (Ind_1^Γ Res_1^Γ) (counit)
  (Ind_1^Γ' Res_1^Γ') (counit)` with `θ = fiberAverage k π`. The
  compatibility `θ_comp_η` is the computation
  `c • ∑_{π γ' = γ} γ'⁻¹ v = c • |ker π| • γ⁻¹ v = γ⁻¹ v` on `⟦γ ⊗ v⟧`:
  each `γ'⁻¹` acts on `Res_π V` as `(π γ')⁻¹ = γ⁻¹`, the fiber has
  `|ker π|` elements, and `c |ker π| = 1`. Without the normalization the
  composite would be `|ker π|` times the counit; this is why `|ker π|` must
  be invertible in `k`.

## The group case for ℓ-divisible systems

Moreover `Γ` is finite. For `π` surjective, `|ker π|` a unit in `k`, and an
`ℓ`-divisible system `K` of `ℕ`-graded cochain complexes of representations
of `Γ`:

- `DivisibleSystem.groupStandardTotalSystemMap π hπ hk N K`: the morphism
  `t.standardTotalSystemMap N K` for `t = groupStandardMap k π hπ hk`, from
  `Res_π` of `K.groupStandardTotalSystem N` (the standard resolutions along
  `Ind_1^Γ Res_1^Γ`) to `(K.map Res_π).groupStandardTotalSystem N` (the
  standard resolutions along `Ind_1^Γ' Res_1^Γ'` of `Res_π K`).
- `DivisibleSystem.groupStandardTotalSystemMap_tower_app_comp`:
  `standardTotalSystemMap_tower_app_comp` for it, with the Library's
  `groupStandardTotalSystemToExtend`.
- `DivisibleSystem.quasiIso_groupStandardTotalSystemMap_tower_app`: for `K`
  vanishing in degrees `q ≥ N`, each level is a quasi-isomorphism, by
  `quasiIso_standardTotalSystemMap_tower_app` with the contractions
  `indResBotContraction` for `Γ` and for `Γ'`.

## Provenance and interpretation

Harris (1999) writes `M_m^{q,H} = G_m^q(U(ẽ)_F̄)^H` and obtains the standard
resolution (2.5) of `M_m^{q,H}` "by iterating the functorial surjection
(2.4) `Z_ℓ[S(ẽ)/H] ⊗_{Z_ℓ} (•) → •`" (p.305). On p.306, after forming
`C_m^{•,H}` from these resolutions: "When we replace H by a subgroup H'
which is normal in S(e), we obtain a natural isomorphism
C_m^{•,H} = [C_m^{•,H'}]^H." (p.306 prints `S(e)` where p.305 has `S(ẽ)`.)
He then takes the direct limit as `H` shrinks to the identity to obtain
(2.6). Both passages were read visually from the scan by Worker 61.

1. What is formalized. This module does not formalize that isomorphism, and
   does not use any identification of the `H`-invariants of the standard
   resolutions of the `M_m^{q,H'}` with the standard resolutions of the
   `M_m^{q,H}`. It builds maps of standard resolutions along a change of
   group: for `Γ' = S(ẽ)/H'`, `Γ = S(ẽ)/H` and `π` the projection (kernel
   `H/H'`), `groupStandardMap` relates the resolutions (2.4) for `S(ẽ)/H`,
   restricted to `S(ẽ)/H'`, to the resolutions for `S(ẽ)/H'` of the same
   (restricted) modules, and `groupStandardTotalSystemMap` does so for the
   total complexes. Composing with the inclusions `M_m^{q,H} ⊆ M_m^{q,H'}`
   to compare `C_m^{•,H}` with `C_m^{•,H'}` is not done here.
2. What is derived. The structure `StandardMap`, its iterated comparisons,
   the maps of resolutions and total complexes, their compatibility with
   the comparisons to `ℤ`-extended complexes, the quasi-isomorphisms and the
   normalized fiber sum are ours; Harris writes none of them. The
   normalization by `|ker π|⁻¹` is what makes the fiber sum compatible with
   the counits (see `groupStandardMap`). In Harris's
   setting `|ker π| = [H : H']`; when `H` is pro-`p` and `H'` has finite
   index in `H` this index is a power of `p`, invertible in `Z/ℓ^mZ` since
   `p ≠ ℓ`. This is not formalized here: `hk` is an explicit hypothesis.
3. Hypotheses. Surjectivity of `π`, finiteness of `Γ'` (and of `Γ`, for the
   system corollaries) and the vanishing of `K` in degrees `q ≥ N` are
   explicit hypotheses.

## Scope

The module constructs maps and proves level-wise quasi-isomorphisms. It does
not address freeness, the inclusion of invariants `M_m^{q,H} ⊆ M_m^{q,H'}`,
the comparison of `C_m^{•,H}` with `C_m^{•,H'}`, the isomorphism
`C_m^{•,H} = [C_m^{•,H'}]^H`, transitivity in `H`, the direct limit over
`H`, (2.6), (2.7) or Lemma 2.8.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
