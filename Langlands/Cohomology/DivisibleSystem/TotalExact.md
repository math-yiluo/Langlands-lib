# The totalized augmentation is a quasi-isomorphism

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.TotalComparison`
(the abbreviations `columnZero`, `columnRestriction`, the isomorphism
`columnComparison` and the composites `…TotalSystemToExtend`) and
`Langlands.Cohomology.DivisibleSystem.StandardExact` (the structure
`StandardContraction`, its identity `identity'`, `augmentation_app_f_zero` and
`indResBotContraction`), and through them on the earlier modules of the series
(`upFin N`, `upFinEmbedding N`, `upFin_π`, `upFinFiber N n` from the Total
module; `standardPow`, `standardDifferential`, `standardResolution`,
`standardResolution_obj_d` from the StandardResolution module). From Mathlib
it uses total complexes of double complexes (`HomologicalComplex₂.total`,
`ιTotal`, `d₁`, `d₂`, `total_d`, `ι_D₁`, `ι_D₂`, `d₁_eq`, `d₂_eq`,
`d₁_eq_zero`, `d₂_eq_zero`, `ιTotal_map`), homotopies and homotopy
equivalences, and the comparison of quasi-isomorphisms along a functor that
preserves homology. The first two sections are in the namespace
`Langlands.Cohomology`, the next three in
`Langlands.Cohomology.StandardContraction`, the last in
`Langlands.Cohomology.DivisibleSystem`.

On p.306 Harris forms `C_m^{•,H}`, the simple complex of the double complex of
the canonical resolutions (2.5) of the `M_m^{q,H}`. After the direct limit
over `H` he asserts a quasi-isomorphism (2.6). The Total module builds these
total complexes and their totalized augmentation, and the TotalComparison
module maps the augmentation target isomorphically to `K` extended to `ℤ` when
`K` vanishes in degrees `q ≥ N`. Neither proves a quasi-isomorphism. This
module proves that the totalized augmentation is a quasi-isomorphism, level by
level. Hence its composite with the comparison is one too, in particular from
Harris's `C_m^{•,H}` (the InvariantTotal module) to the `H`-invariant section
complexes extended to `ℤ`.

Notation: composition `f ≫ g` is `f` followed by `g`. `P^n` is
`standardPow P n` and `d_n : P^(n+1) ⟶ P^n` is `standardDifferential P ε n`,
so `d_0 = ε`. For `L : CochainComplex A ℕ` the double complexes have rows
`q : Fin N` (shape `upFin N`, row differential `(q, r) ⟶ (q + 1, r)` when
`q + 1 < N`) and columns `r : ℕ` (shape `ComplexShape.down ℕ`, column
differential `(q, r + 1) ⟶ (q, r)`). The total degree of `(q, r)` is
`q - r` (`upFin_π`), and the total differential is the row differential plus
`(-1)^q` times the column differential (the Total module's signs
`ε₁ = 1`, `ε₂ (q, r) = (-1)^q`). `ι_(q,r)` is Mathlib's summand inclusion
`ιTotal` of the term `(q, r)` into the degree `q - r` term of a total complex.

## Maps out of a total complex after a functor

`A` is abelian, `B` is a category, `F : A ⥤ B` preserves finite colimits, and
`Y` is a double complex with rows `upFin N` and columns `down ℕ`.

- `totalMapIsColimit F Y n`: `F` of the degree `n` term of the total complex
  of `Y`, with the maps `F ι_(q,r)`, is a coproduct of the `F` of the terms
  `(q, r)` with `q - r = n`. The index set `upFinFiber N n` is finite (Total
  module), so `F` preserves this coproduct (Mathlib's
  `isColimitCofanMkObjOfIsColimit` applied to
  `Y.toGradedObject.isColimitCofanMapObj`).
- `totalMapDesc φ`: the morphism out of `F` of the degree `n` term given by
  maps `φ q r h` on the summands; `map_ιTotal_totalMapDesc` is its defining
  property `F ι_(q,r) ≫ totalMapDesc φ = φ q r h`, and `totalMap_hom_ext`
  says two morphisms out of that term agree if they agree after every
  `F ι_(q,r)`.

## The rows of the standard resolutions

`A` is abelian, `P : A ⥤ A` is additive, `ε : P ⟶ 𝟭 A`, `N : ℕ`,
`L : CochainComplex A ℕ`.

- `standardRows N P ε L` (abbreviation): the rows `q < N` of the double
  complex obtained by applying the standard resolution functor to `L`
  termwise, i.e. the restriction along `upFinEmbedding N` of
  `((standardResolution P ε).mapHomologicalComplex (up ℕ)).obj L`. Its term
  `(q, r)` is `P^(r+1) L^q`. It is the level-`m` double complex of the Total
  module's `standardTotalSystem N P ε K` for `L = K m`.
- `standardRowsAugmentation N P ε L` (abbreviation): the totalized
  augmentation, the map of total complexes from `standardRows N P ε L` to
  `columnRestriction N L` (the rows `q < N` of `L` placed in resolution
  degree `0`) induced by the augmentation of the standard resolutions. It is
  the level-`m` component of the Total module's
  `standardTotalSystemAugmentation N P ε K` for `L = K m`.
- `standardRowsAugmentationApp N P ε L q r`: its component on the term
  `(q, r)`, the degree `r` component of the augmentation of the standard
  resolution of `L^q`, typed with the two double complexes.
  `ιTotal_standardRowsAugmentation` says that the totalized augmentation is
  this component on each summand (Mathlib's `ιTotal_map`).
- `standardRowsD₁ N P ε L q r j`, `standardRowsD₂ N P ε L q r j`: Mathlib's
  row and column parts `d₁`, `d₂` of the total differential out of the term
  `(q, r)`, towards degree `j`. They are retyped with the total complex as
  codomain, so that they can be added to other maps into the total complex.
  The lemmas are: `ιTotal_standardRows_d` (the total differential on a
  summand is `standardRowsD₁ + standardRowsD₂`), `standardRowsD₁_eq` (for
  `q + 1 < N` the row part is `1 •` the row differential followed by
  `ι_(q+1,r)`), `standardRowsD₁_eq_zero` (no row part on the last row),
  `standardRowsD₂_eq` (the column part out of `(q, r + 1)` is
  `(-1)^q •` the column differential followed by `ι_(q,r)`) and
  `standardRowsD₂_zero` (no column part out of `(q, 0)`).

## The section and the contracting homotopy

`A`, `B` are abelian, `F : A ⥤ B` is additive and preserves finite colimits,
`P` is additive, and `c : StandardContraction F P ε` (a natural section
`σ : F ⟶ P ⋙ F` of `F ε`, StandardExact module).

Components, typed with the double complexes:

- `c.rowσ N L q r : F (P^(r+1) L^q) ⟶ F (P^(r+2) L^q)` and
  `c.colσ N L q : F L^q ⟶ F (P L^q)` are `σ` at `P^(r+1) L^q` and at `L^q`.
- `rowσ_naturality`, `colσ_naturality`: they commute with `F` of the row
  differentials (naturality of `σ` at `P^(r+1) (L.d q q')` and at
  `L.d q q'`).
- `colσ_comp`: `c.colσ N L q ≫ F (ε L^q) = 𝟙` (the field `σ_comp`).
- `rowσ_identity`: `c.rowσ q (r+1) ≫ F d_{r+2} + F d_{r+1} ≫ c.rowσ q r = 𝟙`
  on `F (P^(r+2) L^q)`, and `rowσ_identity_zero`:
  `c.rowσ q 0 ≫ F d_1 + F ε ≫ c.colσ q = 𝟙` on `F (P L^q)`. Both are the
  StandardExact module's `c.identity'` (for `n = r + 1` and `n = 0`),
  transported along `standardResolution_obj_d` and `augmentation_app_f_zero`.

The section of `F` of the totalized augmentation:

- `c.totalSectionSummand N L n q r h`: on the summand `(q, 0)` of the
  degree `n` term of the total complex of `columnRestriction N L`, it is
  `c.colσ N L q ≫ F ι_(q,0)`; on the summands `(q, r + 1)`, which are zero, it
  is `0` (`totalSectionSummand_zero`, `totalSectionSummand_succ`).
- `c.totalSectionF N L n` is the induced map of degree `n` terms
  (`totalMapDesc`; `map_ιTotal_totalSectionF`).
- `totalSectionF_comm`: it commutes with the differentials. On a summand
  `(q, r + 1)` the source is zero. On `(q, 0)` neither total differential has
  a column part (`down ℕ` has no arrow out of `0`); the row parts agree by
  `colσ_naturality` when `q + 1 < N` and vanish otherwise.
- `c.totalSection N L` is the resulting morphism of complexes
  `F (Tot (columnRestriction N L)) ⟶ F (Tot (standardRows N P ε L))` (with
  `F` applied termwise, Mathlib's `F.mapHomologicalComplex`).
- `totalSectionF_comp` and `totalSection_comp`: the section followed by `F`
  of the totalized augmentation is the identity. On a summand `(q, 0)` this is
  `colσ_comp`; the summands `(q, r + 1)` are zero.

The contracting homotopy:

- `c.totalHomotopySummand N L n m q r h`: on the summand `(q, r)` of degree
  `n`, towards degree `m`, it is `(-1)^q • (c.rowσ N L q r ≫ F ι_(q,r+1))`
  if `(q, r + 1)` has total degree `m`, and `0` otherwise
  (`totalHomotopySummand_eq`).
- `c.totalHomotopyF N L n m` is the induced map from the degree `n` term to
  the degree `m` term of `F (Tot (standardRows N P ε L))`
  (`map_ιTotal_totalHomotopyF`). It is `0` unless `m + 1 = n`
  (`totalHomotopyF_eq_zero`), since `(q, r + 1)` has degree `q - r - 1`.
- `row_cancel`: on the summand `(q, r)` of degree `i`, the row part of
  `d` followed by the homotopy cancels the homotopy followed by the row part
  of `d`. For `q + 1 < N` both terms are `σ` composed with the row
  differential up to sign (equal by `rowσ_naturality`), with signs
  `(-1)^(q+1)` and `(-1)^q`. For `q = N - 1` both row parts are zero.
- `col_identity`: on the same summand, the column part of `d` followed by
  the homotopy, plus the homotopy followed by the column part of `d`, plus the
  totalized augmentation followed by the section, is `F ι_(q,r)`. The signs
  `(-1)^q` of the homotopy and of the column differential multiply to `1`.
  For `r = r' + 1` this is `rowσ_identity` (the section term is zero, since
  the section is `0` on the summand `(q, r' + 1)`). For `r = 0` the
  column part out of `(q, 0)` is zero, the section term is
  `F ε ≫ c.colσ ≫ F ι_(q,0)`, and this is `rowσ_identity_zero`.
- `homotopy_summand`: combining the two, on each summand
  `F ι_(q,r) = F ι_(q,r) ≫ (d ≫ h + h ≫ d + F a ≫ s)`, where `d` is `F` of
  the total differential, `h` the homotopy, `a` the totalized augmentation
  and `s` the section. The proof splits `ι_(q,r) ≫ d` into its row and column
  parts by `ιTotal_standardRows_d` and finishes with `abel`.
- `c.totalHomotopy N L`: a Mathlib `Homotopy` from the identity of
  `F (Tot (standardRows N P ε L))` to `F a ≫ s`, with components
  `c.totalHomotopyF N L i j`. Its identity is checked on summands
  (`totalMap_hom_ext`) by `homotopy_summand`, using Mathlib's `dNext_eq` and
  `prevD_eq` for `up ℤ`.

## The quasi-isomorphism

- `c.totalHomotopyEquiv N L`: `F a` is a homotopy equivalence
  `F (Tot (standardRows N P ε L)) ≃ F (Tot (columnRestriction N L))`, with
  inverse `s`. The composite `F a ≫ s` is homotopic to the identity by
  `c.totalHomotopy` (reversed), and `s ≫ F a` equals the identity
  (`totalSection_comp`). No vanishing of `L` in high degrees is needed.
- `c.quasiIso_standardRowsAugmentation N L`: if moreover `F` is faithful and
  preserves finite limits, the totalized augmentation
  `standardRowsAugmentation N P ε L` is a quasi-isomorphism. A homotopy
  equivalence is a quasi-isomorphism (Mathlib's `HomotopyEquiv.quasiIso_hom`),
  so `F a` is one. An exact functor preserves homology (Mathlib's
  `Functor.preservesHomology_of_preservesEpis_and_kernels`). A faithful
  functor reflects monomorphisms and epimorphisms, hence reflects
  isomorphisms because the abelian category `A` is balanced (Mathlib's
  instance `reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms`).
  So Mathlib's `HomologicalComplex.quasiIso_map_iff_of_preservesHomology`
  reflects the quasi-isomorphism back to `a`.

## ℓ-divisible systems

`F` is additive, faithful and preserves finite limits and finite colimits, and
`P` is additive and preserves finite limits and finite colimits (as the
systems of the Total module require).

- `quasiIso_standardTotalSystemAugmentation N c K m`: for
  `K : DivisibleSystem (CochainComplex A ℕ) ℓ`, the level `m` component of the
  Total module's `K.standardTotalSystemAugmentation N P ε` is a
  quasi-isomorphism. It is `standardRowsAugmentation N P ε (K m)`.
- `quasiIso_standardTotalSystemToExtend N c K hK m`: for `K` with
  `hK : ∀ m q, N ≤ q → IsZero ((K m).X q)`, the level `m` component of the
  TotalComparison module's `K.standardTotalSystemToExtend N P ε hK`, the
  totalized augmentation followed by the comparison with `K` extended to `ℤ`,
  is a quasi-isomorphism: the comparison is an isomorphism
  (`isIso_columnComparison`), and Mathlib composes quasi-isomorphisms.
- For `k` a commutative ring, `Γ` a finite group and
  `K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ`:
  `quasiIso_groupStandardTotalSystemAugmentation N K m` and
  `quasiIso_groupStandardTotalSystemToExtend N K hK m`, the two statements
  above for `P = Ind_1^Γ Res_1^Γ` (the StandardResolution module's
  `indResBot k Γ`, counit `indResBotCounit k Γ`) with the StandardExact
  module's `c = indResBotContraction k Γ` for the forgetful functor to
  `k`-modules.
- `quasiIso_quotientInvariantsTotalSystemToExtend N K H hK hN m`: for a
  system `K` of complexes of smooth representations of `G`, `H` a normal
  subgroup of finite index, `hK` the surjectivity on `H`-invariants of the
  Invariants module and `hN` the vanishing in degrees `q ≥ N`, the level `m`
  component of the TotalComparison module's
  `K.quotientInvariantsTotalSystemToExtend N H hK hN` is a quasi-isomorphism.
  It is the previous statement for `Γ = G ⧸ H` and the system
  `K.quotientInvariantsComplexes H hK` of `H`-invariants.
- `quasiIso_smoothGodementInvariantTotalSystemToExtend h T D H hterm hres m`:
  the level `m` component of the TotalComparison module's
  `smoothGodementInvariantTotalSystemToExtend h T D H hterm hres`, from the
  InvariantTotal module's `C_m^{•,H}` (with `N = D + 2`) to the `H`-invariant
  compactly supported section complexes of the truncated smooth Godement
  system extended to `ℤ`, is a quasi-isomorphism. Here `hterm`, `hres` are
  the surjectivity hypotheses of the InvariantTotal module, and the vanishing
  in degrees `q ≥ D + 2` was discharged there.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. Worker 61
read (2.4), (2.5), the sentence "let `C_m^{•,H}` be the simple complex
associated to the double complex `K_m^{-•,•,H}` for each `m`" and (2.6) in the
scanned original.

1. What is from the source. After the direct limit over `H` Harris asserts
   the natural `S(ẽ)`-equivariant quasi-isomorphism (2.6)
   `C_m^• → G_m^•(U(ẽ)_F̄)`. He does not state separately that
   `C_m^{•,H} → M_m^{•,H}` is a quasi-isomorphism for each `H`, nor prove
   (2.6). We read the level-`H` quasi-isomorphism as the step behind (2.6),
   since direct limits are exact.
   `quasiIso_smoothGodementInvariantTotalSystemToExtend` is this level-`H`
   statement for the Library's stand-ins of the
   InvariantTotal module (its target is the `H`-invariants of the truncated
   smooth Godement sections extended to `ℤ`). It matches Harris's
   `C_m^{•,H} → M_m^{•,H}` only through the identifications recorded in the
   StandardResolution, InvariantTotal and TotalComparison modules, which are
   not formalized here.
2. What is derived. The proof is the standard argument for the total complex
   of a resolution with a contracting homotopy. After forgetting to an
   underlying category the extra degeneracy `σ` contracts each column. With
   the sign `(-1)^q` it assembles into a homotopy of total complexes whose
   row parts cancel by naturality of `σ`. Harris writes none of this. The
   section, the homotopy, the homotopy equivalence, the reflection along a
   faithful exact functor and all system corollaries are derived. Because the
   section is natural only after `F` (for `Ind_1^Γ Res_1^Γ` it is not
   `Γ`-equivariant), the homotopy equivalence lives after `F`, and only the
   quasi-isomorphism is reflected back to `A`.
3. No boundedness is needed for the totalized augmentation itself: the total
   complexes only use the rows `q < N`. The vanishing of `K` in degrees
   `q ≥ N` is needed only to identify the target with `K` extended to `ℤ`
   (TotalComparison module).
4. Freeness. Harris calls the `C_m^{•,H}` complexes of free
   `ℤ/ℓ^mℤ[S(ẽ)/H]`-modules; no freeness or projectivity is proved here.

## Scope

The module proves quasi-isomorphisms level by level. It does not identify the
homology of the total complexes with `ℓ`-divisible systems of homology, and
does not compare total complexes for different `N`. It does not address
freeness, the isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`, the direct limit over
`H`, the equivariance in (2.6), (2.7) or Lemma 2.8.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
