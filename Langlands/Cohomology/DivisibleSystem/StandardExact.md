# Exactness of the standard resolution

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.StandardResolution`
(the iterates `standardPow P n`, the differentials `standardDifferential P ε n`,
the resolution functor `standardResolution P ε`, its augmentation
`standardResolutionAugmentation P ε`, the systems of resolutions and the
group case `indResBot`, `indResBotCounit`) and on Mathlib. Names are in the
namespace `Langlands.Cohomology`, the `StandardContraction` names in
`Langlands.Cohomology.StandardContraction` and the system corollaries in
`Langlands.Cohomology.DivisibleSystem`.

On p.306 Harris calls (2.5) `⋯ K_m^{-r,q,H} → ⋯ → K_m^{-1,q,H} → M_m^{q,H} → 0`
"the canonical free resolution of `M_m^{q,H}` obtained via (2.4)". The
StandardResolution module builds this complex in bar form but does not prove
that it is a resolution. This module proves exactness: the augmentation from
the standard resolution to the object in degree `0` is a quasi-isomorphism
whenever `F ε` has a natural section for some faithful exact functor `F`. It
constructs such a section for `Ind_1^Γ Res_1^Γ` after forgetting the action
of `Γ`, and it records the consequences for `ℓ`-divisible systems, level by
level and column by column. Freeness is not addressed.

Notation: `P^n` is `standardPow P n`, `d_n : P^(n+1) ⟶ P^n` is
`standardDifferential P ε n`, so `d_0 = ε` and
`d_{n+1} X = ε (P^(n+1) X) - P (d_n X)`. The standard resolution of `X` has
`P^(r+1) X` in degree `r` and differential `d_{r+1} X` from degree `r + 1` to
degree `r`; the augmentation is `ε X = d_0 X` in degree `0`. Composition
`f ≫ g` is `f` followed by `g`.

## Short complexes with a contraction

- `shortComplex_exact_of_contraction`: in a preadditive category, a short
  complex `S : X₁ ⟶ X₂ ⟶ X₃` with homology is exact if there are
  `h₁ : X₂ ⟶ X₁` and `h₂ : X₃ ⟶ X₂` with `h₁ ≫ f + g ≫ h₂ = 𝟙 X₂`. The proof
  first derives `f ≫ h₁ ≫ f = f` and `g ≫ h₂ ≫ g = g` (from the identity and
  `f ≫ g = 0`). These make `h₀ = 𝟙 - f ≫ h₁` and `h₃ = 𝟙 - h₂ ≫ g` satisfy
  the side conditions of a Mathlib `ShortComplex.Homotopy` from `𝟙 S` to
  `0` with middle components `h₁`, `h₂`. Homotopic maps induce the same
  map on homology (`homologyMap_congr`), so the identity of the homology is
  zero and the homology is zero.
- `shortComplex_exact_of_map_contraction`: in an abelian category, `S` is
  exact if, after an additive faithful functor `F` to an abelian category that
  preserves finite limits and finite colimits, there are such `h₁`, `h₂` for
  `F.map S.f`, `F.map S.g`. These two maps may be supplied as morphisms `f'`,
  `g'` with proofs `F.map S.f = f'`, `F.map S.g = g'`, because the
  differentials of the standard resolution are equal, but not syntactically
  equal, to the `d_n`. The proof applies the previous lemma to `S.map F` and
  Mathlib's `ShortComplex.exact_map_iff_of_faithful`.

## Natural contractions

`A`, `B` are abelian categories, `F : A ⥤ B`, `P : A ⥤ A` and
`ε : P ⟶ 𝟭 A`.

- `StandardContraction F P ε` is a structure with a natural transformation
  `σ : F ⟶ P ⋙ F` (components `σ X : F X ⟶ F (P X)`) and the field
  `σ_comp X : σ X ≫ F (ε X) = 𝟙 (F X)`. It is a natural section of `F ε`. It
  is natural for morphisms of `A`, but its components are morphisms of `B`,
  not of `A`.

For `c : StandardContraction F P ε` and additive `F`:

- `c.app n X : F (P^n X) ⟶ F (P^(n+1) X)` is `σ` at `P^n X`, typed with the
  iterates of `P`.
- `c.identity n X`: `c.app (n+1) X ≫ F (d_{n+1} X) = 𝟙 - F (d_n X) ≫ c.app n X`
  on `F (P^(n+1) X)`. Expanding `d_{n+1}`, the term
  `σ ≫ F (ε (P^(n+1) X))` is `𝟙` by `σ_comp`, and the term
  `σ ≫ F (P (d_n X))` is `F (d_n X) ≫ σ` by naturality of `σ` at `d_n X`.
  `F` distributes over the difference because it is additive.
- `c.identity' n X` is the same identity in the form
  `c.app (n+1) X ≫ F (d_{n+1} X) + F (d_n X) ≫ c.app n X = 𝟙`. So after `F`,
  the maps `c.app n X` form a contracting homotopy of the augmented complex
  `⋯ → F (P^2 X) → F (P X) → F X → 0`.
- `c.epi_ε X`: for faithful `F`, `ε X` is an epimorphism. `F (ε X)` has the
  section `σ X`, hence is an epimorphism, and a faithful functor reflects
  epimorphisms (Mathlib's `Functor.epi_of_epi_map`). This needs neither
  additivity nor abelian categories.

From here on `P` preserves zero morphisms (needed for the standard
resolution to be a complex) and `F` is additive, faithful and preserves finite
limits and finite colimits.

- `c.exactAt_succ X n`: the standard resolution of `X` is exact in degree
  `n + 1`. Its short complex there is
  `P^(n+3) X ⟶ P^(n+2) X ⟶ P^(n+1) X` with maps `d_{n+2} X`, `d_{n+1} X`
  (Mathlib's `exactAt_iff'` and the StandardResolution module's
  `standardResolution_obj_d`), and `c.identity' (n+1) X` is the contraction
  identity for it after `F`.
- `augmentation_app_f_zero X`: the degree `0` component of the augmentation
  at `X` is `ε X` (Mathlib's `ChainComplex.toSingle₀Equiv_symm_apply_f_zero`).
- `c.quasiIso_augmentation X`: the augmentation
  `(standardResolutionAugmentation P ε).app X` from the standard resolution of
  `X` to `X` placed in degree `0` is a quasi-isomorphism. In degree `0`,
  Mathlib's `ChainComplex.quasiIsoAt₀_iff` and
  `ShortComplex.quasiIso_iff_of_zeros'` reduce this to two facts: the
  sequence `P^2 X ⟶ P X ⟶ X` with maps `d_1 X`, `ε X` is exact
  (`c.identity' 0 X`), and `ε X` is an epimorphism (`c.epi_ε X`). In degree
  `n + 1` the target `X` in degree `0` is exact (Mathlib's
  `ChainComplex.exactAt_succ_single_obj`). There Mathlib's
  `quasiIsoAt_iff_exactAt'` reduces the claim to `c.exactAt_succ X n`.

Thus `⋯ → P^2 X → P X → X → 0` is exact.

## ℓ-divisible systems

Now `P` is additive and preserves finite limits and finite colimits (as the
systems of the StandardResolution module require), `F` is as above, and
`c : StandardContraction F P ε`.

- `quasiIso_standardResolutionSystemAugmentation c T m`: for
  `T : DivisibleSystem A ℓ`, the level `m` component of
  `T.standardResolutionSystemAugmentation P ε` is a quasi-isomorphism. It is
  the augmentation at the member `T.obj m`.
- `quasiIso_standardResolutionDoubleComplexesAugmentation c K m q`: for
  `K : DivisibleSystem (CochainComplex A ℕ) ℓ`, the column `q` of the level
  `m` component of `K.standardResolutionDoubleComplexesAugmentation P ε` is a
  quasi-isomorphism. It is the augmentation at the degree `q` term of
  `K.obj m`. For `K m = M_m^{•,H}` this is the exactness of Harris's (2.5) for
  each `m` and `q`.

These are statements per level and per column. That the totalized
augmentation of the Total module is a quasi-isomorphism is not proved here.

## The group case

`k` is a commutative ring, `Γ` a group, and representations are Mathlib's
`Rep.{max w u v} k Γ`.

- `indResBotContraction k Γ : StandardContraction (forget₂ (Rep k Γ)
  (ModuleCat k)) (indResBot k Γ) (indResBotCounit k Γ)`. Its component at `V`
  is the `k`-linear map `v ↦ ⟦1 ⊗ v⟧` from `V` to
  `Ind_1^Γ Res_1^Γ V = (k[Γ] ⊗_k V)_⊥`, Mathlib's
  `Representation.IndV.mk ⊥.subtype _ 1`. Naturality in `V` holds by `rfl`.
  The field `σ_comp` says that the counit sends `⟦1 ⊗ v⟧` to `v`. The counit
  is `(Rep.indResHomEquiv ..).symm (𝟙 _)` (Mathlib's `Adjunction.homEquiv_counit`
  for `Rep.indResAdjunction`, which is built from `Rep.indResHomEquiv`). The
  forward map of `Rep.indResHomEquiv` precomposes with `IndV.mk _ _ 1`.
  Hence evaluating `indResHomEquiv (indResHomEquiv.symm 𝟙) = 𝟙` at `v` gives
  the claim. The section is not `Γ`-equivariant in general: `h ∈ Γ` sends
  `⟦1 ⊗ v⟧` to `⟦h⁻¹ ⊗ v⟧` (StandardResolution module, item 1), not to
  `⟦1 ⊗ h v⟧`. It is a natural section only after forgetting to `k`-modules.
  No finiteness of `Γ` is needed. Mathlib's `forget₂ (Rep k Γ) (ModuleCat k)`
  is additive, faithful and exact.
- With `[Finite Γ]` (needed for the systems, as in the StandardResolution
  module), `quasiIso_groupStandardResolutionSystemAugmentation T m` and
  `quasiIso_groupStandardResolutionDoubleComplexesAugmentation K m q` are the
  two system corollaries for `P = indResBot k Γ`,
  `ε = indResBotCounit k Γ` and `c = indResBotContraction k Γ`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. Worker 61
read (2.4), (2.5) and the sentence "be the canonical free resolution of
`M_m^{q,H}` obtained via (2.4)" in the scanned original.

1. What is from the source. Harris states that (2.5) is a resolution of
   `M_m^{q,H}`, that is, exact with augmentation onto `M_m^{q,H}`. He does
   not prove it. The quasi-isomorphisms of the group case are this exactness,
   for each level `m` and each degree `q`, for the bar form of (2.5) built in
   the StandardResolution module. It matches Harris's (2.5) for `k = ℤ_ℓ` and
   `Γ = S(ẽ)/H` only through the identifications of that module's item 1,
   which are not formalized.
2. What is derived. The proof is the standard one for bar resolutions: the
   extra degeneracy `v ↦ ⟦1 ⊗ v⟧` is a contracting homotopy of the underlying
   `k`-modules. Harris does not write it. The abstraction to a natural section
   of `F ε` for a faithful exact `F`, the short-complex lemmas and the system
   corollaries are derived. Exactness is checked after `F` and reflected back
   by faithfulness. This is why the section only needs to be natural, and
   need not be equivariant.
3. Freeness. Harris calls (2.5) a free resolution; this module proves only
   exactness. Freeness of the terms (StandardResolution module, item 5) is not
   addressed.
4. Indexing. Resolution degree `r` here is Harris's degree `-(r+1)`, and
   `M_m^{q,H}` is in degree `0` of the augmented complex (StandardResolution
   module, item 6).

## Scope

The module does not prove that the totalized augmentation of the Total
module, or its comparison with `K` in the TotalComparison module, is a
quasi-isomorphism. That would need a comparison of the homology of a total
complex with the homology of its columns, which is not formalized. It proves
no freeness or projectivity. It
does not address the isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`, the direct
limit over `H`, (2.6), (2.7) or Lemma 2.8.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
