# The residue-field projective-dimension upper bound

This module proves exactly
`Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionUpperBoundStatement.{u}`
as the theorem
`Langlands.CommutativeAlgebra.residueFieldProjectiveDimensionUpperBound`.
Let `R : Type u` be a Noetherian local commutative ring, with `κ` the canonical residue-field
module `ModuleCat.of R (IsLocalRing.ResidueField R)`. If `κ` has finite
categorical, Ext-based projective dimension, then `projectiveDimension κ ≤ ringKrullDim R`
in `WithBot ℕ∞`. This is Stacks Project Lemma 10.110.4,
[Tag 00OB](https://stacks.math.columbia.edu/tag/00OB). The universe is arbitrary, and the
only premise is the finiteness premise of the published statement.

## Proof route

The Stacks proof uses a minimal finite free resolution, the acyclicity criterion and depth.
The Lean proof instead proves the needed direction of the Auslander–Buchsbaum formula using
only long exact `Ext` sequences, and then applies Mathlib's Rees theorem and its
Krull-dimension drop for regular sequences. No Koszul complex, Tor or change of rings is
used. Throughout, "`Ext κ X i` vanishes" means that `Ext κ X i` is a subsingleton.

Auxiliary lemmas (namespace
`Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionUpperBound`):

- `smul_ext_eq_zero`: every `a` in the maximal ideal acts by zero on `Ext κ X i`. Indeed,
  `a • e` is `e` precomposed with `Ext.mk₀ (a • 𝟙 κ)`, and `a • 𝟙 κ = 0`.
- `comp_mk₀_eq_zero_of_range_le`: let `ι : K ⟶ F` be a morphism with `K` projective and the
  range of `ι` inside `𝔪 • ⊤`. Then postcomposition with `Ext.mk₀ ι` is zero on every
  `Ext κ K i`. Choose finitely many generators `a_j` of `𝔪` (Noetherianity) and let
  `σ = ∑ j, a_j • proj_j : (Fin s → F) → F`. Its range contains `𝔪 • ⊤`. Lifting `ι` through
  the range restriction of `σ` (projectivity of `K`) gives `ι = ∑ j, a_j • (proj_j ∘ h)`.
  Each summand acts on `Ext κ (-) i` through some `a_j • (...)`, which vanishes by
  `smul_ext_eq_zero`.
- `subsingleton_ext_of_free`: for a finite free `F`, vanishing of `Ext κ R i` implies vanishing
  of `Ext κ F i`. The identity of `F` is the finite sum, over a chosen basis, of
  coordinate maps `F → R` followed by the corresponding maps `R → F`.
- `subsingleton_ext_self_of_free`: for a nontrivial free `F`, vanishing of `Ext κ F i` implies
  vanishing of `Ext κ R i`, since `R` is a retract of `F` through one basis vector.
- `subsingleton_ext_X₁`: in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, suppose that
  postcomposition with `X₁ → X₂` is zero on `Ext X X₁ i`. Then `Ext X X₁ i` vanishes when
  `i = 0`, by injectivity of that postcomposition for a monomorphism. When `i = j + 1`, it
  vanishes provided `Ext X X₃ j` vanishes, by the covariant long exact sequence.

Main induction, `ext_self_vanish_of_projectiveDimension`. Let `h ≥ 1` and let `M` be a finite
module with `HasProjectiveDimensionLT M (h + 1)` but not `HasProjectiveDimensionLT M h`, that is,
projective dimension exactly `h`. If `Ext κ M i` vanishes for all `i < k`, then
`Ext κ R i` vanishes for all `i < k + h`. The proof is by induction on `h`:

- Case `h = 1`. Take the published minimal finite free cover
  `Langlands.CommutativeAlgebra.minimalFiniteFreeCover R M`, a surjection
  `F = (Fin r →₀ R) → M` whose kernel `K` lies in `𝔪 • ⊤`. Since `M` has projective
  dimension at most one and `F` is projective, `K` is projective. It is also finite, so it
  is free by `Module.free_of_flat_of_isLocalRing`. It is nonzero: otherwise `M ≅ F` would be
  projective. By `comp_mk₀_eq_zero_of_range_le`, the inclusion `K → F` induces zero on all
  `Ext κ (-) i`. Then `subsingleton_ext_X₁` shows that `Ext κ K i` vanishes for `i < k + 1`.
  Finally `subsingleton_ext_self_of_free` transfers this to `R`.
- Step `h → h + 1` (with `h ≥ 1`). Take any finite free presentation `F → M`
  (`Module.exists_finite_presentation`), with kernel `N`. By
  `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`, `N` has projective dimension
  exactly `h`, and `N` is finite since `R` is Noetherian. By strong induction on `i ≤ k`,
  `Ext κ N i` vanishes. The vanishing below `i` and the induction hypothesis for `N` give
  vanishing of `Ext κ R i` (because `i < i + h`), hence of `Ext κ F i`. Then
  `subsingleton_ext_X₁` applies, with the hypothesis on `M` in degree `i - 1`. The induction
  hypothesis for `N` with `k + 1` then gives vanishing of `Ext κ R i` for
  `i < k + 1 + h`.

Final theorem. Let `n` be the least natural number with
`HasProjectiveDimensionLE κ n` (`Nat.find`), so `projectiveDimension κ ≤ n` by
`projectiveDimension_le_iff`. If `n = 0`, the bound follows from
`ringKrullDim_nonneg_of_nontrivial`. Otherwise minimality of `n` says that `κ` does not have
`HasProjectiveDimensionLT κ n`. The main induction with `k = 0` gives vanishing of
`Ext κ R i` for all `i < n`.

The annihilator of `κ` is the maximal ideal `𝔪`, so its support is the zero locus of `𝔪`. Also
`𝔪 • ⊤ = 𝔪 < ⊤` in `R`. Mathlib's Rees theorem,
`ModuleCat.exists_isRegular_of_exists_subsingleton_ext`, therefore yields an `R`-regular
sequence `rs` of length `n`. By `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`,
`ringKrullDim (R ⧸ Ideal.ofList rs) + n = ringKrullDim R`. The quotient is nontrivial
because the regular sequence generates a proper ideal, so its Krull dimension is nonnegative
and `n ≤ ringKrullDim R`.

## Dependencies and independence

The module imports Mathlib, the published statement module, and the published helper
`Langlands.CommutativeAlgebra.MinimalFiniteFreeCover`, which itself imports only Mathlib.
It does not use the residue-field regularity criterion, regular-local localization or finite
projective dimension results, factoriality, or any other statement excluded by the task.
Kernel checking reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Original source

Stacks Project, Lemma 10.110.4, [Tag 00OB](https://stacks.math.columbia.edu/tag/00OB). The
complete page and its comments are retained in registered source
`stacks-residue-field-projective-dimension-bounds-2026-11-01`. The page's comments concern
the reference for finite free resolutions, which this proof route does not use.
