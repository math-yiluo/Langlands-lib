# Generic flatness over a noetherian domain

Author: Worker 866.

This helper module proves generic flatness. Let `A` be a noetherian domain,
`B` a finite type `A`-algebra and `M` a finite `B`-module. Then some nonzero
`a : A` makes `M[1/b]` flat over `A` for every multiple `b` of `a`. The
openness of the flat locus (module `Langlands.Algebra.NoetherianFlatLocusOpen`)
uses this result. All declarations live in
`Langlands.Algebra.GenericFlatness`, and the module adds no axioms.

## Provenance

- Stacks Project, Algebra, Lemma 10.118.1 (Tag 051R), *generic flatness*:
  for `R` a noetherian domain, `R → S` of finite type and `M` a finite
  `S`-module, some nonzero `f ∈ R` makes `M_f` free over `R_f`. Here only the
  weaker conclusion is proved: `M_f` is flat over `R`. Flatness is also
  stated for every multiple of `f`, a strengthening the later steps need.
- The Lean proof does not follow the Stacks proof, which inducts on
  `dim (K ⊗_R S)` via Noether normalization. It inducts on the number of
  polynomial variables instead, using the filtration
  `N ⊆ N + XN ⊆ N + XN + X²N ⊆ ⋯` described below. Flatness, unlike
  freeness, passes to directed unions, so this filtration can be infinite.
  The base case is Mathlib's generic freeness of finitely presented modules
  at a single localization
  (`Module.FinitePresentation.exists_free_localizedModule_powers`).

## Declarations and Lean proofs

### General flatness lemmas

`lift_lsmul_lTensor`: the multiplication maps `I ⊗[A] M → M` are natural in
`M`. This is proved by induction on tensors.

`flat_of_exact`: in a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of
`A`-modules with `M₁` and `M₃` flat, `M₂` is flat. The proof uses Mathlib's
criterion `Module.Flat.iff_lift_lsmul_comp_subtype_injective`: `M` is flat
when `I ⊗ M → M` is injective for every finitely generated ideal `I`. It then
chases the diagram formed by the right exact sequence
`I ⊗ M₁ → I ⊗ M₂ → I ⊗ M₃ → 0` (`lTensor_exact`) over `M₁ → M₂ → M₃`.

`flat_of_directed`: a module that is the union of a directed family of flat
submodules is flat. Every element of `I ⊗ M` comes from `I ⊗ Nᵢ` for a single
member `Nᵢ` of the family, by induction on tensors and directedness. The same
ideal criterion then applies in `Nᵢ`.

`flat_localizedModule`, `flat_localizedModule_iff`,
`flat_localizedModule_of_le`, `flat_localizedModule_of_equiv`: four
transfer facts about `LocalizedModule S M` as an `A`-module. A localization
of a flat module is flat. Flatness only depends on the localization up to
isomorphism. Flatness of `M_S` gives flatness of `M_T` for `S ≤ T`. Linear
equivalences `M₁ ≃ M₂` transfer flatness of localizations. The proofs use
`Module.Flat.trans` through `Localization S` and `IsLocalizedModule.iso`.

`flat_localizedModule_of_exact`: `flat_of_exact` after localization, using
Mathlib's exactness of `LocalizedModule.map` (`LocalizedModule.map_exact`).

`GenFlat A M` (definition): there is a nonzero `a : A` such that
`LocalizedModule (Submonoid.powers b) M` is flat over `A` for every `b`
divisible by `a`.

`flat_localizedModule_powers_of_dvd`: if `a ∣ b` and `M[1/a]` is flat over
`A`, then so is `M[1/b]`. The proof localizes at the saturation
`T = {x | ∃ n, x ∣ bⁿ}`, which contains the powers of `a`. Then
`flat_localizedModule_of_le` applies, and localizing at `T` is the same as
localizing at the powers of `b` (`IsLocalizedModule.of_exists_mul_mem`).

`GenFlat.of_equiv`, `GenFlat.of_exact`: `GenFlat` is invariant under linear
equivalence and stable under extensions in a domain. For an extension, the
product `a₁ a₃` of the two witnesses is nonzero and works.

`GenFlat.of_finite`: every finite module `M` over a noetherian domain `A` is
generically flat. `M` is finitely presented, and `M ⊗ Frac A` is free over
the field `Frac A`. Mathlib's
`Module.FinitePresentation.exists_free_localizedModule_powers` then gives a
nonzero `r` with `M[1/r]` free, hence flat, over `A[1/r]`, so flat over `A`.
Multiples of `r` are handled by `flat_localizedModule_powers_of_dvd`.

### The filtration

Let `R` be a ring, `M` an `R`-module, `τ` an `R`-linear endomorphism of `M`
and `N ⊆ M` a submodule.

`filt τ N k` (definition) is `N + τ N + ⋯ + τᵏ N`, defined by recursion.
`filt_zero`, `filt_succ`, `filt_mono`, `map_filt_le` and `apply_mem_filt` are
its basic properties: it increases with `k`, and `τ` maps `filt k` into
`filt (k+1)`.

`L τ N k` (definition) is the submodule of `N` of those `x` with
`τ^(k+1) x ∈ filt k`. `L_mono`: these submodules increase with `k`, because
`τ` maps `filt k` into `filt (k+1)`.

`succMap`, `succMap_surjective`, `ker_succMap`, `quotEquiv`: the map
`N → filt (k+1) / filt k`, `x ↦ [τ^(k+1) x]`, is surjective with kernel
`L k`. This gives the isomorphism `N / L k ≃ filt (k+1) / filt k`.

`exact_inclusion_mkQ`: for `p ≤ q`, the sequence `p → q → q / p` is exact.

`flat_localizedModule_of_le_quot`, `genFlat_of_le_quot`: for `R`-submodules
`p ≤ q` of an `R`-module that is also an `A`-module through `A → R`, flatness
of the localizations of `p` and `q / p` gives flatness of the localization of
`q`. Likewise, `GenFlat` of `p` and `q / p` gives `GenFlat` of `q`.

### The induction

`GF A R` (definition): every finite `R`-module, with compatible `A`-module
structure, is generically flat over `A`.

`genFlat_of_filt`: assume `A` is a domain, `R` is noetherian and `GF A R`
holds. Let `M` be the union of the submodules `filt τ N k`, with `N` a finite
`R`-module. Then `GenFlat A M`. The proof runs as follows:

1. Each `filt k` is generically flat, by induction on `k`: its successive
   quotients `N / L k` are finite `R`-modules, and extensions preserve
   `GenFlat`.
2. Since `N` is noetherian, the chain `L k` stabilizes at some `k₀`
   (`monotone_stabilizes_iff_noetherian`).
3. Take `a₀` a witness for `filt k₀` and `a₁` a witness for `N / L k₀`. For
   every multiple `b` of `a₀ a₁`, induction on `j` shows that the
   localization of `filt (k₀ + j)` at `b` is flat. All later successive
   quotients are isomorphic to `N / L k₀`.
4. `M[1/b]` is the directed union of the localized submodules
   `filt (k₀ + j)[1/b]` (`Submodule.localized₀`), so it is flat by
   `flat_of_directed`.

`gf_polynomial`: `GF A R` implies `GF A R[X]` for `A` a domain and `R`
noetherian. View a finite `R[X]`-module `M` as an `R`-module through `C`, let
`τ` be multiplication by `X`, and let `N` be the `R`-span of a finite set of
`R[X]`-generators. The union of the `filt τ N k` is an `R[X]`-submodule
(polynomial induction) that contains the generators, so it is all of `M`.
Then `genFlat_of_filt` applies.

`gf_of_surjective`: `GF A R` implies `GF A D` for a surjective `A`-algebra
map `R → D`. A finite `D`-module is a finite `R`-module by restriction of
scalars.

`gf_of_finite`: if `R` is a finite `A`-module, then `GF A R` holds, by
`GenFlat.of_finite`.

`gf_mvPolynomial`: `GF A (MvPolynomial (Fin n) A)` holds for every `n`, by
induction on `n`. The case `n = 0` is `gf_of_finite`. The inductive step
combines `gf_polynomial` with `MvPolynomial.finSuccEquiv`, which identifies
`MvPolynomial (Fin (n+1)) A` with `(MvPolynomial (Fin n) A)[X]`.

`genFlat_of_finiteType` (generic flatness): for `A` a noetherian domain, `B`
a finite type `A`-algebra and `M` a finite `B`-module, `GenFlat A M` holds.
`B` is a quotient of some `MvPolynomial (Fin n) A`
(`Algebra.FiniteType.iff_quotient_mvPolynomial''`), so `gf_mvPolynomial` and
`gf_of_surjective` apply.
