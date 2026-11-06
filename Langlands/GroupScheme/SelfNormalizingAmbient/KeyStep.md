# Stabilizers of the infinitesimal neighbourhoods of a smooth subgroup

This module proves the key step for the ambient map of a self-normalizing subgroup. Let `H` be
a subgroup family cut out by an ideal `J` with `B ⧸ J` smooth and flat with domain fibres. A
point that stabilizes every infinitesimal neighbourhood of the unit in `H` normalizes `H`. If `H`
is self-normalizing and the jet quotients are projective, a single neighbourhood already has
stabilizer exactly `H`. All rings live in one universe `u`.

## Setting

`R` is a commutative ring, `F` is a functor from commutative `R`-algebras to groups, and
`e : (F ⋙ forget GrpCat).CorepresentableBy B` says that the `R`-algebra `B` corepresents the
underlying set functor of `F`. `H A ⊆ F A` is a family of subgroups cut out by an ideal `J` of
`B` (`hH : IsCutOutBy e H J`): `x ∈ H A` exactly when the classifying map
`e.homEquiv.symm x : B ⟶ A` kills `J`.

Notation from the Library and from the module
`Langlands.GroupScheme.SelfNormalizingAmbient.Stabilizer`:

- `cutFunctor hH` is the group functor `A ↦ H A`, corepresented by `B ⧸ J` via
  `cutCorepresentableBy hH`.
- `tensorQuotient J S` is the `R`-algebra `S ⊗[R] (B ⧸ J)`, `tensorQuotientLeft J S` its
  inclusion of `S`, and `universalCutPoint e J S` the point of `F (S ⊗[R] (B ⧸ J))` classified by
  `b ↦ 1 ⊗ₜ [b]`. It is the universal point of `H` over `S`.
- `augIdeal e` is the augmentation ideal of `B` (the kernel of the counit).
  `jetIdeal e J n = J ⊔ augIdeal e ^ (n + 1)` cuts out the `n`-th infinitesimal neighbourhood of
  the unit in `H`.
- `Stabilizes e K g`: after every algebra map, conjugation by `g` and by `g⁻¹` preserves the points
  whose classifying map kills `K`. By `stabilizes_iff`, when `B ⧸ K` is projective, the points
  `e.homEquiv φ` stabilizing `K` are those with `φ` killing the Library ideal
  `subgroupNormalizerIdeal e K`.
- `tensorPairMap`, `eq_bot_of_mul_closed` come from `Langlands.GroupScheme.SelfNormalizingAmbient.HopfIdeal`,
  and `exists_one_sub_mul_eq_zero_of_mem_pow` from `Langlands.GroupScheme.SelfNormalizingAmbient.Krull`.

## Auxiliary results

- `flat_quotient_ker_pow`: for a smooth `A`-algebra `C` with an `A`-algebra section `ε`, every
  quotient `C ⧸ (ker ε) ^ (n + 1)` is flat over `A`. It follows from the projectivity in
  `Algebra.Smooth.finite_projective_quotient_ker_pow` (module `Langlands.RingTheory.Smooth.SectionJets`).
- `exists_one_sub_mul_eq_zero_of_fg`: let `L` be a finitely generated ideal and `I` an ideal. If
  each `l ∈ L` satisfies `(1 - j) * l = 0` for some `j ∈ I`, then one `j ∈ I` works for all of
  `L`. Proof: induction over a finite generating set, using
  `1 - (j₁ + j₂ - j₁ j₂) = (1 - j₁)(1 - j₂)`, then span induction.
- `Stabilizes.inv`: if `g` stabilizes `K`, so does `g⁻¹`.
- `cutCorepresentableBy_homEquiv_symm_mk`: the classifying map `B ⧸ J ⟶ T` of a point `x` of `H T`
  sends `[b]` to the classifying map of `x` (as a point of `F T`) applied to `b`.
- `tensorQuotientLeft_comp_tensorPairMap`: `tensorQuotientLeft J S ≫ tensorPairMap s x = s`, where `tensorPairMap`
  is taken for `cutCorepresentableBy hH`.
- `map_tensorPairMap_universalCutPoint`: `F.map (tensorPairMap s x)` sends the universal cut point to `x`.
- `map_tensorPairMap_conj`: with `g' = F.map (tensorQuotientLeft J S) g`, `F.map (tensorPairMap s x)` sends
  `g' u g'⁻¹` (`u` the universal cut point) to `F.map s g * x * (F.map s g)⁻¹`.
- `tensorPairMap_kills_iff`: `tensorPairMap s x` kills the ideal `J (g' u g'⁻¹)` of `S ⊗[R] (B ⧸ J)` generated
  by the image of `J` under the classifying map of `g' u g'⁻¹` exactly when
  `F.map s g * x * (F.map s g)⁻¹ ∈ H T`.
- `cutCounit hH S : S ⊗[R] (B ⧸ J) →ₐ[S] S` is the `S`-algebra map `tensorPairMap (𝟙 S) 1`
  (identity on `S`, counit of `B ⧸ J`), with `cutCounit_apply`.
- `classify_universalCutPoint_mem_ker`: the classifying map of the universal cut point sends the
  augmentation ideal of `B` into `ker (cutCounit hH S)`.
- `classify_conj_mem_pow`: if `g` stabilizes `jetIdeal e J n`, then the classifying map of
  `g' u g'⁻¹` sends `J` into `ker (cutCounit hH S) ^ (n + 1)`. Proof: modulo
  `N = ker (cutCounit hH S) ^ (n + 1)`, the universal cut point kills `J` and, by
  `classify_universalCutPoint_mem_ker`, the `(n + 1)`-st power of the augmentation ideal. So it
  kills `jetIdeal e J n`. The stabilizer condition, applied along `S ⟶ S ⊗[R] (B ⧸ J) ⟶ (S ⊗[R]
  (B ⧸ J)) ⧸ N`, shows that the image of `g' u g'⁻¹` kills `jetIdeal e J n ⊇ J`.

## Main results

Assume `B ⧸ J` is flat and smooth over `R` (instance arguments), `K ⊗[R] (B ⧸ J)` is an integral
domain for every field `K` that is an `R`-algebra (`hdom`), and `J` is finitely generated (`hJ`).

- **`conj_mem_of_stabilizes`**: if `g : F S` stabilizes `jetIdeal e J n` for every `n`, then
  `g' u g'⁻¹ ∈ H (S ⊗[R] (B ⧸ J))`. Proof: let `L` be the ideal `J (g' u g'⁻¹)` of
  `S ⊗[R] (B ⧸ J)`, which is finitely generated since `J` is. `S ⊗[R] (B ⧸ J)` is smooth over
  `S` with the `S`-algebra section `cutCounit hH S`. By `classify_conj_mem_pow`, every element of
  `L` lies in every power of `ker (cutCounit hH S)`. The Krull step
  `exists_one_sub_mul_eq_zero_of_mem_pow` (with flatness from `flat_quotient_ker_pow`) and
  `exists_one_sub_mul_eq_zero_of_fg` give one `j ∈ ker (cutCounit hH S)` with `(1 - j) * l = 0`
  for all `l ∈ L`. Then `f = 1 - j` has value `1` at the unit. The points `tensorPairMap s x` killing
  `L` are closed under multiplication, by `tensorPairMap_kills_iff` and because conjugation by
  `F.map s g` is a homomorphism. So `eq_bot_of_mul_closed` (for the functor `cutFunctor hH`,
  flat with domain fibres) gives `L = ⊥`, which says that `g' u g'⁻¹` lies in `H`.
- **`mem_normalizerFamily_of_stabilizes`**: under the same hypotheses, `g` lies in the Library
  normalizer family `normalizerFamily H S`. Proof: the Library criterion
  `mem_normalizerFamily_iff` tests the universal cut point. Apply `conj_mem_of_stabilizes` to `g`
  and to `g⁻¹` (`Stabilizes.inv`).

Now assume in addition that every jet quotient `B ⧸ jetIdeal e J n` is projective over `R`, and
that `H` is self-normalizing: `normalizerFamily H A ≤ H A` for every `A` (`hself`).

- `le_iSup_subgroupNormalizerIdeal_jetIdeal`: `J ≤ ⨆ n, subgroupNormalizerIdeal e (jetIdeal e J n)`.
  Proof: let `a` be the supremum and `γ = e.homEquiv (quotientMap a)` the point of `F (B ⧸ a)`
  classified by the quotient map. By `stabilizes_iff`, `γ` stabilizes every `jetIdeal e J n`.
  By `mem_normalizerFamily_of_stabilizes` and `hself`, `γ ∈ H (B ⧸ a)`, so the quotient map kills
  `J`.
- **`exists_stabilizes_jetIdeal_iff`**: there is `N` such that for every `R`-algebra `A` and every
  `x : F A`, `x` stabilizes `jetIdeal e J N` exactly when `x ∈ H A`. Proof: the ideals
  `a n = subgroupNormalizerIdeal e (jetIdeal e J n)` increase with `n`
  (`subgroupNormalizerIdeal_jetIdeal_mono` from the Stabilizer module). `J` is finitely generated,
  hence a compact element of the lattice of ideals (Mathlib `Submodule.fg_iff_compact`), and lies
  below the directed supremum of the `a n`. So `J ≤ a N` for some `N`. Since `a N ≤ J`
  (`subgroupNormalizerIdeal_jetIdeal_le`), `a N = J`, and `stabilizes_iff` together with `hH`
  gives the equivalence.

## Provenance

Internal helper results for the proof of
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`. They formalize the step in Conrad,
*Reductive group schemes* (2014), proof of Theorem 2.3.6(1), printed p. 74. There the normalizer
`N_G(H)` is described as the intersection of the normalizers of the infinitesimal neighbourhoods
`H_n` of the unit in `H`. This intersection stabilizes for large `n` because `G` is Noetherian,
so `N_G(H_n) = N_G(H) = H` for some `n`. The proofs here differ:

- They work over an arbitrary commutative ring. The inclusion of the intersection in `N_G(H)`
  (`mem_normalizerFamily_of_stabilizes`) uses the Krull step of module `Krull` and the vanishing
  criterion of module `HopfIdeal`.
- The stabilization index comes from finite generation of `J`, not from Noetherianity.
