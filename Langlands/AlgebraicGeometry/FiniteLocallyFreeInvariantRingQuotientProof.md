# Invariant ring of a finite locally free equivalence relation

The theorem `Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.invariantRingQuotient`
is the ring calculation used by the proof of Stacks Proposition 39.23.9
(Tag 03BM). For commutative rings `A`, `B`, `C : Type u`, it assumes two maps
`s, t : A →+* B` that make `B` finite projective for each of the two scalar
structures, whose images generate `B`, and whose induced relation on maps to
every commutative ring in universe `u` is an equivalence relation. An injective
map `C → A` identifies `C` with the equalizer of `s` and `t`. The conclusion is
that `A` is finite projective and faithfully flat over `C`, and the square
`C → A ⇉ B` is a pushout of commutative rings. The theorem does not assume a
proof of another Library statement.

## Sources, attribution, and port

The implementation is adapted by Worker 101 from Anthropic, PBC, *Fermat's Last
Theorem in Lean 4*, registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`:

- `P2M/Sol/S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.lean`,
  SHA-256 `b75f5f29f6d67f63688e27b1bb20df2bdeaa5a58cb52943b29fbb0d8890093dd`,
  supplies the implemented proof and its auxiliary declarations.
- `Theorems/Thm_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.lean`,
  SHA-256 `93de7117a262c6511eddf1a9a2d74e55322b80d2bb9609a16fb7244ca4dbf21b`,
  records the original theorem interface.

Copyright 2026 Anthropic, PBC. Adapted under the Apache License, Version 2.0.
The retained license, notice and attribution are
[`LICENSE`](../../licenses/Anthropic-FLT/LICENSE),
[`NOTICE`](../../licenses/Anthropic-FLT/NOTICE), and
[`ATTRIBUTION.md`](../../licenses/Anthropic-FLT/ATTRIBUTION.md).
The registered source directory is
`/home/taskhub/pilot/literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2/`.

The original mathematical source is The Stacks Project Authors, *Groupoid
Schemes*, Section 39.23: the invariant ring in Tag 03BE, characteristic-polynomial
and rank arguments in Tags 03BH–03BJ, flat base change in Tag 03BK, spectrum
surjectivity in Tag 03BL, and the quotient in Tag 03BM. These are available in
registered source `stacks-finite-flat-groupoid-quotient-2026-11-01` and in
`stacks-groupoid-schemes-chapter-pdf-2026-07-14` (PDF SHA-256
`4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`,
Section 39.23, especially pp.46–51). The Stacks route motivates the calculation;
the auxiliary envelope, tensor, and localization interfaces below follow the
registered Lean implementation rather than claiming to be separately numbered
results in Stacks.

This port places all helpers in the namespace
`Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.QuotFLF` and the final
theorem in its parent namespace. It removes `P2M.Util` and its export/reactivate
commands, replacing their uses with ordinary Lean scoped declarations and local
instance/simp attributes. At the two contractions of maximal ideals, it uses
Mathlib's current `Ideal.isMaximal_under_of_isIntegral_of_isMaximal`; an explicit
comap ideal in the rewrite handles the new `Ideal.under` wrapper. The underlying
proof and the quantified universe are preserved. The only import is Mathlib.

## Implemented proof

Write `s` as an algebra map, while a type synonym `Tgt t` carries the scalar
structure given by `t`. The equivalence relation supplies counit, inversion and
composition maps. Joint generation gives uniqueness of ring homomorphisms from
`B`; together these imply the shear isomorphism between the two tensor models
for composable pairs. It identifies the ranks along both projections. When the
invariant ring `C` is local, clopen rank fibers correspond to invariant
idempotents, which must be zero or one. Thus the rank of `B` over `A` is constant.

To construct characteristic polynomials for finite projective modules of
constant rank, the implementation embeds the module as a retract of a finite
free module. Multiplication by an element extends by the identity on the
complement. Its characteristic polynomial has an extra power of `X - 1`;
localization proves this factor divides it and that the quotient is independent
of the chosen retract, commutes with base change and algebra isomorphisms, and
annihilates the original element. The shear isomorphism then proves invariance
of the coefficients of the characteristic polynomial of `t(a)`. Lifting these
coefficients to `C` proves integrality of `C → A`.

Integral spectrum surjectivity and a characteristic-polynomial constant-term
argument show that, over local `C`, there are finitely many maximal ideals of
`A`. After a faithfully flat local extension with infinite residue field, finite
subspace avoidance selects elements `x_i` whose images form bases in all these
fibers. Nakayama's lemma makes `t(x_i)` generate `B` over `A`, and constant rank
makes that generating map bijective. Comparing the two expressions in the
composition tensor product proves the expansion coefficients of elements of
`A` lie in `C`. Consequently `x_i` is a basis of `A` over `C`, and
`A ⊗[C] A → B`, `a ⊗ a' ↦ s(a) * t(a')`, is an isomorphism.

The infinite residue extension is a localization of `C[X]` at the extension of
the maximal ideal. Flat tensoring preserves the equalizer defining invariants,
and all the relation and generation hypotheses pass to base change. Applying
the local argument after localization at every maximal ideal of `C`, faithful
flat descent proves flatness and bijectivity of the tensor map globally. A prime
above each maximal ideal proves faithful flatness of `A`. Finiteness and finite
presentation descend from the identified tensor product; finite presentation
and flatness imply projectivity. The tensor isomorphism gives the asserted
pushout.

## Declaration inventory

In the following tables, names are relative to
`Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.QuotFLF`, except the final
`invariantRingQuotient`. Every entry describes an implemented definition,
instance or proved auxiliary fact from the source port. Section names introduce
hypotheses locally; they are not extra assumptions on the final theorem.
Generated structure constructors and projections have their usual Lean meaning.

### Relations, shear, tensor models and rank

| Declaration | Content and role |
|---|---|
| `Rel` | The relation on `A →+* T` witnessed by a map `B →+* T` through `s` and `t`. |
| `rel_iff` | Unfolds that existential relation. |
| `rel_self` | The identity map of `B` witnesses the pair `(s,t)`. |
| `Rel.map` | Postcomposition transports a related pair to another test ring. |
| `hom_ext` | Maps out of `B` agree when their composites with both generating maps agree. |
| `exists_counit` | Reflexivity gives a common retraction `B → A` of `s` and `t`. |
| `exists_antipode` | Symmetry gives a map `B → B` exchanging `s` and `t`. |
| `exists_comul` | Transitivity gives a composition map into any compatible pair of maps from `B`. |
| `exists_shear` | Symmetry followed by transitivity changes a pair with a common first coordinate into a composable pair. |
| `isPushout_shear` | Uses that construction and joint generation to transform the composable-pair pushout into the common-first-coordinate pushout. |
| `Tgt` | A type synonym for `B` used for the scalar structure given by `t`. |
| `instCommRingTgt` | The commutative ring structure inherited from `B`. |
| `instAlgebraTgt` | The `A`-algebra structure defined by `t`. |
| `Tgt.of` | The identity ring equivalence from `B` to its synonym. |
| `Tgt.algebraMap_eq`, `Tgt.algebraMap_apply` | The ring-hom and pointwise formulas for the algebra map into `Tgt t`. |
| `P₁`, `P₂` | The tensor rings `Tgt t ⊗[A] B` and `B ⊗[A] B`, respectively. |
| `inl₁`, `inr₁` | The left and right ring maps from `B` to `P₁`. |
| `inl₁_apply`, `inr₁_apply` | Their pure-tensor formulas. |
| `isPushout_P₁`, `isPushout_P₂` | The two tensor products satisfy the corresponding commutative-ring pushout properties. |
| `inl₁_comp_t` | Compatibility of the two structure maps into `P₁`. |
| `exists_comul₁` | The composition map specialized to `P₁`. |
| `exists_theta` | Shear gives a ring equivalence `P₂ ≃+* P₁` with the needed formulas on the two factors. |
| `instModuleLeftP₁` | `B` acts on `P₁` through its left factor. |
| `smul_P₁_def` | Expresses this action as multiplication by `inl₁`. |
| `exists_linearEquiv_P₂_P₁` | The shear equivalence is linear for these left `B` actions. |
| `rankAtStalk_P₁_eq` | Computes rank of `P₁` by base change along `t`. |
| `rankAtStalk_comap_algebraMap_eq_rankAtStalk_comap` | Rank of `B` over `A` agrees at the two images of every prime of `B`. |
| `eq_zero_or_eq_one_of_isIdempotentElem` | An invariant idempotent of `A` is zero or one when `C` is local and injects as the invariant ring. |
| `rankAtStalk_eq_rankAtStalk_of_isLocalRing` | Locally constant rank fibers give invariant idempotents, so rank has the same value at all primes of `A`. |
| `exists_rankAtStalk_eq_of_isLocalRing` | Packages that result as a constant natural-number rank; the empty spectrum case uses rank zero. |

### Finite projective characteristic polynomials

The declarations with prefix `L1.` implement the finite free envelope. Later
names in this table are in `QuotFLF` itself.

| Declaration | Content and role |
|---|---|
| `L1.Envelope` | A finite free retract: rank `n`, projection `π`, inclusion `ι`, and equation `πι : π ∘ₗ ι = id`. |
| `L1.nonempty_envelope` | Finite generation supplies the projection and projectivity splits it. |
| `L1.π_ι`, `L1.ι_injective` | The pointwise retract equation and injectivity of the inclusion. |
| `L1.ψ` | Multiplication by `b` on the retract, extended by identity on the complementary kernel. |
| `L1.ψ_apply`, `L1.ψ_ι`, `L1.ψ_pow_ι` | Its pointwise formula, restriction to the retract, and the analogous formula for powers. |
| `L1.aeval_ψ_ι` | Polynomial evaluation in the extended operator restricts to evaluation at `b`. |
| `L1.χ` | The ordinary characteristic polynomial of the finite free extended operator. |
| `L1.χ_monic`, `L1.χ_natDegree` | This polynomial is monic and has degree `n` when the base is nontrivial. |
| `L1.aeval_χ` | Cayley–Hamilton and the injective inclusion show it annihilates `b`. |
| `L1.eF` | The tensor equivalence between the base change of a finite function module and the function module over the new ring. |
| `L1.πb`, `L1.ιb` | Base changes of the projection and inclusion, transported through `eF`. |
| `L1.πb_comp_ιb` | The base-changed projection and inclusion still split. |
| `L1.Envelope.baseChange` | The resulting envelope for the base-changed algebra. |
| `L1.ψ_baseChange` | The extended operator commutes with base change up to `eF`. |
| `L1.χ_baseChange` | Its characteristic polynomial maps to that of the base-changed envelope. |
| `L1.Envelope.mapEquiv` | Transports an envelope through an algebra equivalence. |
| `L1.ψ_mapEquiv`, `L1.χ_mapEquiv` | The extended operator and its characteristic polynomial are unchanged by that transport. |
| `L1.sub_ι_π_mem_ker` | The complementary component of a vector lies in the projection kernel. |
| `L1.toKer`, `L1.coe_toKer`, `L1.toKer_subtype` | The projection to that kernel, its underlying-vector formula, and its identity action on the kernel. |
| `L1.splitEquiv` | The envelope's free module is linearly equivalent to the algebra times the complementary kernel. |
| `L1.finite_ker`, `L1.flat_ker` | The complement is finite and flat as a direct summand of a finite free module. |
| `L1.conj_ψ` | Under the splitting, the extended operator is multiplication on the algebra times identity on the complement. |
| `L1.n_eq_finrank_add` | In the free case, the envelope rank is the sum of the two summand ranks. |
| `L1.χ_eq_mul_of_free` | In the free case, `χ` factors as the multiplication characteristic polynomial times a power of `X - 1`. |
| `L1.free_localization` | The finite projective algebra becomes free at a prime localization. |
| `L1.finrank_localization` | Constant stalk rank `r` computes the localized free rank as `r`. |
| `L1.free_ker_localization` | The complementary kernel also becomes free at that localization. |
| `L1.n_eq_add_finrank_ker_localization` | Its localized rank is `n - r`, expressed as an additive equality. |
| `L1.χ_map_localization` | The localized polynomial factors with the factor `(X - 1)^(n-r)`. |
| `L1.poly_eq_of_localization` | Equality of polynomials is detected at all maximal localizations, coefficient by coefficient. |
| `𝓔₀` | A chosen finite free envelope for a finite projective algebra. |
| `charpoly` | The constant-rank characteristic polynomial: divide `χ` by the monic complementary factor. |
| `monic_X_sub_one_pow`, `map_X_sub_one_pow` | The complementary factor is monic and preserved by a coefficient map. |
| `χ₀_modByMonic` | Localization proves the remainder on division by that factor is zero. |
| `χ₀_eq` | The chosen envelope polynomial equals the complementary factor times `charpoly`. |
| `charpoly_map_localization` | Localization of `charpoly` is the ordinary characteristic polynomial of multiplication on the localized free algebra. |
| `χ_eq_charpoly_mul` | The same factorization works for any envelope, proving independence from the chosen one. |
| `L1_monic`, `L1_natDegree` | `charpoly` is monic, with degree `r` over a nontrivial base. |
| `L1_aeval_self` | It annihilates the original element, by checking Cayley–Hamilton at maximal localizations. |
| `L1_map_baseChange` | It commutes with base change when both constant-rank witnesses have value `r`. |
| `L1_algEquiv` | It is preserved by an algebra equivalence with the same constant-rank value. |
| `L1_eq_linearMap_charpoly` | For a free algebra it equals the ordinary characteristic polynomial of multiplication. |
| `L1_rankAtStalk_baseChange` | Restates stalk-rank compatibility with base change in the required form. |
| `instAlgebraLeftP₁` | The left `B`-algebra structure of `P₁`. |
| `instFiniteLeftP₁`, `instProjectiveLeftP₁` | Finiteness and projectivity of `P₁` over its left factor by tensor base change. |
| `algebraMap_P₁_apply` | The left algebra map into `P₁` is `inl₁`. |
| `charpoly_map_algebraMap_eq_map` | Shear and characteristic-polynomial base change equate the two coefficient maps of the characteristic polynomial of `t(f)`. |
| `coeff_charpoly_invariant` | Every coefficient of that polynomial is invariant under `s` and `t`. |
| `L3_exists_counit` | A convenient repeat of the counit existence interface for the integrality argument. |
| `L3_t_injective`, `L3_s_injective` | Both maps are injective because the counit retracts them. |
| `L3_isIntegral_of_charpoly_invariant` | Monic annihilating polynomials with invariant coefficients lift to `C`, proving `C → A` integral. |
| `L3_isIntegral` | The same integrality interface with an explicit injectivity hypothesis retained for callers. |

### A basis and pushout from a chosen tuple

| Declaration | Content and role |
|---|---|
| `vA`, `vA_apply` | The linear combination map `a ↦ ∑ s(a_i)t(x_i)` and its formula. |
| `vC`, `vC_apply` | The linear combination map `c ↦ ∑ c_i x_i` over the invariant ring and its formula in `A`. |
| `vB` | The analogous combination in `P₁`, with coefficients in its left `B` factor. |
| `vB_injective` | A bijective `vA` gives injectivity of this tensor-base-changed combination map. |
| `vB_comp_t` | Applying `t` to the coefficient tuple gives the right-factor image of `vA`. |
| `vB_comp_s` | Applying `s` to the coefficient tuple gives the composition-map image of `vA`. |
| `t_injective` | The counit gives injectivity of `t` in this proof section. |
| `vC_bijective` | If `t(x_i)` is an `A`-basis of `B`, compare the preceding maps to show `x_i` is a `C`-basis of `A`. |
| `isPushout_of_basis` | The two bases identify the canonical tensor map with `vA`, giving the pushout. |

### Infinite residue extension and base change

| Declaration | Content and role |
|---|---|
| `L8.primeX` | The extension of the maximal ideal of a local ring `R` to `R[X]`. |
| `L8.RX` | Localization of `R[X]` at that prime. |
| `L8.instIsLocalHomRX` | The map from `R` to this localization is a local ring homomorphism. |
| `L8.faithfullyFlat` | That map is faithfully flat, using flatness and locality. |
| `L8.residue_X_pow_injective` | Distinct powers of `X` remain distinct in its residue field. |
| `L8.infinite_residueField` | The residue field is infinite by the preceding injection from the natural numbers. |
| `L8_exists_flat_local_infinite` | Packages the local faithfully flat extension with infinite residue field. |
| `L7.algHomOf`, `L7.algHomOf_apply` | Bundles a compatible ring map as a `C`-algebra map without changing its values. |
| `L7.bc`, `L7.bc_tmul` | Tensor base change of that map and the formula `c ⊗ a ↦ c ⊗ u(a)`. |
| `L7.bc_eq_comp` | Identifies it with ordinary scalar base change followed by the tensor cancellation equivalence. |
| `L7.finite_bc`, `L7.flat_bc`, `L7.finitePresentation_bc` | Transfer finiteness, flatness and finite presentation to that base-changed ring map. |
| `L7.projective_bc` | Transfers projectivity for its induced scalar structure through tensor cancellation. |
| `L7.ringHom_ext_tmul` | Ring maps on a tensor product are determined by pure tensors. |
| `L7.liftPair`, `L7.liftPair_tmul` | Lifts two compatible ring maps from the factors, with their product formula on a pure tensor. |
| `s_comp_algebraMap`, `t_comp_algebraMap` | Both structure maps agree with the scalar map from the invariant ring. |
| `s'` | The scalar base change of the first structure map. |
| `instAlgebraPrimed`, `instIsScalarTowerPrimed` | The algebra structure induced by `s'` and its compatibility with `C'` scalars. |
| `algebraMap_primed_tmul`, `algebraMap_primed_eq_bc` | Its pure-tensor formula and identification with `L7.bc`. |
| `algebraMap_left_apply` | The map from the new scalar ring to the base-changed `A` is `c ↦ c ⊗ 1`. |
| `t'`, `t'_tmul`, `t'_algebraMap` | The base change of the second structure map, its pure-tensor formula and its scalar compatibility. |
| `includeRight_comp_s`, `includeRight_comp_t` | The original two maps commute with the right-factor inclusions. |
| `L7_finite_s`, `L7_flat_s`, `L7_finitePresentation_s` | Finiteness, flatness and finite presentation for the first base-changed projection. |
| `L7_finite_t`, `L7_flat_t`, `L7_finitePresentation_t` | The corresponding properties for the second projection. |
| `L7_moduleFinite`, `L7_moduleFlat`, `L7_moduleProjective` | Module versions of these preservation results for the first scalar structure. |
| `L7_finite_Tgt`, `L7_flat_Tgt`, `L7_projective_Tgt` | Module versions for the second scalar structure using `Tgt`. |
| `L7_hgen` | The ranges of the base-changed maps still generate the target ring. |
| `L7_algebraMap_injective` | Flat scalar base change preserves injectivity of the invariant-ring inclusion. |
| `L7_invariants` | Tensoring the exact equalizer sequence shows invariants commute with flat base change. |
| `one_tmul_algebraMap` | Moves an original scalar across the tensor symbol to the left factor. |
| `rel_primed_iff` | Describes a related pair after base change as an originally related pair with equal scalar components. |
| `L7_hequiv` | Uses that description to preserve reflexivity, symmetry and transitivity under base change. |

### Prime ideals and selection of a local basis

| Declaration | Content and role |
|---|---|
| `L4a_comap_surjective` | An injective integral algebra map induces a surjection on prime spectra. |
| `exists_antipodeAlgEquiv` | Joint generation makes inversion involutive, hence an algebra equivalence between the two scalar structures on `B`. |
| `counitTgt`, `counitTgt_of` | Bundles a retraction of `t` as an algebra map on `Tgt`, with its value formula. |
| `comap_comap_includeRight_eq` | A proper ideal in the fiber ring over a maximal ideal contracts to that maximal ideal in `A`. |
| `isUnit_mulLeft_iff` | Multiplication by an element is an invertible endomorphism exactly when that element is a unit. |
| `coeff_zero_charpoly_notMem_iff` | The characteristic polynomial's constant coefficient avoids a maximal ideal exactly when the element is a unit in that fiber. |
| `L4b_exists_prime_of_comap_eq_of_isMaximal` | Two maximal ideals of `A` contracting equally to `C` are the two contractions of a prime of `B`; prime avoidance, the constant coefficient test and inversion give the proof. |
| `L4c_setOf_isMaximal_finite` | Over local `C`, integrality and the preceding relation reduce the maximal ideals of `A` to the finite fiber of the finite map on spectra. |
| `span_range_t_eq_top` | Joint ring generation implies that the `A`-linear span of the range of `t` is all of `B`. |
| `Fib` | The fiber module `(A ⧸ 𝔪) ⊗[A] B`. |
| `t_algebraMap_eq` | The second structure map agrees with the first on invariant scalars. |
| `Tfib`, `Tfib_apply` | The `C`-linear map `a ↦ 1 ⊗ t(a)` into that fiber and its formula. |
| `span_range_Tfib` | Its range spans the fiber over `A ⧸ 𝔪`. |
| `smul_Tfib_eq_zero` | A scalar from `C` mapping into `𝔪` acts by zero on this image. |
| `finrank_Fib` | At a maximal ideal, the fiber dimension equals the prescribed constant stalk rank. |
| `ofResidue`, `mem_ofResidue` | Reinterprets a submodule as a module over a quotient scalar ring when such an action is given; membership is unchanged. |
| `exists_forall_Tfib_notMem` | Over an infinite residue field, one element simultaneously avoids specified proper fiber subspaces for finitely many maximal ideals above the local maximal ideal. |
| `exists_forall_linearIndependent` | Iterating avoidance selects a tuple with linearly independent images in all the specified fibers. |
| `range_linearCombination_eq_top` | If those images span every maximal fiber, a Jacobson-radical form of Nakayama proves the tuple generates `B`. |
| `bijective_of_surjective_of_rankAtStalk_eq` | A surjection from a free rank-`r` module to a projective module of constant rank `r` has zero kernel, hence is bijective. |
| `L5_exists_basis_of_isLocalRing` | Combines finite maximal spectrum, simultaneous selection, Nakayama and rank to choose `x_i` with bijective `a ↦ ∑ s(a_i)t(x_i)`. |

### Tensor map, local descent and final assembly

| Declaration | Content and role |
|---|---|
| `tAlgHom`, `tAlgHom_apply` | Bundles `t` as a map over `C`, with unchanged values. |
| `theta`, `theta_tmul` | The canonical `A`-algebra map `A ⊗[C] A → B`, with formula `a ⊗ a' ↦ s(a)t(a')`. |
| `isPushout_of_bijective_theta` | A bijective canonical tensor map transports the tensor pushout to the desired ring square. |
| `isLocalizedModule_map_eq_baseChange` | Identifies the localized map with its tensor base change, restricted to the original scalars. |
| `baseChange_baseChange_bijective_iff` | Tensor cancellation equates bijectivity after two scalar extensions with bijectivity after their composite. |
| `bijective_of_forall_exists_faithfullyFlat` | A linear map is bijective if it becomes so on a faithfully flat extension of every maximal localization. |
| `flat_of_forall_exists_faithfullyFlat` | The analogous criterion for module flatness. |
| `thetaLin` | The canonical tensor map viewed as a `C`-linear map for descent. |
| `finite_projective_faithfullyFlat_bijective_of_local` | From local flatness, tensor-map bijectivity and a prime above each maximal ideal, derives global faithful flatness; descends finiteness and finite presentation from `B`, then deduces projectivity. |
| `bijective_baseChange_theta_of_isPushout` | A pushout after scalar extension makes the base-changed canonical tensor map bijective, using tensor associativity and cancellation. |
| `local_world` | For a flat local scalar extension with infinite residue field, obtains constant rank, integrality, a basis, the pushout and a prime over its contracted maximal ideal. |
| `local_package` | Chooses the polynomial localization `L8.RX` after each maximal localization of `C`, supplying the exact witnesses needed for global descent. |
| `invariantRingQuotient` (parent namespace) | Installs the two scalar structures, invokes `local_package` and the global assembly, and converts the resulting tensor isomorphism into the asserted pushout. |

The universe parameter throughout is the arbitrary `u` of the input rings; the
extension rings and tensor products stay in that universe. The helper's checked
theorem uses only `propext`, `Classical.choice` and `Quot.sound`. Compilation is
development evidence; the exact scheme statement is proved in the paired entry
module and remains subject to independent review and formal validation.
