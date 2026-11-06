# Jacquet lifts from stationary compression ranges

Worker 1587 developed the stationary-range cancellation argument. The averaging argument in `exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction` reuses Worker 834's published proof in `IwahoriContractionAdmissibility`, with its finiteness-free part extracted as a separate theorem.

This module works with an arbitrary topological group `G : Type uG`, an independently sized complex module `V : Type uV`, a smooth representation `ρ`, a compact open subgroup `K`, actual subgroups `N`, `M`, `Nbar`, and an element `g` satisfying `IsIwahoriContraction K N M Nbar g`. The Levi normalizer condition `hMN : M ≤ Subgroup.normalizer N` is explicit. There is no admissibility or finite-dimensionality hypothesis.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.9.1, printed pp.195–197 / PDF pp.201–203, specifically (VI.9.1.1), (VI.9.1.3) and the deduction of the generalized Jacquet lemma from the stabilization Proposition. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Write `C` for `compressedAction ρ hρ K hK g`, `j` for the actual coinvariant quotient restricted to `K`-fixed vectors, and `B` for the action on coinvariants of the element `g` viewed in `M`.

`mk_compressedAction_pow_of_iwahoriContraction` proves `j(C^r x) = B^r j(x)` by induction from the published one-step identity. This uses the Iwahori factorization and the stated contraction containments through that identity.

`exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction` proves that for every `K ∩ M`-fixed Jacquet vector `y`, there are `s ≥ 0` and a `K`-fixed vector `x` such that `j(x) = B^s y`. Choose any lift `v` of `y`. Smoothness and opposite contraction make `ρ(g^s)v` fixed by `K ∩ Nbar` for a suitable exponent. The Levi conjugation containment and the fixedness of `y` identify its quotient after each `K ∩ M` translate. Factorization applied to the inverse of a `K` element, and the fact that `N` acts trivially on coinvariants, then show that every `K` translate has the same quotient. Normalized compact averaging produces `x`. This is the finiteness-free averaging argument already used by the published admissible Jacquet proof.

`fixedJacquetMap_surjective_of_stationaryRanges` assumes an exponent `b` such that `range C^r = range C^b` for all `r ≥ b`. Given `j(x) = B^s y`, stationarity gives a vector `w` with `C^(b+s)w = C^b x`. Applying the quotient and the power-intertwining identity gives

`B^(b+s) j(w) = B^b j(x) = B^(b+s)y`.

The representation action of a group element is invertible, so cancellation proves `j(w) = y`. This establishes surjectivity of the actual `fixedJacquetMap`.

The stationary-range cancellation is a derived proof route that avoids constructing the localization or using kernel stationarity and complementarity. The range stationarity remains a visible premise of this helper; this module does not prove the geometric uniform stabilization Proposition or the exact unconditional dynamic-parabolic generalized Jacquet target. Those require the separate stabilization theorem. The abstract helper does not use reductivity, the field, or centrality of `g`; those belong to the geometric proof of stationarity.

`stableImageJacquetMap_bijective_of_stationaryRanges` adds the published predicate `CompactCompressionSplits`, which says that `powerKernelSup` and `stableImage` are complementary. The published equality `powerKernelSup_eq_ker_of_iwahoriContraction` then proves injectivity of the quotient on the stable image. To prove surjectivity of that restriction, first use the stationary-range theorem to lift `y` to a `K`-fixed `x`, decompose `x` into its kernel-supremum and stable-image components, and discard the first component under the quotient.

The construction `stationaryRangeJacquetEquiv` packages this bijective, actual restricted quotient as a complex linear equivalence. Its forward map is exactly `stableImageJacquetMap`, as recorded by `stationaryRangeJacquetEquiv_apply`; its inverse is the unique lift in the stable image. This is the conditional canonical-section construction in the deduction on Renard PDF p.203. All premises remain explicit. It is a derived construction, rather than a proof that those premises hold for geometric parabolics.
