# Galois upper groups through the transitivity index

`Langlands.Ramification.Kummer.truncationGaloisComap` proves
`TruncationGaloisComapStatement.{u}` at an arbitrary universe level `u`. Let
`F` be a p-adic field and `E` a finite intermediate extension of
`F.Carrier`. Suppose the absolute upper group of `F` at `μ` acts
transitively on the `F`-embeddings of `E`, stated as
`E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤`. Then
for `-1 ≤ x ≤ μ`, the preimage of the absolute upper group `G_F^x` under
`intermediateGaloisMap F E` is the absolute upper group `G_E^x` of
`E.asPadicField`.

The proof applies `herbrandPsiTruncation` (module `Herbrand.KummerTruncationProof`) to the transitivity
hypothesis and both bounds on `x`. This gives `relativeHerbrandPsi E x = x`.
By `Subgroup.ext` and `Subgroup.mem_comap`, it suffices to compare membership
for each element `τ` of the absolute Galois group of `E`. The published
comparison
`HerbrandBridge.intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff`,
which needs only `-1 ≤ x`, says that `intermediateGaloisMap F E τ` lies in
`G_F^x` exactly when `τ` lies in `G_E^{ψ_{E/F}(x)}`, where
`ψ_{E/F} = relativeHerbrandPsi E`. This is Herbrand's theorem for the
subextension. Rewriting the index `ψ_{E/F}(x)` to `x` gives the required
equivalence, including at `x = -1` and `x = μ`. The comparison is stated for
`Field.absoluteGaloisGroup E.field`, and the target uses the absolute Galois
group of `E.asPadicField`. Its carrier is `E.field` by definition, so
`simpa using!` matches the two up to definitional unfolding.

This is `G_E ∩ G_F^x = G_E^x`, the Galois-group form of the step
`W_E ∩ R_K(x) = R_E(x)` in Lemma `lem:trunc` of the operator route note
`operator-numerical-llc-route-2026-11-16`, lines 876–889. The proof has the
same structure as `truncationWeilComap`, which proves the Weil-group version.
The [statement's documentation](TruncationQuotientStatement.md) explains the
formulation over the interval `[-1, μ]`.
