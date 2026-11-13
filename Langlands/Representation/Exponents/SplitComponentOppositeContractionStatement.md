# Uniform two-sided contraction by `A^+(ε)` of compact subsets of `N(F)` and `N̄(F)`

Author: Worker 167.

Module: `Langlands.Representation.Exponents.SplitComponentOppositeContractionStatement`.
Declaration:
`Langlands.Aubert.General.RepresentedParabolic.SplitComponentOppositeContractionStatement.{u}`.
This is a proposition-valued definition. It states a derived formulation of the two
compact-containment clauses of Renard V.5.2 (iii) (for `N` and for `N̄`), on the whole of
`A^+(ε)`, in the form used in the proof of Remarque 3 of VI.9.1. No proof is supplied.

It is the geometric input of the Remark 3 target
`RepresentedParabolic.GeneralizedJacquetContractingRangeStatement` (module
`Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements`) of task
`7a03c792-1d54-4a95-89b7-dd1aa5e82a5e`. It extends the published
`PresentationConeContractionStatement` (the `N` clause on `C_A^+(ε)` only).

## Quantifiers and hypotheses

The field universe `u` is arbitrary. The statement quantifies over `k : Type u` with
`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`;
both characteristics are allowed. For every group scheme `G` over `Spec k` and
`hG : IsConnectedReductive G`, it installs `hG.isAffineHom` and the topology
`RationalPointFamily.pointTopology` on `rationalPoints G`, then quantifies over instances
`[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`,
exactly as in `GeneralizedJacquetContractingRangeStatement`.

The parabolic data are word for word those of `GeneralizedJacquetContractingRangeStatement`:

- group schemes `P`, `Pbar`, `M`, `N`, `Nbar` over `Spec k`;
- maps `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P` with `IsParabolicSubgroup p`,
  `IsRationalLeviSubgroup m`, `LeviSubgroup.IsGeometricUnipotentRadical n` and
  `IsIso (subgroupMultiplication m n)` (so `P = MN`);
- maps `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with the same four
  predicates (so `P̄ = M N̄`);
- the equation `mbar ≫ pbar = m ≫ p` (the same Levi `M` in `G`) and
  `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)` (`P(F) ∩ P̄(F) = M(F)`), which
  make `P̄` the parabolic opposite to `P` with respect to `M`.

Unlike the Remark 3 target, there is no compact open subgroup `K` and no element `t₀`.

Next come a commutative group scheme `A` over `Spec k`, a map `a : A.toGrp ⟶ M` and
`pres : ParabolicRootPresentation p m a` (which includes `IsSplitComponent a`), and the
character set

```text
Δ = (fun α => pres.data.f ≫ α) ''
      (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J),
```

the restrictions to `A` of the simple roots outside `J`, i.e. `Δ(P)`, with the same encoding
as in `PresentationConeContractionStatement` and the Remark 3 target. Points of `A` act on
`G(F)` through `incG := rationalPoints.map (a ≫ m ≫ p)`.

## Conclusion

For every `C : Set (rationalPoints G)` with `IsCompact C` and `C ⊆ pointImage (n ≫ p)`,
every `Cbar : Set (rationalPoints G)` with `IsCompact Cbar` and
`Cbar ⊆ pointImage (nbar ≫ pbar)`, and every `L ∈ nhds (1 : rationalPoints G)`, there is a
real `ε > 0` such that for every `t : rationalPoints A.toGrp` with
`CocharacterUniformizer.characterNorm k A α t < ε` for all `α ∈ Δ`,

```text
incG t * c * (incG t)⁻¹ ∈ L    for every c ∈ C,
(incG t)⁻¹ * c * incG t ∈ L    for every c ∈ Cbar.
```

`ε` may depend on all the data, on `C`, `Cbar` and `L`, but works simultaneously for all
such `t` and all `c`. The condition on `t` is exactly the one of the Remark 3 target: it
describes `A^+(ε) = {t ∈ A(F) | |α(t)|_F < ε for α ∈ Δ(P)}`, the whole set and not only
its intersection `C_A^+(ε)` with the lattice image `C_A`. There is no norm-at-most-one
condition. Empty `Δ` (`P = G`) is not excluded; then `N(F)` and `N̄(F)` are trivial and the
conclusion holds with any `ε`.

## Source and derived provenance

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- V.5.2, Théorème (iii), printed p.123 / PDF p.129: for every compact subset `Γ` of `N`
  (resp. `Γ` of `N̄`) there is `ε > 0` such that `Γ ⊂ m⁻¹ K_N m` (resp.
  `Γ ⊂ m K_N̄ m⁻¹`) for every `m ∈ C_A^+(ε)`, where `K` runs over a neighbourhood basis of
  compact open subgroups with Iwahori decompositions and `K_N = K ∩ N`, `K_N̄ = K ∩ N̄`.
- VI.9.1, proof of Remarque 3, printed p.198 / PDF p.204: "on sait (théorème V.5.2)
  qu'il existe `ε > 0` tel que, `C` et `C̄` étant comme ci-dessus, pour tout
  `t ∈ A^+(ε)`, `C ⊂ t⁻¹ K_N t`, `C̄ ⊂ t K_N̄ t⁻¹`."
- V.3.22–V.3.23, printed p.117 / PDF p.123, define
  `A^+(ε) = {a ∈ A_M | |α(a)|_F < ε for α ∈ Δ(P)}` and `C_A^+(ε) = C_A ∩ A^+(ε)`.

The provenance is **derived**:

- Neighbourhood form. `Γ ⊂ t⁻¹ K_N t` is `t Γ t⁻¹ ⊆ K_N`, and `Γ ⊂ t K_N̄ t⁻¹` is
  `t⁻¹ Γ t ⊆ K_N̄`. Given a neighbourhood `L` of `1`, choose `K ⊆ L` in the source's basis;
  conversely, apply the present statement with `L = K` and use that `A` normalizes `N`
  and `N̄`. This is the same reformulation as in `PresentationConeContractionStatement`.
- Range of `t`. Theorem V.5.2 is stated for `m ∈ C_A^+(ε)`; the proof of Remarque 3
  applies it to all `t ∈ A^+(ε)`, and the statement follows that use. The two forms are
  equivalent: every `t ∈ A(F)` is `t = c u` with `c ∈ C_A` and `u` in the compact subgroup
  `A(F)⁰` on which all `|α|_F` equal `1`, so `t ∈ A^+(ε)` iff `c ∈ C_A^+(ε)`, and
  conjugation by `u` maps compact subsets of `N` (resp. `N̄`) to compact subsets.
- Opposite parabolic. `P̄` is given by actual maps with the hypotheses above rather than
  as a standard parabolic of a fixed family; the presentation `pres` of `P` organizes the
  source's standard coordinates around the specified maps, as in
  `PresentationConeContractionStatement`.

The comparison of the presentation's conventions with the source, the identification of
the supplied radicals, the decomposition `A(F) = C_A · A(F)⁰` and the uniform contraction
argument remain obligations for a proof.
