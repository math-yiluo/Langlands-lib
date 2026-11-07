# The compression range as an averaged fixed space

This is a derived supporting result for the proof of Renard VI.9.7. The source
is David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.9.1, Remark 2 and its proof, printed
pp.197–198 / PDF pp.203–204. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The completion application is VI.9.7, printed pp.205–206 / PDF pp.211–212.

Let `G` be a topological group, `ρ` a smooth complex representation on an
arbitrary complex module `V`, and `K` a compact open subgroup. Assume
`Jacquet.IsIwahoriContraction K N M Nbar g` and that `g` commutes with every
element of `M`. Write `A = compressedAction ρ hρ K hK g`, an endomorphism of
`V^K`, and `e_K = Compact.averageMap ρ hρ K hK`. The carrier universes of
`G` and `V` are independent. No finite-dimensionality or admissibility
hypothesis is imposed.

`expandedLowerSubgroup K Nbar g b` is the actual subgroup
`C_b = g^b (K ∩ Nbar) g^-b`, defined as the image of `K ∩ Nbar` under
conjugation. If `Nbar` is closed, `C_b` is compact: `K ∩ Nbar` is a closed
subset of compact `K`, and conjugation is continuous. If `g` normalizes
`Nbar`, then `C_b ≤ Nbar`. These are proved separately, and neither is
needed for the range identity itself.

`compressionRange_eq_average_expandedLower_fixed` proves, for every
nonnegative integer `b`,

`(range A^b).map (V^K).subtype = e_K(V^{C_b})`.

Both sides are submodules of the original module `V`. The left side is
the range of `A^b` included from `V^K` into `V`, not the range of a new
endomorphism of `V`.

The first inclusion uses the published identity
`compressedAction (g^b) = A^b`: if `w ∈ V^K`, then `ρ(g^b)w` is fixed by
`C_b`, and `A^b w = e_K ρ(g^b)w`. For the reverse inclusion, start with
`v ∈ V^{C_b}` and put `w = e_K ρ(g^-b)v ∈ V^K`. The proof shows
`A^b w = e_K v`. To do so, factor the inverse of each `k ∈ K` as
`l m u`, so that `k = u^-1 m^-1 l^-1`. The factor `l^-1` fixes
`ρ(g^-b)v` by the `C_b`-fixedness of `v`. Conjugation by `g^b` carries
`u^-1` into `K` by the upper contraction law and carries `m^-1` into
`K` because `g` commutes with `M`. Thus `e_K ρ(g^b)` is constant on the
`K`-orbit of `ρ(g^-b)v`. The finite-orbit averaging lemma gives the
claimed equality. Translation invariance of the compact orbit mean
removes the two factors already in `K`.

`stableImage_eq_average_expandedLower_fixed` substitutes an explicit
stationary-range equality `stableImage = range A^b` into the range identity.
`exists_compact_average_fixed_le_stableImage` additionally assumes that
`Nbar` is closed and that `g` normalizes it, and produces a compact subgroup
`C ≤ Nbar` with `e_K(V^C)` contained in the ambient stable image. This is
the averaged-image input of `CompactCompletion.componentsIn_eq_completionFixed`.

The statements retain stationarity as a premise; they do not prove
Renard's uniform stabilization theorem or the actual represented-parabolic
completion theorem. The compact subgroup is the specific `C_b`. The unit
does not claim equality for every sufficiently large compact subgroup,
cofinal fixedness of stable-image components, or cofinality of Iwahori
subgroups. Those are separate application obligations.
