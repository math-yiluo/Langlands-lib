# All-field port of `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`

`Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` ports to every nonarchimedean local field the one declaration of the p-adic module `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` that the unequal-rank JPSS functional equation needs: the conductor lemma for additive lattices. The p-adic module works over `F : PadicField p` with bundled topological data `T : F.TopologicalData`. Here `F` is an arbitrary field with bundled data `T : LocalFieldData F`: a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure (see `Langlands.LocalFieldData`).

The column lemmas of the original module (`zeroRowColumnEntries`, `zeroRowColumnUnipotent` and their properties) are stated for an arbitrary field, so they are used directly from the original module, which this module imports. The main theorem of the original module, `Langlands.RankinSelberg.zeroRowLastRowCutoff`, is not used by the unequal-rank functional equation and is not ported.

Source: the original p-adic module in the Library. The lemma is an internal step that makes no literature claim. The module serves the proof of the unequal-rank functional equation of Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983).

## Declarations

- `Langlands.LocalFieldData.mem_additiveLattice_of_forall_mul_eq_one` (theorem): suppose `ψ (a * x) = 1` for every `x ∈ T.additiveLattice m`. Then `a ∈ T.additiveLattice (T.additiveConductor ψ - m)`. In the published convention `additiveLattice m = π^(-m) O`, this says: if `x ↦ ψ(a x)` is trivial on `π^(-m) O`, then `a` lies in `π^(m - n(ψ)) O`.

## Proof

The proof is the original one, with the `T`-API taken from `Langlands.LocalFieldData` and the ported lattice lemmas. The hypothesis gives `ψ(t · π^(-m) a) = 1` for every integer `t`, because `π^(-m) t` lies in `T.additiveLattice m` (`mem_additiveLattice_iff_exists_integer`). By `integer_annihilator_iff_mem_additiveLattice`, `π^(-m) a` therefore lies in `T.additiveLattice (T.additiveConductor ψ)`. Since `T.ord (π^(-m)) = -m` (by `ord_zpow` and `ord_uniformizer`), `mul_mem_additiveLattice_iff` moves the level to `T.additiveConductor ψ - m`. The step uses that `π^(-m) ≠ 0`, which follows from `discreteValuation_uniformizer`. No step uses the characteristic of `F`.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeTopology`
