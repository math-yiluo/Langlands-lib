# Transport of obstruction-cone data along a quasi-isomorphism

Module `Langlands.Cohomology.ModuleComplex.ObstructionCone.Transfer`, namespace of the same
name. This is an internal helper for
`Langlands.Cohomology.ModuleComplex.ObstructionCone.openStatement`. It uses the definition
`ObstructionCone.HOneVanishes` from `ObstructionConeOpenStatement`.

## Definitions and basic lemmas

- `rTensor_lTensor`: `f.rTensor N' (g.lTensor X t) = g.lTensor Y (f.rTensor N t)`.
- `CohIso K C dK d φ N` is a proposition about complexes `(K, dK)`, `(C, d)` and maps
  `φ i : K i → C i`. It says that for every `i`, `φ (i+1) ⊗ N` is injective and surjective
  on cohomology in degree `i + 1`, in the same elementwise form as `QuasiIsoModule.rTensor_quasiIso`.
- `rTensor_chain`: a chain map stays a chain map after `- ⊗ N`.

## Results

`exists_transfer`. Assume `CohIso … Q` and `CohIso … F`, `δ : Q → F`, `θ ∈ C 1 ⊗ F` and
`z ∈ C 2 ⊗ Q` with `d θ = δ_* z` and `d z = 0`. Then there are
`zh ∈ K 2 ⊗ Q`, `w ∈ C 1 ⊗ Q`, `θh ∈ K 1 ⊗ F` and `v ∈ C 0 ⊗ F` with
- `dK zh = 0`;
- `φ zh = z + d w`;
- `dK θh = δ_* zh`;
- `φ θh = θ + δ_* w + d v`.

Here `δ_*` is `δ.lTensor`, and `dK`, `d`, `φ` act on the left tensor factor. Proof:
1. Surjectivity in degree 2 for `Q` gives `zh` and `w`.
2. `δ_* zh` is a cycle whose image `d (θ + δ_* w)` is a boundary, so injectivity in degree 2
   for `F` writes it as `dK θ₀`.
3. `φ θ₀ − θ − δ_* w` is a cycle, so surjectivity in degree 1 for `F` corrects `θ₀` by a
   cycle `t`. Then `θh = θ₀ − t`.

`hOneVanishes_of_model`. With these relations and `CohIso … M`,
`HOneVanishes K dK δ θh zh M` implies `HOneVanishes C d δ θ z M`. Given `c` and `ψ` with
`d c + ψ_* z = 0`:
1. Injectivity in degree 2 for `M` writes `ψ_* zh` as a boundary `dK c₀`.
2. Surjectivity in degree 1 adjusts `−c₀` by a cycle `t` so that `φ (−c₀ − t)` equals
   `c − ψ_* w` up to a boundary `d e'`.
3. The vanishing over `K` gives `bh` and `D` with `−c₀ − t = dK bh + D_* θh` and
   `ψ + D ∘ δ = 0`.
4. Applying `φ` and the relations gives `c = d (φ bh + D_* v + e') + D_* θ`.

`hOneVanishes_model`. Conversely, with `CohIso … M`, `HOneVanishes C d δ θ z M` implies
`HOneVanishes K dK δ θh zh M`. Given `ch` and `ψ` with `dK ch + ψ_* zh = 0`:
1. The element `φ ch + ψ_* w` satisfies the hypothesis over `C`.
2. The resulting `b`, `D` show that `ch − D_* θh` is a cycle whose image is the boundary
   `d (b − D_* v)`.
3. Injectivity in degree 1 writes `ch − D_* θh` as `dK bh`.

## Provenance

Internal diagram chases. In the language of the Stacks Project, Artin's Axioms, Section
98.23, they show that the first cohomology of the obstruction cone does not depend on the
choice of a quasi-isomorphic model of the coefficient complex. The proof is the elementwise
chase above.
