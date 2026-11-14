# Independence of the torus norm square from the splitting field

Module: `Langlands.Geometry.Building.Kottwitz.TorusKottwitzTransfer`. It imports `TorusKottwitzLaw` and `Langlands.GroupScheme.Torus.SplittingDescentHelpers`.

This module proves the splitting-field independence step in Kaletha–Prasad, Proposition 11.1.1 (printed p. 421, PDF p. 452). The proof there says: "if we have a map κ_T that makes the above diagram commutative for one particular Galois extension L/K splitting T, then it also makes it commutative for any other Galois extensions L/K splitting T. This follows from the fact that if L1/K and L2/K are two such extensions and L1 ⊂ L2, then the diagram [T(L2) → X_*(T) over T(L1) → X_*(T)] commutes, due to the fact that L2/L1 is totally ramified."

## Setting

- `F` is a nonarchimedean local field. `K = UnramifiedClosure F` and `F^sep = SeparableClosure F`.
- `k` is a coefficient field with the tower `k → K → F^sep` and `Normal k K`.
- `T` is a commutative group scheme over `Spec k` with affine total space.
- For a finite intermediate field `L` of `F^sep / K` over which `T` splits, `normLawValue F k T L hL : Additive T(L) →+ X_*(T)_I` (from `TorusKottwitzLaw`) is the right-hand side of the norm square. Take the split valuation of a point with respect to `normalizedIntermediateValuation F L`, extend cocharacters from `L` to `F^sep`, and project to inertia coinvariants.

## Statements

`orderUnits_norm`. Let `L`, `M` be finite intermediate fields of `F^sep / K` with an algebra `L → M`, and assume the normalized valuations satisfy `v_L(N_{M/L} x) = v_M(x)` for all `x ∈ M`. Then for every unit `w ∈ M^×`, the integer order of `N_{M/L}(w)` for `v_L` equals the integer order of `w` for `v_M`. This is a direct consequence of `IntegerValuation.orderUnits_toAdd`.

`normLawValue_relativeNorm_tmul`. This is the case of the next statement on a pure cocharacter evaluation `w ⊗ ν'`, with `w ∈ M^×` and `ν'` a cocharacter of `T_M`.

`normLawValue_relativeNorm` (the diagram in the quoted proof). Assume:
- `L`, `M` are finite intermediate fields of `F^sep / K`;
- there is an algebra `L → M` with towers `k → L → M` and `L → M → F^sep`;
- `M / L` is finite Galois;
- `T` splits over `L` (`hL`) and over `M` (`hM`);
- `hv`: `v_L(N_{M/L} x) = v_M(x)` for all `x ∈ M`.

Then for every `x ∈ T(M)`,
`normLawValue … L hL (N_{M/L} x) = normLawValue … M hM x`,
where `N_{M/L} = relativeNorm k L M T` is the norm `T(M) → T(L)`.

In KP the commutativity comes from "L2/L1 is totally ramified". In the Lean statement this input is the hypothesis `hv`, which `normalizedIntermediateValuation_norm` (module `TorusNormValuation`) supplies when `L ≤ M` with the inclusion algebra. Because the residue field of `K` is algebraically closed, every finite `M / L` here is totally ramified, so `v_L ∘ N_{M/L} = v_M`.

`torusNormLawAt_of_torusNormLawAt` (independence of the splitting field). Let `L₀` and `L` be finite Galois intermediate fields of `F^sep / K` over which `T` splits. Let `κ : T(K) →* X_*(T)_I` be a homomorphism that satisfies the norm square `TorusNormLawAt F k T L₀ hL₀ κ`. Then `κ` also satisfies `TorusNormLawAt F k T L hL κ`. Unlike the quoted argument, the statement does not require `L₀ ⊆ L`: the proof passes through the compositum.

## Proofs

`normLawValue_relativeNorm_tmul`.
1. Splitting over `L` makes `extendGeometricCocharacters k L M T` bijective (`extendGeometricCocharacters_bijective`). So write `ν' = ext_{L→M} ν`.
2. Choose a unit `u₀ ∈ L^×` of infinite order (`exists_not_isOfFinOrder`). `T` splits over `F^sep` by `IsSplitTorus.baseChange_fieldTower`.
3. `relativeNorm_coefficientEvaluation_tmul` gives `N_{M/L}(w ⊗ ext_{L→M} ν) = N_{M/L}(w) ⊗ ν`.
4. `normLawValue_tmul` on both sides reduces the claim to
   `π(ext_{L→F^sep}(ord_L(N w) • ν)) = π(ext_{M→F^sep}(ord_M(w) • ext_{L→M} ν))`.
5. This follows from `orderUnits_norm` (equal orders), additivity (`map_zsmul`), and transitivity `ext_{M→F^sep} ∘ ext_{L→M} = ext_{L→F^sep}` (`extendGeometricCocharacters_extend`).

Steps 4–5 are written as `Eq.trans`/`congrArg` terms. A `rw` on goals of this size times out in the motive check.

`normLawValue_relativeNorm`. Both sides are additive maps on `Additive T(M)`. Since `T` splits over `M`, `additive_ext_coefficientEvaluation` reduces their equality to pure evaluations `w ⊗ ν'`, which is the previous lemma.

`torusNormLawAt_of_torusNormLawAt`.
1. Let `M = L ⊔ L₀`. It is finite Galois over `K` (Mathlib instances `IntermediateField.finiteDimensional_sup` and the `IsGalois` instance for sups in `Mathlib.FieldTheory.Galois.GaloisClosure`).
2. For `L₀ ⊆ M` and `L ⊆ M`, define the algebra by `IntermediateField.inclusion`. The towers hold definitionally. `M` is finite over each (`FiniteDimensional.right`) and Galois over each (`IsGalois.tower_top_of_isGalois`).
3. `T` splits over `M` by base change from `L₀` (`IsSplitTorus.baseChange_fieldTower_iff`). The hypotheses `hv` for `L₀ ⊆ M` and `L ⊆ M` come from `normalizedIntermediateValuation_norm`.
4. Norm square at `M`: for `x ∈ T(M)`,
   - `κ(N_{M/K} x) = κ(N_{L₀/K}(N_{M/L₀} x))` by `relativeNorm_relativeNorm`;
   - this equals `normLawValue … L₀ (N_{M/L₀} x)` by the law at `L₀` (`torusNormLawAt_iff`);
   - this equals `normLawValue … M x` by `normLawValue_relativeNorm`.
5. Descent to `L`. `L` has dimension at most one (`HasDimensionLEOne`), by `unramifiedClosure_hasDimensionLEOne` and `HasDimensionLEOne.finite_separable_extension`. So `N_{M/L} : T(M) → T(L)` is surjective (`relativeNorm_surjective`, module `TorusNormCohomology`). Write `y = N_{M/L} x`. Then
   - `κ(N_{L/K} y) = κ(N_{M/K} x)` by `relativeNorm_relativeNorm`;
   - this equals `normLawValue … M x` by step 4;
   - this equals `normLawValue … L y` by `normLawValue_relativeNorm`.
   This is the norm square at `L` (`torusNormLawAt_iff`).

## Implementation notes

The file sets `attribute [local instance high] Algebra.toModule Algebra.toSMul`. Without it, elaborating binders such as `[FiniteDimensional L M]` and `[IsScalarTower L M F^sep]` for intermediate fields `L`, `M` with a given `[Algebra L M]` times out in instance search. The attribute only changes the search order inside this file. The instances found are the ones coming from the given algebra.

All theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
