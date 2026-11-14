# A finite Galois splitting field of a torus inside `F^sep / K`

Module: `Langlands.Geometry.Building.Kottwitz.TorusSplittingField`.

## Statement

`Langlands.Geometry.Building.Kottwitz.exists_finiteGalois_splitting` takes the following data.

- A nonarchimedean local field `F`. Write `K := UnramifiedClosure F` (the maximal unramified extension of `F` inside `F^sep := SeparableClosure F`).
- A coefficient field `k`, with the scalar tower `k → K → F^sep` (`IsScalarTower k K F^sep`) and `Normal k K`.
- A commutative group scheme `T` over `Spec k` that is a torus (`IsTorus T.toGrp`).

It concludes that there is an intermediate field `L` of `F^sep / K` such that

- `L / K` is finite (`FiniteDimensional K L`),
- `L / K` is Galois (`IsGalois K L`),
- the base change `T_L` of `T` along `Spec L → Spec k` is a split torus: `IsSplitTorus ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp`. Here `Algebra k L` is the `IntermediateField` instance coming from the tower.

The binders and the splitting conclusion are those of `TorusKottwitzExistenceStatement` (`Langlands/Geometry/Building/Kottwitz/TorusMapStatement.lean`). Its last conjunct quantifies over exactly such fields `L`. The lemma shows that such an `L` exists for every torus in that statement. Kaletha–Prasad, Proposition 11.1.1 (printed p. 421, PDF p. 452), quantifies over "any finite Galois extension L/K splitting T", and its existence proof begins with "Fixing one finite Galois extension L/K splitting T". This lemma supplies such an extension, chosen inside `F^sep`. It is an internal helper: the book uses the existence of a splitting field without stating it as a separate result.

The hypothesis `Normal k K` is not used by the proof. It is kept so that the binders match `TorusKottwitzExistenceStatement` exactly.

## Proof

1. `T_K := baseChanged k K T.toGrp` is a torus by `IsTorus.baseChange` (`Langlands/GroupScheme/Torus/BaseChange.lean`). A torus stays a torus after any field extension.
2. `torusFiniteGaloisSplitting` (`Langlands/GroupScheme/Torus/FiniteGaloisSplittingProof.lean`) gives an abstract finite Galois extension `E / K` over which `T_K` splits.
3. `F^sep` is separably closed and `E / K` is separable, so `IsSepClosed.lift` gives a `K`-embedding `φ : E →ₐ[K] F^sep`. Let `L := φ.fieldRange`. Then `φ.equivFieldRange : E ≃ₐ[K] L` transfers finiteness (`Module.Finite.equiv`) and the Galois property (`IsGalois.of_algEquiv`) to `L`.
4. A splitting isomorphism `(T_K)_E ≅ splitTorus E I` is moved along the `K`-isomorphism `E ≃ L` by `TorusExistence.nonempty_splitIso_extension` (`Langlands/GroupScheme/Torus/ExistenceProof.lean`). So `(T_K)_L` is split.
5. `IsSplitTorus.baseChange_fieldTower_iff k K L` (`Langlands/GroupScheme/Torus/SplittingDescentHelpers.lean`) identifies the iterated base change `(T_K)_L` with the direct base change `T_L` along `Spec L → Spec k`. This gives the conclusion.

Steps 3–4 follow the Library's `Langlands.Geometry.Building.exists_finiteGaloisSplittingField_inside` (`Langlands/Geometry/Building/KPZeroDatumConstruction.lean`). This lemma does not import that module.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
