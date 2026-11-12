# Universe transport of the finite norm and transfer diagrams

`Langlands.LocalClassField.NYLL.finiteAbelianNormTransferUniverseTransport`
proves the published target
`Langlands.LocalClassField.NYLL.FiniteAbelianNormTransferUniverseTransportStatement.{u, v, w}`
from [`UniverseTransportStatement`](UniverseTransportStatement.lean).
Its type is exactly that statement: the host proposition
`FiniteAbelianNormTransfer.{0, 0, 0}`, through its alias
`FiniteAbelianNormTransferTypeZeroStatement`, implies
`FiniteAbelianNormTransfer.{u, v, w}` for independent universes. The proof adds
no hypothesis. The statement and host files are unchanged.

## Model data

The proof uses the published model layer
[`UniverseZeroModel`](UniverseZeroModel.lean). Fix a prime `p`, a tower
`F ⊆ E ⊆ L` with `F : PadicField.{u} p`, `E : PadicField.{v} p` and
`L : PadicField.{w} p`, its supplied instances, and arbitrary supplied data `TF`
and `TE`.

1. Install `universeZeroAlgebra` for the three supplied maps `F → E`, `F → L`
   and `E → L`. The published lemmas then give the following on the models
   `F₀`, `E₀` and `L₀`:
   - the three `Padic p` scalar towers;
   - the tower `F₀ ⊆ E₀ ⊆ L₀` (`universeZeroAlgebra_isScalarTower_tower`);
   - the three finite-dimension facts;
   - the abelian Galois extension `L₀/F₀`.
2. Apply the hypothesis to the models with the canonical data `TF₀` and `TE₀`.
   This gives `rF₀` and `rE₀`, with the norm clause `hnorm` and the transfer
   clause `htr`.
3. Let `QF = universeZeroNormQuotientEquiv F L TF₀ TF` and
   `QE = universeZeroNormQuotientEquiv E L TE₀ TE`. They identify the model norm
   quotients with the actual host quotients and their supplied topologies. Let
   `GF = universeZeroGaloisEquiv F L` and `GE = universeZeroGaloisEquiv E L`.
   They identify the actual Galois groups.
4. The witnesses are `QF.symm.trans (rF₀.trans GF)` and
   `QE.symm.trans (rE₀.trans GE)`.

The key Galois fact is `universeZeroGaloisEquiv_restrictScalars`:
`GF (τ.restrictScalars F₀) = (GE τ).restrictScalars F.Carrier`.

## Norm clause

Let `a : E.Carrierˣ` and let `a₀` be its model unit. By
`universeZeroEquiv_norm` and `universeZeroNormQuotientEquiv_symm_mk`, the class
of `Units.map (Algebra.norm F.Carrier) a` is sent by `QF.symm` to the class of
the model norm of `a₀`. Then `hnorm a₀` and the key Galois fact identify the
host value with `(rE [a]).restrictScalars F.Carrier`, because `QE.symm [a]` is
`[a₀]`. The field norm thus still corresponds to Galois inclusion.

## Transfer clause

Let `a : F.Carrierˣ` and let `a₀` be its model unit. By
`universeZeroEquiv_symm_algebraMap`, the class of the scalar inclusion
`Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a` is sent by
`QE.symm` to the class of the model scalar inclusion of `a₀`. Then:

- the key Galois fact, read backwards, rewrites the restriction of scalars;
- `htr a₀` gives the degree power;
- `map_pow` moves the power through `GF`;
- `universeZeroAlgebra_finrank` replaces the model degree by
  `Module.finrank F.Carrier E.Carrier`.

The result is `rF [a] ^ Module.finrank F.Carrier E.Carrier`. The scalar
inclusion keeps its direction, distinct from the norm.

## Scope

This proof transports the two diagrams from universe zero. It proves no Type 0
statement and no uniqueness. It makes no comparison with the cohomological
transfer and no claim about a Weil-group or common-closure system.

## Provenance

This is an internal transport-of-structure proof of the published implication.
It reuses Worker 929's shared draft, revision 1 for Task 5273, with verification
and submission by Worker 126. Its mathematical inputs are the published host
statement and model-layer lemmas described above; it copies no external NYLL
implementation and attributes no additional theorem to the literature.
