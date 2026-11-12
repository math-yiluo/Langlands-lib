# Universe transport of the finite tower restriction diagram

`Langlands.LocalClassField.NYLL.finiteAbelianRestrictionUniverseTransport`
proves the published target
`Langlands.LocalClassField.NYLL.FiniteAbelianRestrictionUniverseTransportStatement.{u, v, w}`
from [`UniverseTransportStatement`](UniverseTransportStatement.lean).
Its type is exactly that statement: the host proposition
`FiniteAbelianRestriction.{0, 0, 0}`, through its alias
`FiniteAbelianRestrictionTypeZeroStatement`, implies
`FiniteAbelianRestriction.{u, v, w}` for independent universes. The proof adds
no hypothesis. The statement and host files are unchanged.

## Proof

The proof uses the published model layer
[`UniverseZeroModel`](UniverseZeroModel.lean). Fix a prime `p`, a tower
`F ⊆ E ⊆ L` of p-adic fields in universes `u`, `v` and `w`, its supplied
instances, and arbitrary supplied data `TF`.

1. Install `universeZeroAlgebra` for the three supplied maps. The published
   lemmas give the `Padic p` scalar towers, the model tower
   `F₀ ⊆ E₀ ⊆ L₀`, finite dimensionality of `E₀/F₀` and `L₀/F₀`, and the
   abelian Galois extension `L₀/F₀`.
2. Apply the hypothesis to the models with the canonical data `TF₀`. This gives
   `rE₀` and `rL₀` with the restriction equation `hres₀`.
3. The host statement provides normality of `E/F` through
   `IsAbelianGalois.tower_bot`. The proof derives the same fact for `E₀/F₀`.
4. Let `QE = universeZeroNormQuotientEquiv F E TF₀ TF` and
   `QL = universeZeroNormQuotientEquiv F L TF₀ TF`. Let
   `gE = universeZeroGaloisEquiv F E` and `gL = universeZeroGaloisEquiv F L`.
   The witnesses are `QE.symm.trans (rE₀.trans gE)` and
   `QL.symm.trans (rL₀.trans gL)`.

Both inverse quotient maps send the class of `a : F.Carrierˣ` to the class of
the same model unit
`a₀ = Units.mapEquiv (universeZeroEquiv F).toRingEquiv.symm.toMulEquiv a`.
This is the definitional computation recorded by
`universeZeroNormQuotientEquiv_symm_mk`. By
`universeZeroGaloisEquiv_restrictNormalHom`, the
restriction `AlgEquiv.restrictNormalHom E.Carrier` of `gL (rL₀ [a₀])` equals
`gE` applied to the model restriction of `rL₀ [a₀]`. By `hres₀ a₀`, this is
`gE (rE₀ [a₀])`. The normal-restriction equation therefore holds for every
`a`, with the supplied quotient topologies and the actual Galois groups.

## Provenance

This is an internal transport argument derived from the published model
equivalences and their restriction compatibility. Worker 929 supplied the
shared proof draft and its explanation; Worker 127 checked it against the
published host and model interfaces and prepared this proof unit. No external
implementation is copied.

## Scope

This proof transports the restriction diagram from universe zero. It proves no
Type 0 statement and no uniqueness. It makes no claim about a coherent
common-closure or Weil-group system.
