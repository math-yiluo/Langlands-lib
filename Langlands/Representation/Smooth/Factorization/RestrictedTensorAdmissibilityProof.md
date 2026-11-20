# Admissibility of restricted tensor representations

Authors: Worker 3657 (shared draft for Task 7602), Worker 1000 (adaptation
to the published `Irreducibility` module).

Lean module:
`Langlands.Representation.Smooth.Factorization.RestrictedTensorAdmissibilityProof`.
It imports only published modules:
`Langlands.Representation.Smooth.Factorization.RestrictedTensorStatement`,
`Langlands.Representation.RestrictedTensor.Irreducibility`,
`Langlands.Representation.Tensor.FiniteProperties` and
`Langlands.Representation.RestrictedTensor.LocalSeparation`. It changes no
published file and adds no other module.

## Main theorem

```lean
theorem Langlands.restrictedTensorAdmissibility :
    RestrictedTensorAdmissibilityStatement.{uI, uG, uV}
```

This is exactly the published statement, with its three universes: for
Hausdorff, locally compact, totally disconnected local groups `G i` with open
compact subgroups `H i`, admissible local representations `ρ i`, nonzero
reference vectors `r` fixed by `H i` outside a finite set `E`, and
`finrank (fixedVectors (ρ i) (H i)) = 1` for almost every `i`, the restricted
tensor representation `productRepresentation H ρ E r hr` of the restricted
product is admissible.

## Declarations

In namespace `Langlands.RestrictedTensor`:

- `exists_finset_forall_mem H K`: an open subgroup `K` of `RestrictedGroup G H`
  contains every element `g` with all `g i ∈ H i` and `g i = 1` on some finite
  set `T`. Proof: the preimage of `K` under Mathlib's continuous
  `RestrictedProduct.structureMap` from `∏ H i` is an open neighbourhood of
  `1`, hence contains a basic box (`isOpen_pi_iff`) with finite support `T`.
- `inv_localInsertion_mul_apply`: the coordinates of
  `(localInsertion H w (g w))⁻¹ * g` are `1` at `w` and `g i` elsewhere.
- `mem_of_localInsertion_mem`: with `T` as above, `K` contains every `g` with
  all `g i ∈ H i` and `localInsertion H i (g i) ∈ K` for `i ∈ T`. Proof by
  induction over finite sets, splitting off one local factor at a time.
- `localOpenSubgroup H hH K i`: the open subgroup
  `{x ∈ H i | localInsertion H i x ∈ K}` of `G i`. Openness: it is the image
  in `G i` of the preimage of `K` under the continuous map
  `x ↦ structureMap (Pi.mulSingle i x)` on `H i`, and `H i` is open.
- `fixedVectors_le_range`: for subgroups `L i` and a finite stage `S0` such that
  outside `S0` every `L i`-fixed vector is a multiple of the reference vector,
  every vector of the restricted tensor product fixed by all `g` with
  `g i ∈ L i` lies in the image of `⊗_{i ∈ S0} fixedVectors (ρ i) (L i)` in the
  stage `S0`. Proof: write the vector as `of S t` with `S ⊇ S0`; `t` is fixed
  by `∏_{i ∈ S} L i` (through the Library's `stageGroupElement` and
  `of_external` from `RestrictedTensor/Irreducibility.lean`, which make an
  element of `∏_{i ∈ S} G i`, extended by `1` outside `S`, act on the stage by
  the external tensor product, and `of_injective`), so by the Library's
  `FiniteTensor.fixedVectors_external_le` it is a tensor of `L i`-fixed
  vectors; on pure tensors, the coordinates outside `S0` are multiples of the
  references, so `MultilinearMap.map_smul_univ` and the Library's
  `pure_extend` move the tensor to the stage `S0`.

In namespace `Langlands`, `restrictedTensorAdmissibility`: smoothness is the
Library's `isSmooth_productRepresentation`. For an open subgroup `K`, take `T`
from `exists_finset_forall_mem`, `L i := localOpenSubgroup H hH K i` for
`i ∈ T` and `L i := H i` otherwise; then every `g` with `g i ∈ L i` lies in `K`
(`mem_of_localInsertion_mem`). Let `S0` be `E ∪ T` together with the finitely
many indices where the `H i`-fixed space is not a line; outside `S0` the
`L i`-fixed vectors are multiples of the reference vector
(`finrank_eq_one_iff_of_nonzero'`). By `fixedVectors_le_range` the `K`-fixed
vectors lie in the image of `⊗_{i ∈ S0} fixedVectors (ρ i) (L i)`, which is
finite-dimensional because each `ρ i` is admissible; so the `K`-fixed space
is finite-dimensional (`Submodule.finiteDimensional_of_le`). Compactness of
`H i` is not used.

## Provenance

D. Flath, *Decomposition of representations into tensor products*, in
*Automorphic Forms, Representations and L-functions*, Proc. Sympos. Pure Math.
33, Part 1 (1979), registered as `flath-1979-tensor-products` (SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`), section 2,
Example 2, printed p.181 (PDF page 177 of the registered file). Example 2 forms
the tensor product `W = ⊗ W_v` of admissible `G_v`-modules with
`dim W_v^{K_v} = 1` for almost all `v`, using nonzero vectors
`x_v ∈ W_v^{K_v}`, and states "One sees that W is admissible"; Flath gives no
proof. The argument here (reduction of an open subgroup to a product of local
open subgroups trivial-up-to-`H i` outside a finite set, and of its fixed
vectors to a finite stage) is the standard one and is internal to this module.

## Lean checks

Lake-build `lean_check` 68a06039-f337-4205-b2fc-f3bbdb5a82e7 (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Library base
`24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85`): no errors or warnings;
`restrictedTensorAdmissibility` has universe parameters `uI`, `uG`, `uV` and
uses only `propext`, `Classical.choice` and `Quot.sound`. A separate check
elaborates `example : RestrictedTensorAdmissibilityStatement.{uI, uG, uV} :=
restrictedTensorAdmissibility.{uI, uG, uV}`.

## History

Worker 3657's shared draft for Task 7602 (draft revision 1) used a helper
module `Langlands.Representation.RestrictedTensor.StageAction` declaring
`stageInclusion` and `Langlands.RestrictedTensor.of_external`. The Library
module `Langlands.Representation.RestrictedTensor.Irreducibility` already
declares `Langlands.RestrictedTensor.of_external` (with `stageGroupElement`),
so the helper was dropped to avoid a duplicate declaration name, and the proof
uses the published declarations; the rest of the proof is unchanged.
