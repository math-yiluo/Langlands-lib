# Proof of transfer and idele-class norm compatibility

Proof for task `d02b213c-6237-44c1-a667-4a8c19662bfe`, revision 1. The theorem
`Langlands.ClassField.Global.RelativeWeilGroup.transferNormCompatibilityStatement.{u}` proves
exactly the published statement
`Langlands.ClassField.Global.RelativeWeilGroup.TransferNormCompatibilityStatement.{u}`
from `RelativeWeilTransferNormStatement`. It adds no hypothesis.

Let `c` be any class family, let `h : FundamentalClass.Restriction c`, and let
`F ⊆ K ⊆ E` be number fields in universe `u` with `IsScalarTower F K E` and `E / F` Galois.
The extension `K / F` need not be Galois. For every `t ∈ W_{E/K}`,

```text
transfer c F E (restrictionInclusion c F E K h t)
  = ideleClassNorm (K := F) (L := K) (transfer c K E t).
```

## Declarations

- `RelativeWeilGroup.transferNormCompatibility c F K E h` (theorem): the identity above,
  that is `TransferNormCompatibility c F K E h`.
- `RelativeWeilGroup.transferNormCompatibilityStatement` (theorem): the target. It applies
  `transferNormCompatibility` to every class family, every tower and every `h`.

The proof uses two helper modules:

- `Langlands.GroupTheory.TransferRestriction`, with
  `Langlands.GroupTheory.Transfer.transfer_apply_eq_prod` (restriction of the transfer along
  a homomorphism) and `conjComap`;
- `Langlands.ClassField.Global.IdeleClassNormEmbeddingProduct`, with
  `ideleClassInclusion_ideleClassNorm_eq_prod` (the idele-class norm as a product over
  automorphisms that restrict to the embeddings `K → E`).

Their own Markdown files describe them.

## What is used

The proof uses the published relative Weil group API: `restrictionInclusion`,
`restrictionInclusion_inclusion`, `restrictionInclusion_injective`,
`range_restrictionInclusion`, `projection_surjective` and `conjugation`. It also uses the
published transfer API in `RelativeWeilTransfer`: `ideleClassSubgroup`,
`ideleClassSubgroupEquiv`, `ideleClassSubgroupEquiv_inclusion`, `ideleTransfer_apply`,
`transfer_comp`, `ideleClassInclusion_transfer` and
`eq_transfer_of_ideleClassInclusion_eq`. It does not use transfer reciprocity, any global
functional equation or any local Langlands result. It needs no arithmetic hypothesis on
`c`.

## Implemented proof

Write `W_F = W_{E/F}`, `W_K = W_{E/K}`, `C_E ⊆ W_F` for `ideleClassSubgroup c F E`, and
`C_E ⊆ W_K` for `ideleClassSubgroup c K E`.

1. *The inclusion.* Let `ι : W_K →* W_F` be `restrictionInclusion c F E K h`. It sends
   `inclusion c K E a` to `inclusion c F E a` (`restrictionInclusion_inclusion`). Hence:
   - `x ∈ C_E ⊆ W_K` if and only if `ι x ∈ C_E ⊆ W_F`. The reverse direction uses
     injectivity of `ι` (`restrictionInclusion_injective`).
   - `C_E ⊆ W_F` lies in the range of `ι`, so the range has finite index.

   These are the hypotheses of `transfer_apply_eq_prod` for `A = C_E ⊆ W_F` and
   `A' = C_E ⊆ W_K`.
2. *Conjugation is the Galois action.* Let `ψ_F` and `ψ_K` be the identifications
   `ideleClassSubgroupEquiv` of the idele-class subgroups with `C_E`. For a coset
   `q ∈ W_F ⧸ ι.range`, put `s q = projection c F E q.out ∈ Gal(E/F)`. Then

   ```text
   ψ_F ∘ conjComap ι _ q.out = relativeIdeleClassAut F E (s q) ∘ ψ_K.
   ```

   On `inclusion c K E a`, this is the published `conjugation`
   (`w * inclusion a * w⁻¹ = inclusion (σ_w a)`) together with
   `ideleClassSubgroupEquiv_inclusion`.
3. *The automorphisms `s q` restrict to the embeddings `K → E`, each once.* By
   `range_restrictionInclusion`, `g ∈ ι.range` holds if and only if `projection c F E g`
   fixes `K` pointwise. An `F`-automorphism of `E` that fixes `K` is the restriction of
   scalars of a `K`-automorphism (`AlgEquiv.ofRingEquiv`). It follows that the map
   `q ↦ (s q)|_K` from `W_F ⧸ ι.range` to `K →ₐ[F] E` is bijective.
   - Injectivity. If `s q₁` and `s q₂` agree on `K`, then
     `projection (q₁.out⁻¹ * q₂.out)` fixes `K`, so `q₁ = q₂`.
   - Surjectivity. Extend an embedding `τ : K → E` to the automorphism `τ.liftNormal E`
     of `E` (bijective because `E / F` is normal), and lift it to `g ∈ W_F`
     (`projection_surjective`). Then `g⁻¹ * (q.out)` lies in the range for `q = [g]`, so
     `s q` agrees with `τ` on `K`.
4. *Assembly.* By `eq_transfer_of_ideleClassInclusion_eq`, it suffices to prove the
   identity after the injective inclusion `C_F → C_E`, against `ideleTransfer c F E (ι t)`.
   - The left side is `ideleClassInclusion (ideleClassNorm (transfer c K E t))`. By
     `ideleClassInclusion_ideleClassNorm_eq_prod` with the family `s` from step 3, it is
     `∏ q, σ_{s q} (ideleClassInclusion (transfer c K E t))`.
   - The right side is `MonoidHom.transfer ψ_F (ι t)` (`ideleTransfer_apply`). By
     `transfer_apply_eq_prod` it is `∏ q, transfer (ψ_F ∘ conjComap ι _ q.out) t`. By step 2
     and `transfer_comp` (post-composition with a homomorphism of abelian groups), each
     factor is `σ_{s q} (transfer ψ_K t) = σ_{s q} (ideleTransfer c K E t)`. Finally
     `ideleClassInclusion_transfer` rewrites `ideleTransfer c K E t` as
     `ideleClassInclusion (transfer c K E t)`.

   The two products agree factor by factor.

## Relation to the source

Tate (1979), *Number theoretic background*, (1.2.2) and the remark after it, p.4, derives
the norm compatibility from the coset computation for the transfer when the subgroup is
normal. Here the image of `W_{E/K}` is normal only when `K / F` is Galois. The proof
therefore computes the transfer to the idele-class subgroup `C_E`, which is normal in both
groups. The quotient `W_F ⧸ ι.range` plays the role of the `F`-embeddings of `K` into `E`.
